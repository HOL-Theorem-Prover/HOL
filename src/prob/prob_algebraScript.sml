open HolKernel Parse boolLib bossLib arithmeticTheory realTheory
     seqTheory pred_setTheory ind_typeTheory listTheory
     rich_listTheory pairTheory combinTheory realLib probTools
     boolean_sequenceTheory boolean_sequenceTools prob_extraTheory
     prob_extraTools prob_canonTheory prob_canonTools numSyntax;

val _ = new_theory "prob_algebra";

infixr 0 ++ << || ORELSEC ## -->;
infix 1 >> |->;
nonfix THEN ORELSE;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);

(* ------------------------------------------------------------------------- *)
(* Definition of the embedding function from boolean list lists to boolean   *)
(* sequences.                                                                *)
(* ------------------------------------------------------------------------- *)

val alg_embed_def = Define `(alg_embed [] s = T)
  /\ (alg_embed (h::t) s = (h = SHD s) /\ alg_embed t (STL s))`;

val algebra_embed_def = Define `(algebra_embed [] = {})
  /\ (algebra_embed (h::t) = alg_embed h UNION algebra_embed t)`;

val measurable_def = Define `measurable s = (?b. s = algebra_embed b)`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. algebra_embed (alg_canon b) = algebra_embed b                          *)
(* 2. (alg_canon b = alg_canon c) = (algebra_embed b = algebra_embed c)      *)
(* 3. measurable a ==> measurable (COMPL a)                                  *)
(* 4. measurable a /\ measurable b ==> measurable (a UNION b)                *)
(* 5. measurable a /\ measurable b ==> measurable (a INTER b)                *)
(* 6. measurable (a o STL) = measurable a                                    *)
(* 7. measurable (a o SDROP n) = measurable a                                *)
(* ------------------------------------------------------------------------- *)

val HALVES_INTER = store_thm
  ("HALVES_INTER",
   ``(\x. SHD x = T) INTER (\x. SHD x = F) = {}``,
   PSET_TAC []);

val INTER_STL = store_thm
  ("INTER_STL",
   ``!p q. (p INTER q) o STL = p o STL INTER q o STL``,
   PSET_TAC [o_DEF]);

val COMPL_SHD = store_thm
  ("COMPL_SHD",
   ``!b. COMPL (\x. SHD x = b) = (\x. SHD x = ~b)``,
   PSET_TAC []
   ++ Cases_on `b`
   ++ PROVE_TAC []);

val ALG_EMBED_BASIC = store_thm
  ("ALG_EMBED_BASIC",
   ``(alg_embed [] = UNIV)
     /\ (!h t. alg_embed (h::t) = (\x. SHD x = h) INTER alg_embed t o STL)``,
   PSET_TAC [o_DEF, alg_embed_def]
   ++ PROVE_TAC []);

val ALG_EMBED_NIL = store_thm
  ("ALG_EMBED_NIL",
   ``!c. (!x. alg_embed c x) = (c = [])``,
   Cases >> RW_TAC std_ss [alg_embed_def]
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `SCONST (~h)`
   ++ RW_TAC std_ss [alg_embed_def, SHD_SCONST]
   ++ Cases_on `h`
   ++ RW_TAC std_ss []);

val ALG_EMBED_POPULATED = store_thm
  ("ALG_EMBED_POPULATED",
   ``!b. ?x. alg_embed b x``,
   Induct >> PROVE_TAC [alg_embed_def]
   ++ REWRITE_TAC [alg_embed_def]
   ++ POP_ASSUM MP_TAC
   ++ REPEAT STRIP_TAC
   ++ MP_TAC (SPECL [``h:bool``, ``x:num->bool``] SHD_STL_ISO)
   ++ STRIP_TAC
   ++ PROVE_TAC []);

val ALG_EMBED_PREFIX = store_thm
  ("ALG_EMBED_PREFIX",
   ``!b c s. alg_embed b s /\ alg_embed c s
             ==> IS_PREFIX b c \/ IS_PREFIX c b``,
   Induct >> RW_TAC list_ss [IS_PREFIX]
   ++ Cases_on `c` >> RW_TAC list_ss [IS_PREFIX]
   ++ RW_TAC list_ss [alg_embed_def, IS_PREFIX]
   ++ PROVE_TAC []);

val ALG_EMBED_PREFIX_SUBSET = store_thm
  ("ALG_EMBED_PREFIX_SUBSET",
   ``!b c. alg_embed b SUBSET alg_embed c = IS_PREFIX b c``,
   Induct
   >> (PSET_TAC []
       ++ RW_TAC list_ss [IS_PREFIX_NIL, alg_embed_def, ALG_EMBED_NIL])
   ++ PSET_TAC []
   ++ Cases_on `c` >> RW_TAC std_ss [alg_embed_def, IS_PREFIX]
   ++ RW_TAC std_ss [alg_embed_def, IS_PREFIX]
   ++ Q.PAT_ASSUM `!c. P c = Q c` (fn th => REWRITE_TAC [SYM (Q.SPEC `t` th)])
   ++ EQ_TAC <<
   [STRIP_TAC
    ++ KNOW_TAC `h = h'`
    >> (MP_TAC (Q.SPEC `b` ALG_EMBED_POPULATED)
        ++ STRIP_TAC
        ++ Q.PAT_ASSUM `!x. P x ==> Q x` (MP_TAC o Q.SPEC `SCONS h x`)
        ++ RW_TAC std_ss [SHD_SCONS, STL_SCONS])
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `!x. P x ==> Q x` (MP_TAC o Q.SPEC `SCONS h x`)
    ++ RW_TAC std_ss [SHD_SCONS, STL_SCONS],
    RW_TAC std_ss []]);

val ALG_EMBED_TWINS = store_thm
  ("ALG_EMBED_TWINS",
   ``!l. alg_embed (SNOC T l) UNION alg_embed (SNOC F l) = alg_embed l``,
   Induct <<
   [PSET_TAC []
    ++ SEQ_CASES_TAC `v`
    ++ RW_TAC std_ss [SNOC, alg_embed_def, SHD_SCONS, STL_SCONS],
    RW_TAC std_ss [SNOC]
    ++ PSET_TAC [alg_embed_def]
    ++ SEQ_CASES_TAC `v`
    ++ POP_ASSUM (MP_TAC o Q.SPEC `t`)
    ++ RW_TAC std_ss [SHD_SCONS, STL_SCONS]
    ++ PROVE_TAC []]);

val ALGEBRA_EMBED_BASIC = store_thm
  ("ALGEBRA_EMBED_BASIC",
   ``(algebra_embed [] = {}) /\ (algebra_embed [[]] = UNIV)
     /\ (!b. algebra_embed [[b]] = (\s. SHD s = b))``,
   PSET_TAC [algebra_embed_def, alg_embed_def]
   ++ PROVE_TAC []);

val ALGEBRA_EMBED_MEM = store_thm
  ("ALGEBRA_EMBED_MEM",
   ``!b x. algebra_embed b x ==> (?l. MEM l b /\ alg_embed l x)``,
   Induct >> PSET_TAC [algebra_embed_def]
   ++ PSET_TAC [algebra_embed_def, MEM] <<
   [PROVE_TAC [],
    PROVE_TAC []]);

val ALGEBRA_EMBED_APPEND = store_thm
  ("ALGEBRA_EMBED_APPEND",
   ``!l1 l2. algebra_embed (APPEND l1 l2)
             = algebra_embed l1 UNION algebra_embed l2``,
   REPEAT STRIP_TAC
   ++ Induct_on `l1` >> PSET_TAC [APPEND, algebra_embed_def]
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC list_ss [algebra_embed_def]
   ++ PSET_TAC []
   ++ PROVE_TAC []);

val ALGEBRA_EMBED_TLS = store_thm
  ("ALGEBRA_EMBED_TLS",
   ``!l b. algebra_embed (MAP (CONS b) l) (SCONS h t)
           = (h = b) /\ algebra_embed l t``,
   REPEAT STRIP_TAC
   ++ Induct_on `l` >> PSET_TAC [MAP, algebra_embed_def]
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ PSET_TAC [MAP, algebra_embed_def, alg_embed_def, SHD_SCONS, STL_SCONS]
   ++ KILL_ALL_TAC
   ++ PROVE_TAC []);

val ALG_CANON_PREFS_EMBED = store_thm
  ("ALG_CANON_PREFS_EMBED",
   ``!l b. algebra_embed (alg_canon_prefs l b) = algebra_embed (l::b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_prefs_def]
   ++ RW_TAC list_ss [alg_canon_prefs_def]
   ++ PSET_TAC [algebra_embed_def]
   ++ SUFF_TAC `alg_embed h SUBSET alg_embed l`
   >> (PSET_TAC [] ++ PROVE_TAC [])
   ++ PROVE_TAC [ALG_EMBED_PREFIX_SUBSET]);

val ALG_CANON_FIND_EMBED = store_thm
  ("ALG_CANON_FIND_EMBED",
   ``!l b. algebra_embed (alg_canon_find l b) = algebra_embed (l::b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_find_def]
   ++ POP_ASSUM MP_TAC
   ++ BasicProvers.NORM_TAC list_ss [alg_canon_find_def, algebra_embed_def] <<
   [MP_TAC (Q.SPECL [`l`, `h`] ALG_EMBED_PREFIX_SUBSET)
    ++ PSET_TAC []
    ++ PROVE_TAC [],
    PSET_TAC [] ++ PROVE_TAC [],
    MP_TAC (Q.SPECL [`l`, `h::b`] ALG_CANON_PREFS_EMBED)
    ++ BasicProvers.NORM_TAC std_ss [algebra_embed_def]]);

val ALG_CANON1_EMBED = store_thm
  ("ALG_CANON1_EMBED",
   ``!l. algebra_embed (alg_canon1 l) = algebra_embed l``,
   REWRITE_TAC [alg_canon1_def]
   ++ Induct >> RW_TAC list_ss [FOLDR]
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ MP_TAC ALG_CANON_FIND_EMBED
   ++ RW_TAC list_ss [algebra_embed_def, FOLDR]);

val ALG_CANON_MERGE_EMBED = store_thm
  ("ALG_CANON_MERGE_EMBED",
   ``!l b. algebra_embed (alg_canon_merge l b) = algebra_embed (l::b)``,
   Induct_on `b` >> RW_TAC std_ss [alg_canon_merge_def]
   ++ RW_TAC list_ss [alg_canon_merge_def, alg_twin_def]
   ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC std_ss [BUTLAST, algebra_embed_def]
   ++ MP_TAC (Q.SPEC `l'` ALG_EMBED_TWINS)
   ++ PSET_TAC []
   ++ PROVE_TAC []);

val ALG_CANON2_EMBED = store_thm
  ("ALG_CANON2_EMBED",
   ``!l. algebra_embed (alg_canon2 l) = algebra_embed l``,
   REWRITE_TAC [alg_canon2_def]
   ++ Induct >> RW_TAC list_ss [FOLDR]
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ MP_TAC ALG_CANON_MERGE_EMBED
   ++ RW_TAC list_ss [algebra_embed_def, FOLDR]);

val ALG_CANON_EMBED = store_thm
  ("ALG_CANON_EMBED",
   ``!l. algebra_embed (alg_canon l) = algebra_embed l``,
   RW_TAC std_ss [alg_canon_def, ALG_CANON1_EMBED, ALG_CANON2_EMBED]);

val ALGEBRA_CANON_UNIV = store_thm
  ("ALGEBRA_CANON_UNIV",
   ``!l. algebra_canon l ==> ((algebra_embed l = UNIV) ==> (l = [[]]))``,
   HO_MATCH_MP_TAC ALGEBRA_CANON_INDUCTION
   ++ RW_TAC std_ss []
   >> PSET_TAC [algebra_embed_def, FOLDR]
   ++ KNOW_TAC `(algebra_embed l = UNIV)`
   >> (POP_ASSUM MP_TAC
       ++ PSET_TAC [ALGEBRA_EMBED_APPEND]
       ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
       ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS])
   ++ KNOW_TAC `(algebra_embed l' = UNIV)`
   >> (Q.PAT_ASSUM `algebra_embed (APPEND X Y) = UNIV` MP_TAC
       ++ PSET_TAC [ALGEBRA_EMBED_APPEND]
       ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS F v`)
       ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS])
   ++ RES_TAC
   ++ Q.PAT_ASSUM `algebra_canon (APPEND X Y)` MP_TAC
   ++ RW_TAC prob_canon_ss [algebra_canon_def]);

val ALG_CANON_REP = store_thm
  ("ALG_CANON_REP",
   ``!b c. (alg_canon b = alg_canon c)
           = (algebra_embed b = algebra_embed c)``,
   REPEAT STRIP_TAC
   ++ EQ_TAC >> PROVE_TAC [ALG_CANON_EMBED]
   ++ SUFF_TAC `!b. algebra_canon b ==> (!c. algebra_canon c ==>
                  (algebra_embed b = algebra_embed c) ==> (b = c))`
   >> (DISCH_THEN (MP_TAC o Q.SPEC `alg_canon b`)
       ++ RW_TAC std_ss [algebra_canon_def, ALG_CANON_IDEMPOT]
       ++ Q.PAT_ASSUM `!c. P c` (MP_TAC o Q.SPEC `alg_canon c`)
       ++ RW_TAC std_ss [ALG_CANON_IDEMPOT, ALG_CANON_EMBED])
   ++ HO_MATCH_MP_TAC ALGEBRA_CANON_INDUCTION
   ++ RW_TAC std_ss [] <<
   [Cases_on `c` >> RW_TAC std_ss []
    ++ PSET_TAC [algebra_embed_def, FOLDR]
    ++ PROVE_TAC [ALG_EMBED_POPULATED],
    PROVE_TAC [ALGEBRA_EMBED_BASIC, ALGEBRA_CANON_UNIV],
    NTAC 2 (POP_ASSUM MP_TAC)
    ++ Q.SPEC_TAC (`c`, `c`)
    ++ HO_MATCH_MP_TAC ALGEBRA_CANON_CASES
    ++ RW_TAC std_ss [] <<
    [POP_ASSUM MP_TAC
     ++ REVERSE (Cases_on `b`)
     >> (PSET_TAC [algebra_embed_def, FOLDR, APPEND, MAP]
         ++ PROVE_TAC [ALG_EMBED_POPULATED])
     ++ REVERSE (Cases_on `b'`)
     >> (PSET_TAC [algebra_embed_def, FOLDR, APPEND, MAP]
         ++ PROVE_TAC [ALG_EMBED_POPULATED])
     ++ RW_TAC list_ss [MAP],
     PROVE_TAC [ALGEBRA_EMBED_BASIC, ALGEBRA_CANON_UNIV],
     KNOW_TAC `algebra_embed b = algebra_embed l1`
     >> (POP_ASSUM MP_TAC
         ++ KILL_ALL_TAC
         ++ PSET_TAC [ALGEBRA_EMBED_APPEND]
         ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
         ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS])
     ++ KNOW_TAC `algebra_embed b' = algebra_embed l2`
     >> (POP_ASSUM (K ALL_TAC)
         ++ POP_ASSUM MP_TAC
         ++ KILL_ALL_TAC
         ++ PSET_TAC [ALGEBRA_EMBED_APPEND]
         ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS F v`)
         ++ RW_TAC std_ss [ALGEBRA_EMBED_TLS])
     ++ RES_TAC
     ++ RW_TAC std_ss []]]);

val ALGEBRA_CANON_EMBED_EMPTY = store_thm
  ("ALGEBRA_CANON_EMBED_EMPTY",
   ``!l. algebra_canon l ==> ((!v. ~algebra_embed l v) = (l = []))``,
   RW_TAC std_ss []
   ++ REVERSE EQ_TAC >> PSET_TAC [ALGEBRA_EMBED_BASIC]
   ++ RW_TAC std_ss []
   ++ SUFF_TAC `alg_canon l = alg_canon []`
   >> PROVE_TAC [algebra_canon_def, ALG_CANON_BASIC]
   ++ PSET_TAC [ALG_CANON_REP, ALGEBRA_EMBED_BASIC]);

val ALGEBRA_CANON_EMBED_UNIV = store_thm
  ("ALGEBRA_CANON_EMBED_UNIV",
   ``!l. algebra_canon l ==> ((!v. algebra_embed l v) = (l = [[]]))``,
   RW_TAC std_ss []
   ++ REVERSE EQ_TAC >> PSET_TAC [ALGEBRA_EMBED_BASIC]
   ++ RW_TAC std_ss []
   ++ SUFF_TAC `alg_canon l = alg_canon [[]]`
   >> PROVE_TAC [algebra_canon_def, ALG_CANON_BASIC]
   ++ PSET_TAC [ALG_CANON_REP, ALGEBRA_EMBED_BASIC]);

val MEASURABLE_ALGEBRA = store_thm
  ("MEASURABLE_ALGEBRA",
   ``!b. measurable (algebra_embed b)``,
   RW_TAC std_ss [measurable_def]
   ++ PROVE_TAC []);

val MEASURABLE_BASIC = store_thm
  ("MEASURABLE_BASIC",
   ``measurable {} /\ measurable UNIV /\ (!b. measurable (\s. SHD s = b))``,
   RW_TAC std_ss [measurable_def] <<
   [Q.EXISTS_TAC `[]`
    ++ RW_TAC std_ss [ALGEBRA_EMBED_BASIC],
    Q.EXISTS_TAC `[[]]`
    ++ RW_TAC std_ss [ALGEBRA_EMBED_BASIC],
    Q.EXISTS_TAC `[[b]]`
    ++ PSET_TAC [algebra_embed_def, alg_embed_def]
    ++ PROVE_TAC []]);

val MEASURABLE_SHD = store_thm
  ("MEASURABLE_SHD",
   ``!b. measurable (\s. SHD s = b)``,
   RW_TAC std_ss [MEASURABLE_BASIC]);

val ALGEBRA_EMBED_COMPL = store_thm
  ("ALGEBRA_EMBED_COMPL",
   ``!l. ?l'. COMPL (algebra_embed l) = algebra_embed l'``,
   STRIP_TAC
   ++ SUFF_TAC `!l. algebra_canon l ==>
                  (?l'. COMPL (algebra_embed l) = algebra_embed l')`
   >> (DISCH_THEN (MP_TAC o Q.SPEC `alg_canon l`)
       ++ RW_TAC std_ss [algebra_canon_def, ALG_CANON_EMBED, ALG_CANON_IDEMPOT])
   ++ HO_MATCH_MP_TAC ALGEBRA_CANON_INDUCTION
   ++ PSET_TAC [ALGEBRA_EMBED_BASIC] <<
   [Q.EXISTS_TAC `[[]]`
    ++ PSET_TAC [ALGEBRA_EMBED_BASIC],
    Q.EXISTS_TAC `[]`
    ++ PSET_TAC [ALGEBRA_EMBED_BASIC],
    Q.EXISTS_TAC `APPEND (MAP (CONS T) l'') (MAP (CONS F) l''')`
    ++ STRIP_TAC
    ++ SEQ_CASES_TAC `v`
    ++ PSET_TAC [ALGEBRA_EMBED_APPEND, ALGEBRA_EMBED_TLS]
    ++ PROVE_TAC []]);

val MEASURABLE_COMPL = store_thm
  ("MEASURABLE_COMPL",
   ``!s. measurable (COMPL s) = measurable s``,
   SUFF_TAC `!s. measurable s ==> measurable (COMPL s)`
   >> PROVE_TAC [COMPL_COMPL]
   ++ RW_TAC std_ss [measurable_def]
   ++ PROVE_TAC [ALGEBRA_EMBED_COMPL]);

val MEASURABLE_UNION = store_thm
  ("MEASURABLE_UNION",
   ``!s t. measurable s /\ measurable t ==> measurable (s UNION t)``,
   RW_TAC std_ss [measurable_def]
   ++ Q.EXISTS_TAC `APPEND b b'`
   ++ RW_TAC std_ss [ALGEBRA_EMBED_APPEND]);

val MEASURABLE_INTER = store_thm
  ("MEASURABLE_INTER",
   ``!s t. measurable s /\ measurable t ==> measurable (s INTER t)``,
   RW_TAC std_ss [INTER_UNION_COMPL, MEASURABLE_COMPL,
		  MEASURABLE_UNION]);

val MEASURABLE_STL = store_thm
  ("MEASURABLE_STL",
   ``!p. measurable (p o STL) = measurable p``,
   RW_TAC std_ss [measurable_def]
   ++ EQ_TAC <<
   [STRIP_TAC
    ++ POP_ASSUM MP_TAC
    ++ SUFF_TAC `!b. algebra_canon b ==>
                     (p o STL = algebra_embed b) ==>
		     ?b'. (p = algebra_embed b')`
     >> (DISCH_THEN (MP_TAC o Q.SPEC `alg_canon b`)
	 ++ RW_TAC std_ss [algebra_canon_def, ALG_CANON_IDEMPOT,
                           ALG_CANON_EMBED])
   ++ HO_MATCH_MP_TAC ALGEBRA_CANON_CASES
   ++ PSET_TAC [o_DEF, ALGEBRA_EMBED_BASIC] <<
   [Q.EXISTS_TAC `[]`
    ++ PSET_TAC [ALGEBRA_EMBED_BASIC]
    ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
    ++ RW_TAC std_ss [STL_SCONS],
    Q.EXISTS_TAC `[[]]`
    ++ PSET_TAC [ALGEBRA_EMBED_BASIC]
    ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
    ++ RW_TAC std_ss [STL_SCONS],
    Q.EXISTS_TAC `l1`
    ++ PSET_TAC [ALGEBRA_EMBED_APPEND]
    ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS T v`)
    ++ RW_TAC std_ss [STL_SCONS, ALGEBRA_EMBED_TLS]],
    PSET_TAC [o_DEF]
    ++ Q.EXISTS_TAC `APPEND (MAP (CONS T) b) (MAP (CONS F) b)`
    ++ PSET_TAC [ALGEBRA_EMBED_APPEND]
    ++ SEQ_CASES_TAC `v`
    ++ RW_TAC std_ss [STL_SCONS, ALGEBRA_EMBED_TLS]
    ++ PROVE_TAC []]);

val MEASURABLE_SDROP = store_thm
  ("MEASURABLE_SDROP",
   ``!n p. measurable (p o SDROP n) = measurable p``,
   Induct >> RW_TAC std_ss' [SDROP_def, o_DEF, I_THM]
   ++ RW_TAC bool_ss [SDROP_def, o_ASSOC, MEASURABLE_STL]);

val MEASURABLE_INTER_HALVES = store_thm
  ("MEASURABLE_INTER_HALVES",
   ``!p. measurable ((\x. SHD x = T) INTER p)
         /\ measurable ((\x. SHD x = F) INTER p) = measurable p``,
   STRIP_TAC
   ++ REVERSE EQ_TAC <<
   [REPEAT STRIP_TAC
    ++ MATCH_MP_TAC MEASURABLE_INTER
    ++ RW_TAC std_ss [MEASURABLE_BASIC],
    REPEAT STRIP_TAC
    ++ ONCE_REWRITE_TAC [(GSYM o Q.SPECL [`(\x. SHD x = T)`, `p`]
                          o INST_TYPE [alpha |-> (num --> bool)]) COMPL_SPLITS]
    ++ MATCH_MP_TAC MEASURABLE_UNION
    ++ PURE_ASM_REWRITE_TAC [COMPL_SHD]
    ++ PROVE_TAC []]);

val MEASURABLE_HALVES = store_thm
  ("MEASURABLE_HALVES",
   ``!p q. measurable ((\x. SHD x = T) INTER p UNION (\x. SHD x = F) INTER q)
           = measurable ((\x. SHD x = T) INTER p)
             /\ measurable ((\x. SHD x = F) INTER q)``,
   REPEAT STRIP_TAC
   ++ REVERSE EQ_TAC <<
   [REPEAT STRIP_TAC
    ++ MATCH_MP_TAC MEASURABLE_UNION
    ++ RW_TAC std_ss [],
    REPEAT STRIP_TAC <<
    [SUFF_TAC `(\x. SHD x = T) INTER p = ((\x. SHD x = T) INTER
                 ((\x. SHD x = T) INTER p UNION (\x. SHD x = F) INTER q))`
     >> (DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
         ++ MATCH_MP_TAC MEASURABLE_INTER
         ++ RW_TAC std_ss [MEASURABLE_BASIC])
     ++ RW_TAC pset_ss []
     ++ PROVE_TAC [],
     SUFF_TAC `(\x. SHD x = F) INTER q = ((\x. SHD x = F) INTER
                 ((\x. SHD x = T) INTER p UNION (\x. SHD x = F) INTER q))`
     >> (DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
         ++ MATCH_MP_TAC MEASURABLE_INTER
         ++ RW_TAC std_ss [MEASURABLE_BASIC])
     ++ RW_TAC pset_ss []
     ++ PROVE_TAC []]]);

val MEASURABLE_INTER_SHD = store_thm
  ("MEASURABLE_INTER_SHD",
   ``!b p. measurable ((\x. SHD x = b) INTER p o STL) = measurable p``,
   RW_TAC std_ss []
   ++ REVERSE EQ_TAC <<
   [STRIP_TAC
    ++ MATCH_MP_TAC MEASURABLE_INTER
    ++ RW_TAC std_ss [MEASURABLE_BASIC, MEASURABLE_STL],
    PSET_TAC [measurable_def, o_DEF]
    ++ POP_ASSUM MP_TAC
    ++ SUFF_TAC `!b'. algebra_canon b' ==>
           (!v. (SHD v = b) /\ p (STL v) = algebra_embed b' v) ==>
           ?b. !v. p v = algebra_embed b v`
    >> (DISCH_THEN (MP_TAC o Q.SPEC `alg_canon b'`)
        ++ RW_TAC std_ss [ALG_CANON_EMBED, ALG_CANON_IDEMPOT,
                          algebra_canon_def])
    ++ HO_MATCH_MP_TAC ALGEBRA_CANON_CASES
    ++ REPEAT CONJ_TAC <<
    [PSET_TAC [ALGEBRA_EMBED_BASIC]
     ++ Q.EXISTS_TAC `[]`
     ++ STRIP_TAC
     ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS b v`)
     ++ PSET_TAC [ALGEBRA_EMBED_BASIC, SHD_SCONS, STL_SCONS],
     RW_TAC std_ss []
     ++ Q.EXISTS_TAC `[[]]`
     ++ STRIP_TAC
     ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS b v`)
     ++ PSET_TAC [ALGEBRA_EMBED_BASIC, SHD_SCONS, STL_SCONS],
     RW_TAC std_ss []
     ++ Q.EXISTS_TAC `if b then l1 else l2`
     ++ STRIP_TAC
     ++ POP_ASSUM (MP_TAC o Q.SPEC `SCONS b v`)
     ++ PSET_TAC [ALGEBRA_EMBED_APPEND, ALGEBRA_EMBED_TLS, SHD_SCONS,
                  STL_SCONS]]]);

val _ = export_theory ();

