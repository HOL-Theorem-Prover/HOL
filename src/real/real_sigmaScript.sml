(* ************************************************************************* *)
(* Sum of a real-valued function on a set: SIGMA f s                         *)
(* ************************************************************************* *)

(* interactive mode
app load ["bossLib", "arithmeticTheory", "combinTheory",
          "pred_setTheory", "realTheory", "realLib",
          "res_quanTools", "pairTheory", "seqTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib arithmeticTheory combinTheory
     pred_setTheory realTheory realLib res_quanTools pairTheory seqTheory;

(* interactive mode
quietdec := false;
*)

val _ = new_theory "real_sigma";

infixr 0 ++ << || THENC ORELSEC ORELSER ## |-> ORELSE;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;
val Strip = S_TAC;

fun K_TAC _ = ALL_TAC;
val KILL_TAC = POP_ASSUM_LIST K_TAC;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);


(* ----------------------------------------------------------------------
    REAL_SUM_IMAGE

    This constant is the same as standard mathematics \Sigma operator:

     \Sigma_{x\in P}{f(x)} = SUM_IMAGE f P

    Where f's range is the real numbers and P is finite.
   ---------------------------------------------------------------------- *)

val REAL_SUM_IMAGE_DEF = new_definition(
  "REAL_SUM_IMAGE_DEF",
  ``REAL_SUM_IMAGE f s = ITSET (\e acc. f e + acc) s (0:real)``);

val REAL_SUM_IMAGE_THM = store_thm(
  "REAL_SUM_IMAGE_THM",
  ``!f. (REAL_SUM_IMAGE f {} = 0) /\
        (!e s. FINITE s ==>
               (REAL_SUM_IMAGE f (e INSERT s) =
                f e + REAL_SUM_IMAGE f (s DELETE e)))``,
  REPEAT STRIP_TAC
  >> SIMP_TAC (srw_ss()) [ITSET_THM, REAL_SUM_IMAGE_DEF]
  ++ SIMP_TAC (srw_ss()) [REAL_SUM_IMAGE_DEF]
  ++ Q.ABBREV_TAC `g = \e acc. f e + acc`
  ++ Suff `ITSET g (e INSERT s) 0 =
                    g e (ITSET g (s DELETE e) 0)`
  >> (Q.UNABBREV_TAC `g` ++ SRW_TAC [] [])
  ++ MATCH_MP_TAC COMMUTING_ITSET_RECURSES
  ++ Q.UNABBREV_TAC `g`
  ++ RW_TAC real_ss []
  ++ REAL_ARITH_TAC);

val REAL_SUM_IMAGE_SING = store_thm(
  "REAL_SUM_IMAGE_SING",
  ``!f e. REAL_SUM_IMAGE f {e} = f e``,
  SRW_TAC [][REAL_SUM_IMAGE_THM]);

val REAL_SUM_IMAGE_POS = store_thm
  ("REAL_SUM_IMAGE_POS",
   ``!f s. FINITE s /\
	   (!x. x IN s ==> 0 <= f x) ==>
		0 <= REAL_SUM_IMAGE f s``,
   REPEAT STRIP_TAC
   ++ POP_ASSUM MP_TAC ++ Q.SPEC_TAC (`f`, `f`)
   ++ POP_ASSUM MP_TAC ++ Q.SPEC_TAC (`s`, `s`)
   ++ Q.ABBREV_TAC `Q = (\s. !f. (!x. x IN s ==> 0 <= f x) ==> 0 <= REAL_SUM_IMAGE f s)`
   ++ Suff `!s. FINITE s ==> Q s` >> (Q.UNABBREV_TAC `Q` ++ RW_TAC std_ss [])
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ Q.UNABBREV_TAC `Q`
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM]
   ++ MATCH_MP_TAC REAL_LE_ADD
   ++ CONJ_TAC >> FULL_SIMP_TAC real_ss [IN_INSERT]
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   ++ Q.PAT_ASSUM `!f. (!x. x IN s ==> 0 <= f x) ==> 0 <= REAL_SUM_IMAGE f s` MATCH_MP_TAC
   ++ REPEAT STRIP_TAC ++ Q.PAT_ASSUM `!x. b` MATCH_MP_TAC
   ++ RW_TAC std_ss [IN_INSERT]);

val REAL_SUM_IMAGE_SPOS = store_thm
  ("REAL_SUM_IMAGE_SPOS",
   ``!s. FINITE s /\ (~(s = {})) ==>
	   !f. (!x. x IN s ==> 0 < f x) ==>
		0 < REAL_SUM_IMAGE f s``,
   Suff `!s. FINITE s ==>
		(\s. (~(s = {})) ==>
	   !f. (!x. x IN s ==> 0 < f x) ==>
		0 < REAL_SUM_IMAGE f s) s`
   >> RW_TAC std_ss []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM,
		      FORALL_AND_THM]
   ++ Cases_on `s = {}`
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM]
   ++ MATCH_MP_TAC REAL_LT_ADD
   ++ ASM_SIMP_TAC real_ss []);

val REAL_SUM_IMAGE_NONZERO_lem = prove
  (``!P. FINITE P ==>
	(\P. !f. (!x.x IN P ==> 0 <= f x) /\ (?x. x IN P /\ ~(f x = 0)) ==>
		((~(REAL_SUM_IMAGE f P = 0)) = (~(P = {})))) P``,
   (MATCH_MP_TAC FINITE_INDUCT
    ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, NOT_INSERT_EMPTY, IN_INSERT]
    ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT])
   >> (ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
       ++ `0 <= f e + REAL_SUM_IMAGE f s`
		by (MATCH_MP_TAC REAL_LE_ADD
		    ++ RW_TAC std_ss []
		    ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
		    ++ METIS_TAC [])
       ++ ASM_REWRITE_TAC []
       ++ RW_TAC std_ss [GSYM real_lt]
       ++ MATCH_MP_TAC REAL_LTE_TRANS
       ++ Q.EXISTS_TAC `f e + 0`
       ++ CONJ_TAC
       >> (RW_TAC real_ss [] ++ POP_ASSUM (K ALL_TAC)
	   ++ POP_ASSUM MP_TAC ++ POP_ASSUM (MP_TAC o Q.SPECL [`e`])
	   ++ SIMP_TAC std_ss []
	   ++ REAL_ARITH_TAC)
       ++ MATCH_MP_TAC REAL_LE_ADD2
       ++ RW_TAC real_ss []
       ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
       ++ METIS_TAC [])
   ++ Cases_on `f e = 0`
   >> (RW_TAC real_ss [] ++ METIS_TAC [NOT_IN_EMPTY])
   ++ ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   ++ `0 <= f e + REAL_SUM_IMAGE f s`
		by (MATCH_MP_TAC REAL_LE_ADD
		    ++ RW_TAC std_ss []
		    ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
		    ++ METIS_TAC [])
   ++ ASM_REWRITE_TAC []
   ++ RW_TAC std_ss [GSYM real_lt]
   ++ MATCH_MP_TAC REAL_LTE_TRANS
   ++ Q.EXISTS_TAC `f e + 0`
   ++ CONJ_TAC
   >> (RW_TAC real_ss [] ++ POP_ASSUM (K ALL_TAC)
       ++ POP_ASSUM MP_TAC ++ POP_ASSUM (K ALL_TAC)
       ++ POP_ASSUM (K ALL_TAC) ++ POP_ASSUM (MP_TAC o Q.SPECL [`e`])
	   ++ SIMP_TAC std_ss []
	   ++ REAL_ARITH_TAC)
   ++ MATCH_MP_TAC REAL_LE_ADD2
   ++ RW_TAC real_ss []
   ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
   ++ METIS_TAC []);

val REAL_SUM_IMAGE_NONZERO = store_thm
  ("REAL_SUM_IMAGE_NONZERO",
   ``!P. FINITE P ==>
	!f. (!x.x IN P ==> 0 <= f x) /\ (?x. x IN P /\ ~(f x = 0)) ==>
		((~(REAL_SUM_IMAGE f P = 0)) = (~(P = {})))``,
   METIS_TAC [REAL_SUM_IMAGE_NONZERO_lem]);

val REAL_SUM_IMAGE_IF_ELIM_lem = prove
  (``!s. FINITE s ==>
		(\s. !P f. (!x. x IN s ==> P x) ==>
			(REAL_SUM_IMAGE (\x. if P x then f x else 0) s =
	 		 REAL_SUM_IMAGE f s)) s``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, IN_INSERT, DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_IF_ELIM = store_thm
  ("REAL_SUM_IMAGE_IF_ELIM",
   ``!s P f. FINITE s /\ (!x. x IN s ==> P x) ==>
		(REAL_SUM_IMAGE (\x. if P x then f x else 0) s =
	 	 REAL_SUM_IMAGE f s)``,
   METIS_TAC [REAL_SUM_IMAGE_IF_ELIM_lem]);

val REAL_SUM_IMAGE_FINITE_SAME_lem = prove
  (``!P. FINITE P ==>
	 (\P. !f p.
             p IN P /\ (!q. q IN P ==> (f p = f q)) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * f p)) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY, DELETE_NON_ELEMENT]
   ++ `f p = f e` by FULL_SIMP_TAC std_ss [IN_INSERT]
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT] ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC real_ss [CARD_INSERT, ADD1]
   ++ ONCE_REWRITE_TAC [GSYM REAL_ADD]
   ++ RW_TAC real_ss [REAL_ADD_RDISTRIB]
   ++ Suff `REAL_SUM_IMAGE f s = & (CARD s) * f e`
   >> RW_TAC real_ss [REAL_ADD_COMM]
   ++ (MP_TAC o Q.SPECL [`s`]) SET_CASES ++ RW_TAC std_ss []
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY]
   ++ `f e = f x` by FULL_SIMP_TAC std_ss [IN_INSERT]
   ++ FULL_SIMP_TAC std_ss [] ++ POP_ASSUM (K ALL_TAC)
   ++ Q.PAT_ASSUM `!f p. b` MATCH_MP_TAC ++ METIS_TAC [IN_INSERT]);

val REAL_SUM_IMAGE_FINITE_SAME = store_thm
  ("REAL_SUM_IMAGE_FINITE_SAME",
   ``!P. FINITE P ==>
	 !f p.
             p IN P /\ (!q. q IN P ==> (f p = f q)) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * f p)``,
   MP_TAC REAL_SUM_IMAGE_FINITE_SAME_lem ++ RW_TAC std_ss []);

val REAL_SUM_IMAGE_FINITE_CONST = store_thm
  ("REAL_SUM_IMAGE_FINITE_CONST",
   ``!P. FINITE P ==>
	!f x. (!y. f y = x) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * x)``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`P`]) REAL_SUM_IMAGE_FINITE_SAME
   ++ RW_TAC std_ss []
   ++ POP_ASSUM (MP_TAC o (Q.SPECL [`f`]))
   ++ RW_TAC std_ss []
   ++ (MP_TAC o Q.SPECL [`P`]) SET_CASES
   ++ RW_TAC std_ss [] >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY]
   ++ POP_ASSUM (K ALL_TAC)
   ++ POP_ASSUM MATCH_MP_TAC
   ++ Q.EXISTS_TAC `x'` ++ RW_TAC std_ss [IN_INSERT]);

val REAL_SUM_IMAGE_IN_IF_lem = prove
  (``!P. FINITE P ==>
		(\P.!f. REAL_SUM_IMAGE f P = REAL_SUM_IMAGE (\x. if x IN P then f x else 0) P) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM]
   ++ POP_ASSUM MP_TAC
   ++ ONCE_REWRITE_TAC [DELETE_NON_ELEMENT]
   ++ SIMP_TAC real_ss [IN_INSERT]
   ++ `REAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then f x else 0)) s =
       REAL_SUM_IMAGE (\x. (if x IN s then f x else 0)) s`
	by (POP_ASSUM (MP_TAC o Q.SPECL [`(\x. (if (x = e) \/ x IN s then f x else 0))`])
	    ++ RW_TAC std_ss [])
   ++ POP_ORW
   ++ POP_ASSUM (MP_TAC o Q.SPECL [`f`])
   ++ RW_TAC real_ss []);

val REAL_SUM_IMAGE_IN_IF = store_thm
  ("REAL_SUM_IMAGE_IN_IF",
   ``!P. FINITE P ==>
	!f. REAL_SUM_IMAGE f P = REAL_SUM_IMAGE (\x. if x IN P then f x else 0) P``,
   METIS_TAC [REAL_SUM_IMAGE_IN_IF_lem]);

val REAL_SUM_IMAGE_CMUL_lem = prove
  (``!f c P. FINITE P ==>
	(\P. REAL_SUM_IMAGE (\x. c * f x) P = c * (REAL_SUM_IMAGE f P)) P``,
   STRIP_TAC ++ STRIP_TAC ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, REAL_ADD_LDISTRIB, DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_CMUL = store_thm
  ("REAL_SUM_IMAGE_CMUL",
   ``!P. FINITE P ==>
	!f c. (REAL_SUM_IMAGE (\x. c * f x) P = c * (REAL_SUM_IMAGE f P))``,
   METIS_TAC [REAL_SUM_IMAGE_CMUL_lem]);

val REAL_SUM_IMAGE_NEG = store_thm
  ("REAL_SUM_IMAGE_NEG",
   ``!P. FINITE P ==>
	!f. (REAL_SUM_IMAGE (\x. ~ f x) P = ~ (REAL_SUM_IMAGE f P))``,
   REPEAT STRIP_TAC
   ++ (ASSUME_TAC o Q.SPECL [`f`, `~1`] o UNDISCH o Q.SPEC `P`) REAL_SUM_IMAGE_CMUL
   ++ FULL_SIMP_TAC real_ss []);

val REAL_SUM_IMAGE_IMAGE = store_thm
  ("REAL_SUM_IMAGE_IMAGE",
   ``!P. FINITE P ==>
	 !f'. INJ f' P (IMAGE f' P) ==>
              !f. REAL_SUM_IMAGE f (IMAGE f' P) = REAL_SUM_IMAGE (f o f') P``,
   Induct_on `FINITE`
   ++ SRW_TAC [][REAL_SUM_IMAGE_THM]
   ++ `IMAGE f' P DELETE f' e = IMAGE f' P`
   by (SRW_TAC [][EXTENSION]
       ++ EQ_TAC >> (METIS_TAC[])
       ++ POP_ASSUM MP_TAC
       ++ ASM_SIMP_TAC (srw_ss()) [INJ_DEF]
       ++ METIS_TAC[])
   ++ `P DELETE e = P` by METIS_TAC [DELETE_NON_ELEMENT]
   ++ SRW_TAC [][]
   ++ FIRST_X_ASSUM MATCH_MP_TAC
   ++ Q.PAT_ASSUM `INJ f' SS1 SS2` MP_TAC
   ++ CONV_TAC (BINOP_CONV (SIMP_CONV (srw_ss()) [INJ_DEF]))
   ++ METIS_TAC[]);

val REAL_SUM_IMAGE_DISJOINT_UNION_lem = prove
  (``!P.
	FINITE P ==>
	(\P. !P'. FINITE P' ==>
		(\P'. DISJOINT P P' ==>
			(!f. REAL_SUM_IMAGE f (P UNION P') =
		     	     REAL_SUM_IMAGE f P +
		     	     REAL_SUM_IMAGE f P')) P') P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ CONJ_TAC
   >> (RW_TAC real_ss [DISJOINT_EMPTY, UNION_EMPTY, REAL_SUM_IMAGE_THM])
   ++ REPEAT STRIP_TAC
   ++ CONV_TAC (BETA_CONV) ++ MATCH_MP_TAC FINITE_INDUCT
   ++ CONJ_TAC
   >> (RW_TAC real_ss [DISJOINT_EMPTY, UNION_EMPTY, REAL_SUM_IMAGE_THM])
   ++ FULL_SIMP_TAC std_ss [DISJOINT_INSERT]
   ++ ONCE_REWRITE_TAC [DISJOINT_SYM]
   ++ RW_TAC std_ss [INSERT_UNION, DISJOINT_INSERT, IN_INSERT]
   ++ FULL_SIMP_TAC std_ss [DISJOINT_SYM]
   ++ ONCE_REWRITE_TAC [UNION_COMM] ++ RW_TAC std_ss [INSERT_UNION]
   ++ ONCE_REWRITE_TAC [UNION_COMM] ++ ONCE_REWRITE_TAC [INSERT_COMM]
   ++ `FINITE (e INSERT s UNION s')` by RW_TAC std_ss [FINITE_INSERT, FINITE_UNION]
   ++ Q.ABBREV_TAC `Q = e INSERT s UNION s'`
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
   ++ Q.UNABBREV_TAC `Q`
   ++ `~ (e' IN (e INSERT s UNION s'))`
	by RW_TAC std_ss [IN_INSERT, IN_UNION]
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
   ++ REAL_ARITH_TAC);

val REAL_SUM_IMAGE_DISJOINT_UNION = store_thm
  ("REAL_SUM_IMAGE_DISJOINT_UNION",
   ``!P P'. FINITE P /\ FINITE P' /\ DISJOINT P P' ==>
		(!f. REAL_SUM_IMAGE f (P UNION P') =
		     REAL_SUM_IMAGE f P +
		     REAL_SUM_IMAGE f P')``,
   METIS_TAC [REAL_SUM_IMAGE_DISJOINT_UNION_lem]);

val REAL_SUM_IMAGE_EQ_CARD_lem = prove
   (``!P. FINITE P ==>
	(\P. REAL_SUM_IMAGE (\x. if x IN P then 1 else 0) P = (&(CARD P))) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY, IN_INSERT]
   ++ (MP_TAC o Q.SPECL [`s`]) CARD_INSERT
   ++ RW_TAC real_ss [ADD1] ++ ONCE_REWRITE_TAC [GSYM REAL_ADD]
   ++ Suff `REAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then 1 else 0)) (s DELETE e) =
		REAL_SUM_IMAGE (\x. (if x IN s then 1 else 0)) s`
   >> RW_TAC real_ss []
   ++ Q.PAT_ASSUM `REAL_SUM_IMAGE (\x. (if x IN s then 1 else 0)) s = & (CARD s)` (K ALL_TAC)
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   ++ `REAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then 1 else 0)) s =
       REAL_SUM_IMAGE (\x. if x IN s then (\x. (if (x = e) \/ x IN s then 1 else 0)) x else 0) s`
	by (METIS_TAC [REAL_SUM_IMAGE_IN_IF])
   ++ RW_TAC std_ss []);

val REAL_SUM_IMAGE_EQ_CARD = store_thm
  ("REAL_SUM_IMAGE_EQ_CARD",
   ``!P. FINITE P ==>
	(REAL_SUM_IMAGE (\x. if x IN P then 1 else 0) P = (&(CARD P)))``,
   METIS_TAC [REAL_SUM_IMAGE_EQ_CARD_lem]);

val REAL_SUM_IMAGE_INV_CARD_EQ_1 = store_thm
  ("REAL_SUM_IMAGE_INV_CARD_EQ_1",
   ``!P. (~(P = {})) /\ FINITE P ==>
		(REAL_SUM_IMAGE (\s. if s IN P then inv (& (CARD P)) else 0) P = 1)``,
    REPEAT STRIP_TAC
    ++ `(\s. if s IN P then inv (& (CARD P)) else 0) = (\s. inv (& (CARD P)) * (\s. if s IN P then 1 else 0) s)`
	by (RW_TAC std_ss [FUN_EQ_THM] ++ RW_TAC real_ss [])
    ++ POP_ORW
    ++ `REAL_SUM_IMAGE (\s. inv (& (CARD P)) * (\s. (if s IN P then 1 else 0)) s) P =
	(inv (& (CARD P))) * (REAL_SUM_IMAGE (\s. (if s IN P then 1 else 0)) P)`
		by (MATCH_MP_TAC REAL_SUM_IMAGE_CMUL ++ RW_TAC std_ss [])
    ++ POP_ORW
    ++ `REAL_SUM_IMAGE (\s. (if s IN P then 1 else 0)) P = (&(CARD P))`
		by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ_CARD ++ RW_TAC std_ss [])
    ++ POP_ORW
    ++ MATCH_MP_TAC REAL_MUL_LINV
    ++ RW_TAC real_ss []
    ++ METIS_TAC [CARD_EQ_0]);

val REAL_SUM_IMAGE_INTER_NONZERO_lem = prove
  (``!P. FINITE P ==>
	(\P. !f. REAL_SUM_IMAGE f (P INTER (\p. ~(f p = 0))) =
		 REAL_SUM_IMAGE f P) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, INTER_EMPTY, INSERT_INTER]
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   ++ (RW_TAC std_ss [IN_DEF] ++ RW_TAC real_ss [])
   ++ `FINITE (s INTER (\p. ~(f p = 0)))` by (MATCH_MP_TAC INTER_FINITE ++ RW_TAC std_ss [])
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
   ++ `~(e IN (s INTER (\p. ~(f p = 0))))`
	by RW_TAC std_ss [IN_INTER]
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_INTER_NONZERO = store_thm
  ("REAL_SUM_IMAGE_INTER_NONZERO",
   ``!P. FINITE P ==>
	!f. REAL_SUM_IMAGE f (P INTER (\p. ~(f p = 0))) =
		 REAL_SUM_IMAGE f P``,
   METIS_TAC [REAL_SUM_IMAGE_INTER_NONZERO_lem]);

val REAL_SUM_IMAGE_INTER_ELIM_lem = prove
  (``!P. FINITE P ==>
	(\P. !f P'. (!x. (~(x IN P')) ==> (f x = 0)) ==>
			(REAL_SUM_IMAGE f (P INTER P') =
			 REAL_SUM_IMAGE f P)) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [INTER_EMPTY, REAL_SUM_IMAGE_THM, INSERT_INTER]
   ++ Cases_on `e IN P'`
   >> (`~ (e IN (s INTER P'))` by RW_TAC std_ss [IN_INTER]
       ++ FULL_SIMP_TAC std_ss [INTER_FINITE, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT])
   ++ FULL_SIMP_TAC real_ss []
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_INTER_ELIM = store_thm
  ("REAL_SUM_IMAGE_INTER_ELIM",
   ``!P. FINITE P ==>
	 !f P'. (!x. (~(x IN P')) ==> (f x = 0)) ==>
			(REAL_SUM_IMAGE f (P INTER P') =
			 REAL_SUM_IMAGE f P)``,
   METIS_TAC [REAL_SUM_IMAGE_INTER_ELIM_lem]);

val REAL_SUM_IMAGE_COUNT = store_thm
  ("REAL_SUM_IMAGE_COUNT",
   ``!f n. REAL_SUM_IMAGE f (pred_set$count n) =
	   sum (0,n) f``,
   STRIP_TAC ++ Induct
   >> RW_TAC std_ss [pred_setTheory.count_def, REAL_SUM_IMAGE_THM, GSPEC_F, sum]
   ++ `pred_set$count (SUC n) = n INSERT pred_set$count n`
	by (RW_TAC std_ss [EXTENSION, IN_INSERT, pred_setTheory.IN_COUNT] ++ DECIDE_TAC)
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, sum, pred_setTheory.FINITE_COUNT]
   ++ `pred_set$count n DELETE n = pred_set$count n`
	by RW_TAC arith_ss [DELETE_DEF, DIFF_DEF, IN_SING, pred_setTheory.IN_COUNT,
			    Once EXTENSION, pred_setTheory.IN_COUNT, GSPECIFICATION,
		      	    DECIDE ``!(x:num) (y:num). x < y ==> ~(x = y)``]
   ++ RW_TAC std_ss [REAL_ADD_SYM]);

val REAL_SUM_IMAGE_MONO = store_thm
  ("REAL_SUM_IMAGE_MONO",
   ``!P. FINITE P ==>
	   !f f'. (!x. x IN P ==> f x <= f' x) ==>
		REAL_SUM_IMAGE f P <= REAL_SUM_IMAGE f' P``,
   Suff `!P. FINITE P ==>
		(\P. !f f'. (!x. x IN P ==> f x <= f' x) ==>
		REAL_SUM_IMAGE f P <= REAL_SUM_IMAGE f' P) P`
   >> PROVE_TAC []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT, IN_INSERT,
		      DISJ_IMP_THM, FORALL_AND_THM, REAL_LE_ADD2]);

val REAL_SUM_IMAGE_POS_MEM_LE = store_thm
  ("REAL_SUM_IMAGE_POS_MEM_LE",
   ``!P. FINITE P ==>
	!f. (!x. x IN P ==> 0 <= f x) ==>
	    (!x. x IN P ==> f x <= REAL_SUM_IMAGE f P)``,
   Suff `!P. FINITE P ==>
	(\P. !f. (!x. x IN P ==> 0 <= f x) ==>
	    (!x. x IN P ==> f x <= REAL_SUM_IMAGE f P)) P`
   >> PROVE_TAC []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, NOT_IN_EMPTY, IN_INSERT,
		     DISJ_IMP_THM, FORALL_AND_THM,
		     DELETE_NON_ELEMENT]
   >> (Suff `f e + 0 <= f e + REAL_SUM_IMAGE f s` >> RW_TAC real_ss []
       ++ MATCH_MP_TAC REAL_LE_LADD_IMP
       ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS ++ ASM_REWRITE_TAC [])
   ++ Suff `0 + f x <= f e + REAL_SUM_IMAGE f s` >> RW_TAC real_ss []
   ++ MATCH_MP_TAC REAL_LE_ADD2 ++ PROVE_TAC []);

val REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD = store_thm
  ("REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD",
   ``!P. FINITE P ==>
	!f. (REAL_SUM_IMAGE f P = 1) /\
	    (!x y. x IN P /\ y IN P ==> (f x = f y)) ==>
	    (!x. x IN P ==> (f x = inv (& (CARD P))))``,
   Suff `!P. FINITE P ==>
	(\P. !f. (REAL_SUM_IMAGE f P = 1) /\
	    (!x y. x IN P /\ y IN P ==> (f x = f y)) ==>
	    (!x. x IN P ==> (f x = inv (& (CARD P))))) P`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, IN_INSERT, DELETE_NON_ELEMENT]
  >> (RW_TAC std_ss [(UNDISCH o Q.SPEC `s`) CARD_INSERT]
      ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
      ++ Q.PAT_ASSUM `(f:'a->real) e + REAL_SUM_IMAGE f s = 1`
	(MP_TAC o REWRITE_RULE [Once ((UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF)])
      ++ `(\x:'a. (if (x IN s) then (f:'a -> real) x else (0:real))) =
	       (\x:'a. (if (x IN s) then (\x:'a. (f:'a -> real) e) x else (0:real)))`
	by METIS_TAC []
      ++ POP_ORW
      ++ ONCE_REWRITE_TAC [(GSYM o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF]
      ++ (MP_TAC o Q.SPECL [`(\x. (f:'a->real) e)`, `(f:'a->real) e`] o
	  UNDISCH o Q.ISPEC `s:'a -> bool`) REAL_SUM_IMAGE_FINITE_CONST
      ++ SIMP_TAC std_ss []
      ++ STRIP_TAC ++ POP_ASSUM (K ALL_TAC)
      ++ `f e + & (CARD s) * f e = f e *( & (CARD s) + 1)` by REAL_ARITH_TAC
      ++ POP_ORW
      ++ `1:real = &1` by RW_TAC real_ss []
      ++ POP_ASSUM (fn thm => SIMP_TAC std_ss [thm, REAL_OF_NUM_ADD, GSYM ADD1])
      ++ REPEAT (POP_ASSUM (K ALL_TAC))
      ++ METIS_TAC [REAL_NZ_IMP_LT, GSYM REAL_EQ_RDIV_EQ, REAL_INV_1OVER, SUC_NOT])
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
   ++ RW_TAC std_ss [(UNDISCH o Q.SPEC `s`) CARD_INSERT]
   ++ Q.PAT_ASSUM `f e + REAL_SUM_IMAGE f s = 1`
	(MP_TAC o REWRITE_RULE [Once ((UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF)])
   ++ `(\x:'a. (if (x IN s) then (f:'a -> real) x else (0:real))) =
	       (\x:'a. (if (x IN s) then (\x:'a. (f:'a -> real) e) x else (0:real)))`
	by METIS_TAC []
   ++ POP_ORW
   ++ ONCE_REWRITE_TAC [(GSYM o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF]
   ++ (MP_TAC o Q.SPECL [`(\x. (f:'a->real) e)`, `(f:'a->real) e`] o
	  UNDISCH o Q.ISPEC `s:'a -> bool`) REAL_SUM_IMAGE_FINITE_CONST
   ++ SIMP_TAC std_ss []
   ++ STRIP_TAC ++ POP_ASSUM (K ALL_TAC)
   ++ `f e + & (CARD s) * f e = f e *( & (CARD s) + 1)` by REAL_ARITH_TAC
   ++ POP_ORW
   ++ `1:real = &1` by RW_TAC real_ss []
   ++ POP_ASSUM (fn thm => SIMP_TAC std_ss [thm, REAL_OF_NUM_ADD, GSYM ADD1])
   ++ `f x = f e` by METIS_TAC [] ++ POP_ORW
   ++ REPEAT (POP_ASSUM (K ALL_TAC))
   ++ METIS_TAC [REAL_NZ_IMP_LT, GSYM REAL_EQ_RDIV_EQ, REAL_INV_1OVER, SUC_NOT]);

val REAL_SUM_IMAGE_ADD = store_thm
  ("REAL_SUM_IMAGE_ADD",
   ``!s. FINITE s ==> !f f'.
		(REAL_SUM_IMAGE (\x. f x + f' x) s =
		 REAL_SUM_IMAGE f s + REAL_SUM_IMAGE f' s)``,
   Suff `!s. FINITE s ==>
	(\s. !f f'.
		(REAL_SUM_IMAGE (\x. f x + f' x) s =
		 REAL_SUM_IMAGE f s + REAL_SUM_IMAGE f' s)) s`
   >> RW_TAC std_ss []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT]
   ++ REAL_ARITH_TAC);

val REAL_SUM_IMAGE_REAL_SUM_IMAGE = store_thm
  ("REAL_SUM_IMAGE_REAL_SUM_IMAGE",
   ``!s s' f. FINITE s /\ FINITE s' ==>
	(REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (f x) s') s =
	 REAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))``,
   Suff `!s. FINITE s ==>
	     (\s. !s' f. FINITE s' ==>
	(REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (f x) s') s =
	 REAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))) s`
   >> RW_TAC std_ss []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [CROSS_EMPTY, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT]
   ++ `((e INSERT s) CROSS s') = (IMAGE (\x. (e,x)) s') UNION (s CROSS s')`
	by (RW_TAC std_ss [Once EXTENSION, IN_INSERT, IN_SING, IN_CROSS, IN_UNION, IN_IMAGE]
	    ++ (MP_TAC o Q.ISPEC `x:'a#'b`) pair_CASES
	    ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [FST,SND, GSYM DELETE_NON_ELEMENT]
	    ++ METIS_TAC [])
   ++ POP_ORW
   ++ `DISJOINT (IMAGE (\x. (e,x)) s') (s CROSS s')`
	by (FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF, Once EXTENSION,
				  NOT_IN_EMPTY, IN_INTER, IN_CROSS, IN_SING, IN_IMAGE]
	    ++ STRIP_TAC ++ (MP_TAC o Q.ISPEC `x:'a#'b`) pair_CASES
	    ++ RW_TAC std_ss [FST, SND]
	    ++ METIS_TAC [])
   ++ (MP_TAC o REWRITE_RULE [GSYM AND_IMP_INTRO] o
	Q.ISPECL [`IMAGE (\x. (e:'a,x)) (s':'b->bool)`, `(s:'a->bool) CROSS (s':'b->bool)`])
	REAL_SUM_IMAGE_DISJOINT_UNION
   ++ RW_TAC std_ss [FINITE_CROSS, IMAGE_FINITE]
   ++ POP_ASSUM (K ALL_TAC)
   ++ (MP_TAC o Q.SPEC `(\x. (e,x))` o UNDISCH o Q.SPEC `s'` o
	INST_TYPE [``:'c``|->``:'a # 'b``] o INST_TYPE [``:'a``|->``:'b``] o
	INST_TYPE [``:'b``|->``:'c``]) REAL_SUM_IMAGE_IMAGE
   ++ RW_TAC std_ss [INJ_DEF, IN_IMAGE, o_DEF] ++ METIS_TAC []);

val REAL_SUM_IMAGE_0 = store_thm
  ("REAL_SUM_IMAGE_0",
   ``!s. FINITE s ==> (REAL_SUM_IMAGE (\x. 0) s = 0)``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`(\x. 0)`,`0`] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_FINITE_CONST
   ++ RW_TAC real_ss []);

val SEQ_REAL_SUM_IMAGE = store_thm
  ("SEQ_REAL_SUM_IMAGE",
   ``!s. FINITE s ==>
	!f f'. (!x. x IN s ==> (\n. f n x) --> f' x) ==>
	 	(\n. REAL_SUM_IMAGE (f n) s) -->
		REAL_SUM_IMAGE f' s``,
   Suff `!s. FINITE s ==>
		(\s. !f f'. (!x. x IN s ==> (\n. f n x) --> f' x) ==>
	 	(\n. REAL_SUM_IMAGE (f n) s) -->
		REAL_SUM_IMAGE f' s) s`
   >> RW_TAC std_ss []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, SEQ_CONST, IN_INSERT, DELETE_NON_ELEMENT]
   ++ `(\n. f n e + REAL_SUM_IMAGE (f n) s) = (\n. (\n. f n e) n + (\n. REAL_SUM_IMAGE (f n) s) n)`
   	by RW_TAC std_ss []
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_ADD
   ++ METIS_TAC []);

val NESTED_REAL_SUM_IMAGE_REVERSE = store_thm
  ("NESTED_REAL_SUM_IMAGE_REVERSE",
   ``!f s s'. FINITE s /\ FINITE s' ==>
		(REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (f x) s') s =
		 REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (\y. f y x) s) s')``,
   RW_TAC std_ss [REAL_SUM_IMAGE_REAL_SUM_IMAGE]
   ++ `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
	by (RW_TAC std_ss [EXTENSION, IN_CROSS, IN_IMAGE]
	    ++ EQ_TAC >> (STRIP_TAC ++ Q.EXISTS_TAC `(SND x, FST x)` ++ RW_TAC std_ss [PAIR])
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [FST, SND])
   ++ POP_ORW
   ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
   ++ `INJ (\x. (SND x,FST x)) (s CROSS s') (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
	by (RW_TAC std_ss [INJ_DEF, IN_IMAGE] >> METIS_TAC []
	    ++ METIS_TAC [PAIR, PAIR_EQ])
   ++ `REAL_SUM_IMAGE (\x. f (SND x) (FST x)) (IMAGE (\x. (SND x,FST x)) (s CROSS s')) =
       REAL_SUM_IMAGE ((\x. f (SND x) (FST x)) o (\x. (SND x,FST x))) (s CROSS s')`
	by METIS_TAC [REAL_SUM_IMAGE_IMAGE]
   ++ POP_ORW
   ++ RW_TAC std_ss [o_DEF]);

val REAL_SUM_IMAGE_EQ_sum = store_thm
("REAL_SUM_IMAGE_EQ_sum", ``!n r. sum (0,n) r = REAL_SUM_IMAGE r (count n)``,
  RW_TAC std_ss []
  ++ Induct_on `n`
  >> RW_TAC std_ss [sum,REAL_SUM_IMAGE_THM,COUNT_ZERO]
  ++ RW_TAC std_ss [sum,COUNT_SUC,REAL_SUM_IMAGE_THM,FINITE_COUNT]
  ++ Suff `count n DELETE n = count n`
  >> RW_TAC std_ss [REAL_ADD_COMM]
  ++ RW_TAC std_ss [GSYM DELETE_NON_ELEMENT,IN_COUNT]);

val REAL_SUM_IMAGE_POW = store_thm
 ("REAL_SUM_IMAGE_POW",``!a s. FINITE s
           ==> ((REAL_SUM_IMAGE a s) pow 2 =
                REAL_SUM_IMAGE (\(i,j). a i * a j) (s CROSS s):real)``,
  RW_TAC std_ss []
  ++ `(\(i,j). a i * a j) = (\x. (\i j. a i * a j) (FST x) (SND x))`
       by (RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `x`
	   ++ RW_TAC std_ss [])
  ++ POP_ORW
  ++ (MP_TAC o GSYM o Q.SPECL [`s`,`s`,`(\i j. a i * a j)`] o
          INST_TYPE [``:'b`` |-> ``:'a``]) REAL_SUM_IMAGE_REAL_SUM_IMAGE
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_CMUL]
  ++ RW_TAC std_ss [Once REAL_MUL_COMM,REAL_SUM_IMAGE_CMUL,POW_2]);

val REAL_SUM_IMAGE_EQ = store_thm
 ("REAL_SUM_IMAGE_EQ", ``!s (f:'a->real) f'. FINITE s /\ (!x. x IN s ==> (f x = f' x))
                         ==> (REAL_SUM_IMAGE f s = REAL_SUM_IMAGE f' s)``,
  RW_TAC std_ss []
  ++ ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF]
  ++ RW_TAC std_ss []);

val REAL_SUM_IMAGE_IN_IF_ALT = store_thm
  ("REAL_SUM_IMAGE_IN_IF_ALT",``!s f z:real.
         FINITE s ==> (REAL_SUM_IMAGE f s = REAL_SUM_IMAGE (\x. if x IN s then f x else z) s)``,
  RW_TAC std_ss []
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss []);

val REAL_SUM_IMAGE_SUB = store_thm
 ("REAL_SUM_IMAGE_SUB", ``!s (f:'a -> real) f'. FINITE s ==>
                 (REAL_SUM_IMAGE (\x. f x - f' x) s =
                  REAL_SUM_IMAGE f s - REAL_SUM_IMAGE f' s)``,
  RW_TAC std_ss [Once real_sub,REAL_SUM_IMAGE_ADD,Once REAL_NEG_MINUS1]
  ++ RW_TAC std_ss [Once real_sub,REAL_SUM_IMAGE_ADD,Once
     	    	    REAL_NEG_MINUS1,REAL_SUM_IMAGE_CMUL]
  ++ RW_TAC std_ss [GSYM REAL_NEG_MINUS1,real_sub]);

val REAL_SUM_IMAGE_MONO_SET = store_thm
 ("REAL_SUM_IMAGE_MONO_SET", ``!(f:'a -> real) s t.
         FINITE s /\ FINITE t /\ s SUBSET t /\ (!x. x IN t ==> 0 <= f x)
              ==> REAL_SUM_IMAGE f s <= REAL_SUM_IMAGE f t``,
  RW_TAC std_ss []
  ++ `t = s UNION (t DIFF s)` by RW_TAC std_ss [UNION_DIFF]
  ++ `FINITE (t DIFF s)` by RW_TAC std_ss [FINITE_DIFF]
  ++ `DISJOINT s (t DIFF s)` by (`DISJOINT s (t DIFF s)`
      by RW_TAC std_ss [DISJOINT_DEF,IN_DIFF,EXTENSION,GSPECIFICATION,
      	 	        NOT_IN_EMPTY,IN_INTER]
         ++ METIS_TAC [])
  ++ `REAL_SUM_IMAGE f t = REAL_SUM_IMAGE f s + REAL_SUM_IMAGE f (t DIFF s)`
      by METIS_TAC [REAL_SUM_IMAGE_DISJOINT_UNION]
  ++ POP_ORW
  ++ Suff `0 <= REAL_SUM_IMAGE f (t DIFF s)`
  >> REAL_ARITH_TAC
  ++ METIS_TAC [REAL_SUM_IMAGE_POS,IN_DIFF]);

val _ = overload_on ("SIGMA", ``REAL_SUM_IMAGE ``);

val _ = export_theory ();
