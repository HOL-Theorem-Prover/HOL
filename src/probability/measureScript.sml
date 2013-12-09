(* ------------------------------------------------------------------------- *)
(* Measure Theory defined on the extended reals and includes Borel spaces    *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble, Cambridge University                    *)
(* ------------------------------------------------------------------------- *)

(* interactive mode
app load ["arithmeticTheory", "realTheory", "seqTheory", "pred_setTheory","res_quanTheory",
		"res_quanTools", "listTheory", "transcTheory", "rich_listTheory", "pairTheory",
		"combinTheory", "realLib", "optionTheory", "real_sigmaTheory",
		"util_probTheory", "extrealTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib arithmeticTheory realTheory
     seqTheory pred_setTheory res_quanTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory
     real_sigmaTheory util_probTheory extrealTheory;

val _ = new_theory "measure";

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

val REVERSE = Tactical.REVERSE;

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;
val Strip = S_TAC;

fun K_TAC _ = ALL_TAC;
val KILL_TAC = POP_ASSUM_LIST K_TAC;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

val Cond =
  MATCH_MP_TAC (PROVE [] ``!a b c. a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
  ++ CONJ_TAC;

local
  val th = prove (``!a b. a /\ (a ==> b) ==> a /\ b``, PROVE_TAC [])
in
  val STRONG_CONJ_TAC :tactic = MATCH_MP_TAC th ++ CONJ_TAC
end;

fun wrap a = [a];
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);

(*
 interactive mode
quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Basic measure theory definitions.                                         *)
(* ------------------------------------------------------------------------- *)

val space_def = Define
   `space (x:'a->bool,y:('a->bool)->bool) = x`;


val subsets_def = Define
   `subsets (x:'a->bool,y:('a->bool)->bool) = y`;


val subset_class_def = Define
   `subset_class sp sts = !x. x IN sts ==> x SUBSET sp`;


val algebra_def = Define
  `algebra a =
     subset_class (space a) (subsets a) /\
     {} IN subsets a /\
     (!s. s IN subsets a ==> space a DIFF s IN subsets a) /\
     (!s t. s IN subsets a /\ t IN subsets a ==> s UNION t IN subsets a)`;


val sigma_algebra_def = Define
   `sigma_algebra a =
     algebra a /\
     !c. countable c /\ c SUBSET (subsets a) ==> BIGUNION c IN (subsets a)`;


val sigma_def = Define
   `sigma sp st = (sp, BIGINTER {s | st SUBSET s /\ sigma_algebra (sp,s)})`;


val m_space_def = Define
   `m_space (sp:'a->bool, sts:('a->bool)->bool, mu:('a->bool)->real) = sp`;


val measurable_sets_def = Define
   `measurable_sets (sp:'a->bool, sts:('a->bool)->bool, mu:('a->bool)->real) = sts`;


val measure_def = Define
   `measure (sp:'a->bool, sts:('a->bool)->bool, mu:('a->bool)->real) = mu`;


val positive_def = Define
  `positive m =
   (measure m {} = 0) /\ !s. s IN measurable_sets m ==> 0 <= measure m s`;


val additive_def = Define
  `additive m =
   !s t. s IN measurable_sets m /\ t IN measurable_sets m /\ DISJOINT s t ==>
   (measure m (s UNION t) = measure m s + measure m t)`;


val countably_additive_def = Define
  `countably_additive m =
   !f : num -> ('a -> bool).
     f IN (UNIV -> measurable_sets m) /\
     (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
     BIGUNION (IMAGE f UNIV) IN measurable_sets m ==>
     (measure m o f) sums measure m (BIGUNION (IMAGE f UNIV))`;


val subadditive_def = Define
  `subadditive m =
   !s t.
     s IN measurable_sets m /\ t IN measurable_sets m ==>
     measure m (s UNION t) <= measure m s + measure m t`;


val countably_subadditive_def = Define
  `countably_subadditive m =
   !f : num -> ('a -> bool).
     f IN (UNIV -> measurable_sets m) /\
     BIGUNION (IMAGE f UNIV) IN measurable_sets m /\
     summable (measure m o f) ==>
     measure m (BIGUNION (IMAGE f UNIV)) <= suminf (measure m o f)`;


val increasing_def = Define
  `increasing m =
   !s t.
     s IN measurable_sets m /\ t IN measurable_sets m /\ s SUBSET t ==>
     measure m s <= measure m t`;


val measure_space_def = Define
  `measure_space m =
   sigma_algebra (m_space m, measurable_sets m) /\ positive m /\ countably_additive m`;


val lambda_system_def = Define
  `lambda_system gen (lam : ('a -> bool) -> real) =
   {l |
    l IN (subsets gen) /\
    !s. s IN (subsets gen) ==> (lam (l INTER s) + lam ((space gen DIFF l) INTER s) = lam s)}`;


val outer_measure_space_def = Define
  `outer_measure_space m =
   positive m /\ increasing m /\ countably_subadditive m`;


val inf_measure_def = Define
  `inf_measure m s =
   inf
   {r |
    ?f.
      f IN (UNIV -> measurable_sets m) /\
      (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
      s SUBSET BIGUNION (IMAGE f UNIV) /\ ((measure m o f) sums r)}`;


val closed_cdi_def = Define
  `closed_cdi p =
   subset_class (space p) (subsets p) /\
   (!s. s IN (subsets p) ==> (space p DIFF s) IN (subsets p)) /\
     (!f : num -> 'a -> bool.
        f IN (UNIV -> (subsets p)) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
        BIGUNION (IMAGE f UNIV) IN (subsets p)) /\
     (!f : num -> 'a -> bool.
        f IN (UNIV -> (subsets p)) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
        BIGUNION (IMAGE f UNIV) IN (subsets p))`;


val smallest_closed_cdi_def = Define
  `smallest_closed_cdi a = (space a, BIGINTER {b | (subsets a) SUBSET b /\
                   closed_cdi (space a, b)})`;


val measurable_def = Define
  `measurable a b = {f | sigma_algebra a /\ sigma_algebra b /\
			 f IN (space a -> space b) /\
			 !s. s IN subsets b ==> ((PREIMAGE f s)INTER(space a)) IN subsets a}`;


val measure_preserving_def = Define
  `measure_preserving m1 m2 =
   {f |
    f IN measurable (m_space m1, measurable_sets m1) (m_space m2, measurable_sets m2) /\
    measure_space m1 /\ measure_space m2 /\
    !s.
      s IN measurable_sets m2 ==>
           (measure m1 ((PREIMAGE f s)INTER(m_space m1)) = measure m2 s)}`;

val indicator_fn_def = Define
   `indicator_fn s = \x. if x IN s then (1:extreal) else (0:extreal)`;

val pos_simple_fn_def = Define
   `pos_simple_fn m f (s:num->bool) a x =
        (!t. 0 <= f t) /\
	(!t. t IN m_space m ==> (f t = SIGMA (\i. Normal (x i) * (indicator_fn (a i) t)) s)) /\
	(!i. i IN s ==> a i IN measurable_sets m) /\
	FINITE s /\ (!i. i IN s ==> 0 <= x i) /\
	(!i j. i IN s /\ j IN s /\ (~(i=j)) ==> DISJOINT (a i) (a j)) /\
	(BIGUNION (IMAGE a s) = m_space m)`;

val null_set_def = Define `null_set m s = s IN measurable_sets m /\ (measure m s = 0)`;

(* ------------------------------------------------------------------------- *)
(* Basic measure theory theorems                                             *)
(* ------------------------------------------------------------------------- *)

val SPACE = store_thm
  ("SPACE",
   ``!a. (space a, subsets a) = a``,
   STRIP_TAC ++ MP_TAC (Q.ISPEC `(a :('a -> bool) # (('a -> bool) -> bool))` pair_CASES)
   ++ RW_TAC std_ss [space_def, subsets_def]);

val ALGEBRA_ALT_INTER = store_thm
  ("ALGEBRA_ALT_INTER",
   ``!a.
       algebra a =
       subset_class (space a) (subsets a) /\
       {} IN (subsets a) /\ (!s. s IN (subsets a) ==> (space a DIFF s) IN (subsets a)) /\
       !s t. s IN (subsets a) /\ t IN (subsets a) ==> s INTER t IN (subsets a)``,
   RW_TAC std_ss [algebra_def, subset_class_def]
   ++ EQ_TAC <<
   [RW_TAC std_ss []
    ++ Know `s INTER t =  space a DIFF ((space a DIFF s) UNION (space a DIFF t))`
    >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION]
	++ EQ_TAC
	>> (RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [SUBSET_DEF] ++ PROVE_TAC [])
	++ RW_TAC std_ss [] ++ ASM_REWRITE_TAC [])
    ++ RW_TAC std_ss [],
    RW_TAC std_ss []
    ++ Know `s UNION t = space a DIFF ((space a DIFF s) INTER (space a DIFF t))`
    >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION]
	++ EQ_TAC
	>> (RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [SUBSET_DEF] ++ PROVE_TAC [])
	++ RW_TAC std_ss [] ++ ASM_REWRITE_TAC [])
    ++ RW_TAC std_ss []]);


val ALGEBRA_EMPTY = store_thm
  ("ALGEBRA_EMPTY",
   ``!a. algebra a ==> {} IN (subsets a)``,
   RW_TAC std_ss [algebra_def]);


val ALGEBRA_SPACE = store_thm
  ("ALGEBRA_SPACE",
   ``!a. algebra a ==> (space a) IN (subsets a)``,
   RW_TAC std_ss [algebra_def]
   ++ PROVE_TAC [DIFF_EMPTY]);


val ALGEBRA_COMPL = store_thm
  ("ALGEBRA_COMPL",
   ``!a s. algebra a /\ s IN (subsets a) ==> (space a DIFF s) IN (subsets a)``,
   RW_TAC std_ss [algebra_def]);


val ALGEBRA_UNION = store_thm
  ("ALGEBRA_UNION",
   ``!a s t. algebra a /\ s IN (subsets a) /\ t IN (subsets a) ==> s UNION t IN (subsets a)``,
   RW_TAC std_ss [algebra_def]);


val ALGEBRA_INTER = store_thm
  ("ALGEBRA_INTER",
   ``!a s t. algebra a /\ s IN (subsets a) /\ t IN (subsets a) ==> s INTER t IN (subsets a)``,
   RW_TAC std_ss [ALGEBRA_ALT_INTER]);


val ALGEBRA_DIFF = store_thm
  ("ALGEBRA_DIFF",
   ``!a s t. algebra a /\ s IN (subsets a) /\ t IN (subsets a) ==> s DIFF t IN (subsets a)``,
   REPEAT STRIP_TAC
   ++ Know `s DIFF t = s INTER (space a DIFF t)`
   >> (RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER]
       ++ FULL_SIMP_TAC std_ss [algebra_def, SUBSET_DEF, subset_class_def]
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss [ALGEBRA_INTER, ALGEBRA_COMPL]);


val ALGEBRA_FINITE_UNION = store_thm
  ("ALGEBRA_FINITE_UNION",
   ``!a c. algebra a /\ FINITE c /\ c SUBSET (subsets a) ==> BIGUNION c IN (subsets a)``,
   RW_TAC std_ss [algebra_def]
   ++ NTAC 2 (POP_ASSUM MP_TAC)
   ++ Q.SPEC_TAC (`c`, `c`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [BIGUNION_EMPTY, BIGUNION_INSERT, INSERT_SUBSET]);


val ALGEBRA_INTER_SPACE = store_thm
  ("ALGEBRA_INTER_SPACE",
   ``!a s. algebra a /\ s IN subsets a ==> ((space a INTER s = s) /\ (s INTER space a = s))``,
   RW_TAC std_ss [algebra_def, SUBSET_DEF, IN_INTER, EXTENSION, subset_class_def]
   ++ PROVE_TAC []);

val LAMBDA_SYSTEM_EMPTY = store_thm
  ("LAMBDA_SYSTEM_EMPTY",
   ``!g0 lam. algebra g0 /\ positive (space g0, subsets g0, lam) ==> {} IN lambda_system g0 lam``,
   RW_TAC real_ss [lambda_system_def, GSPECIFICATION, positive_def,
                  INTER_EMPTY, DIFF_EMPTY, ALGEBRA_INTER_SPACE, measure_def]
   ++ FULL_SIMP_TAC std_ss [algebra_def]);


val LAMBDA_SYSTEM_COMPL = store_thm
  ("LAMBDA_SYSTEM_COMPL",
   ``!g0 lam l.
       algebra g0 /\ positive (space g0, subsets g0, lam) /\ l IN lambda_system g0 lam ==>
       (space g0) DIFF l IN lambda_system g0 lam``,
   RW_TAC real_ss [lambda_system_def, GSPECIFICATION, positive_def]
   >> PROVE_TAC [algebra_def, subset_class_def]
   ++ Know `(space g0 DIFF (space g0 DIFF l)) = l`
   >> (RW_TAC std_ss [Once EXTENSION, IN_DIFF, LEFT_AND_OVER_OR] ++ PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF])
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [REAL_ADD_SYM]);

val LAMBDA_SYSTEM_INTER = store_thm
  ("LAMBDA_SYSTEM_INTER",
   ``!g0 lam l1 l2.
       algebra g0 /\ positive (space g0, subsets g0, lam) /\
       l1 IN lambda_system g0 lam /\ l2 IN lambda_system g0 lam ==>
       (l1 INTER l2) IN lambda_system g0 lam``,
   RW_TAC real_ss [lambda_system_def, GSPECIFICATION, positive_def]
   >> PROVE_TAC [ALGEBRA_ALT_INTER]
   ++ Know
      `lam ((space g0 DIFF (l1 INTER l2)) INTER s) =
       lam (l2 INTER (space g0 DIFF l1) INTER s) + lam ((space g0 DIFF l2) INTER s)`
   >> (ONCE_REWRITE_TAC [EQ_SYM_EQ]
       ++ Know
          `l2 INTER (space g0 DIFF l1) INTER s = l2 INTER ((space g0 DIFF (l1 INTER l2)) INTER s)`
       >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF]
           ++ PROVE_TAC [])
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ Know `(space g0 DIFF l2) INTER s = (space g0 DIFF l2) INTER ((space g0 DIFF (l1 INTER l2)) INTER s)`
       >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF]
           ++ PROVE_TAC [])
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ Q.PAT_ASSUM `!g. P g` MATCH_MP_TAC
       ++ PROVE_TAC [ALGEBRA_ALT_INTER])
   ++ Know `lam (l2 INTER s) + lam ((space g0 DIFF l2) INTER s) = lam s`
   >> PROVE_TAC []
   ++ Know
      `lam (l1 INTER l2 INTER s) + lam (l2 INTER (space g0 DIFF l1) INTER s) =
       lam (l2 INTER s)`
   >> (Know `l2 INTER (space g0 DIFF l1) INTER s = (space g0 DIFF l1) INTER (l2 INTER s)`
       >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF]
           ++ PROVE_TAC [])
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ REWRITE_TAC [GSYM INTER_ASSOC]
       ++ Q.PAT_ASSUM `!g. P g` K_TAC
       ++ Q.PAT_ASSUM `!g. P g` MATCH_MP_TAC
       ++ PROVE_TAC [ALGEBRA_ALT_INTER])
   ++ Q.SPEC_TAC (`l1 INTER l2`, `l`)
   ++ GEN_TAC
   ++ Q.SPEC_TAC (`lam (l2 INTER (space g0 DIFF l1) INTER s)`, `r1`)
   ++ Q.SPEC_TAC (`lam (l INTER s)`, `r2`)
   ++ Q.SPEC_TAC (`lam ((space g0 DIFF l2) INTER s)`, `r3`)
   ++ Q.SPEC_TAC (`lam (l2 INTER s)`, `r4`)
   ++ Q.SPEC_TAC (`lam s`, `r5`)
   ++ Q.SPEC_TAC (`lam ((space g0 DIFF l) INTER s)`, `r6`)
   ++ KILL_TAC
   ++ REAL_ARITH_TAC);

val LAMBDA_SYSTEM_ALGEBRA = store_thm
  ("LAMBDA_SYSTEM_ALGEBRA",
   ``!g0 lam.
       algebra g0 /\ positive (space g0, subsets g0, lam)
       ==> algebra (space g0, lambda_system g0 lam)``,
   RW_TAC std_ss [ALGEBRA_ALT_INTER, LAMBDA_SYSTEM_EMPTY, positive_def,
                  LAMBDA_SYSTEM_COMPL, LAMBDA_SYSTEM_INTER, space_def,
		  subsets_def, subset_class_def]
   ++ FULL_SIMP_TAC std_ss [lambda_system_def, GSPECIFICATION]);

val LAMBDA_SYSTEM_STRONG_ADDITIVE = store_thm
  ("LAMBDA_SYSTEM_STRONG_ADDITIVE",
   ``!g0 lam g l1 l2.
       algebra g0 /\ positive (space g0, subsets g0, lam) /\ g IN (subsets g0) /\ DISJOINT l1 l2 /\
       l1 IN lambda_system g0 lam /\ l2 IN lambda_system g0 lam ==>
       (lam ((l1 UNION l2) INTER g) = lam (l1 INTER g) + lam (l2 INTER g))``,
   RW_TAC std_ss [positive_def]
   ++ Know `l1 INTER g = l1 INTER ((l1 UNION l2) INTER g)`
   >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_UNION]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Know `l2 INTER g = (space g0 DIFF l1) INTER ((l1 UNION l2) INTER g)`
   >> (Q.PAT_ASSUM `DISJOINT x y` MP_TAC
       ++ RW_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, DISJOINT_DEF,
                         NOT_IN_EMPTY]
       ++ PROVE_TAC [algebra_def, SUBSET_DEF, subset_class_def])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Know `(l1 UNION l2) INTER g IN (subsets g0)`
   >> (Suff `l1 IN (subsets g0) /\ l2 IN (subsets g0)`
       >> PROVE_TAC [algebra_def, SUBSET_DEF, ALGEBRA_ALT_INTER, subset_class_def]
       ++ !! (POP_ASSUM MP_TAC)
       ++ RW_TAC std_ss [lambda_system_def, GSPECIFICATION])
   ++ STRIP_TAC
   ++ Q.PAT_ASSUM `l1 IN x` MP_TAC
   ++ RW_TAC std_ss [lambda_system_def, GSPECIFICATION]);

val LAMBDA_SYSTEM_ADDITIVE = store_thm
  ("LAMBDA_SYSTEM_ADDITIVE",
   ``!g0 lam l1 l2.
       algebra g0 /\ positive (space g0, subsets g0, lam) ==>
       additive (space g0, lambda_system g0 lam, lam)``,
   RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
   ++ MP_TAC (Q.SPECL [`g0`, `lam`, `space g0`, `s`, `t`]
              LAMBDA_SYSTEM_STRONG_ADDITIVE)
   ++ FULL_SIMP_TAC std_ss [lambda_system_def, GSPECIFICATION, ALGEBRA_INTER_SPACE,
      		    	    ALGEBRA_SPACE, ALGEBRA_UNION]);

val COUNTABLY_SUBADDITIVE_SUBADDITIVE = store_thm
  ("COUNTABLY_SUBADDITIVE_SUBADDITIVE",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ countably_subadditive m ==>
       subadditive m``,
   RW_TAC std_ss [countably_subadditive_def, subadditive_def]
   ++ Q.PAT_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n : num. if n = 0 then s else if n = 1 then t else {}`)
   ++ Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       s UNION t`
   >> (Suff
       `IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV =
        {s; t; {}}`
       >> (RW_TAC std_ss [BIGUNION, EXTENSION, IN_INSERT, GSPECIFICATION]
           ++ RW_TAC std_ss [GSYM EXTENSION]
           ++ RW_TAC std_ss [NOT_IN_EMPTY, IN_UNION]
           ++ PROVE_TAC [NOT_IN_EMPTY])
       ++ RW_TAC arith_ss [EXTENSION, IN_IMAGE, IN_INSERT, IN_UNIV]
       ++ RW_TAC std_ss [GSYM EXTENSION]
       ++ RW_TAC std_ss [NOT_IN_EMPTY]
       ++ KILL_TAC
       ++ EQ_TAC >> PROVE_TAC []
       ++ Know `~(0:num = 1) /\ ~(0:num = 2) /\ ~(1:num = 2)` >> DECIDE_TAC
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ Know
      `(measure m o (\n. (if n = 0 then s else (if n = 1 then t else {})))) sums
       (measure m s + measure m t)`
   >> (Know
       `measure m s + measure m t =
        sum (0,2)
        (measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))))`
       >> (ASM_SIMP_TAC bool_ss [TWO, sum, ONE, o_DEF]
           ++ RW_TAC arith_ss []
           ++ RW_TAC real_ss [])
       ++ DISCH_THEN (REWRITE_TAC o wrap)
       ++ MATCH_MP_TAC SER_0
       ++ RW_TAC arith_ss [o_DEF]
       ++ PROVE_TAC [positive_def])
   ++ REWRITE_TAC [SUMS_EQ]
   ++ DISCH_THEN (REWRITE_TAC o CONJUNCTS)
   ++ DISCH_THEN MATCH_MP_TAC
   ++ CONJ_TAC
   >> (Q.PAT_ASSUM `algebra a` MP_TAC
       ++ BasicProvers.NORM_TAC std_ss [IN_FUNSET, IN_UNIV, algebra_def, subsets_def, subset_class_def])
   ++ PROVE_TAC [algebra_def, subsets_def, subset_class_def]);


val SIGMA_ALGEBRA_ALT = store_thm
  ("SIGMA_ALGEBRA_ALT",
   ``!a.
       sigma_algebra a =
       algebra a /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> (subsets a)) ==> BIGUNION (IMAGE f UNIV) IN (subsets a))``,
   RW_TAC std_ss [sigma_algebra_def]
   ++ EQ_TAC
   >> (RW_TAC std_ss [countable_def, IN_FUNSET, IN_UNIV]
       ++ Q.PAT_ASSUM `!c. P c ==> Q c` MATCH_MP_TAC
       ++ REVERSE (RW_TAC std_ss [IN_IMAGE, SUBSET_DEF, IN_UNIV])
       >> PROVE_TAC []
       ++ Q.EXISTS_TAC `f`
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss [COUNTABLE_ALT]
   >> PROVE_TAC [ALGEBRA_FINITE_UNION]
   ++ Q.PAT_ASSUM `!f. P f` (MP_TAC o Q.SPEC `\n. enumerate c n`)
   ++ RW_TAC std_ss' [IN_UNIV, IN_FUNSET]
   ++ Know `BIGUNION c = BIGUNION (IMAGE (enumerate c) UNIV)`
   >> (RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV]
       ++ Suff `!s. s IN c = ?n. (enumerate c n = s)` >> PROVE_TAC []
       ++ Q.PAT_ASSUM `BIJ x y z` MP_TAC
       ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ POP_ASSUM MATCH_MP_TAC
   ++ Strip
   ++ Suff `enumerate c n IN c` >> PROVE_TAC [SUBSET_DEF]
   ++ Q.PAT_ASSUM `BIJ i j k` MP_TAC
   ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV]);


val SIGMA_ALGEBRA_ALT_MONO = store_thm
  ("SIGMA_ALGEBRA_ALT_MONO",
   ``!a.
       sigma_algebra a =
       algebra a /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> (subsets a)) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN (subsets a))``,
   RW_TAC std_ss [SIGMA_ALGEBRA_ALT]
   ++ EQ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n. BIGUNION (IMAGE f (count n))`)
   ++ RW_TAC std_ss [IN_UNIV, IN_FUNSET]
   ++ Know
      `BIGUNION (IMAGE f UNIV) =
       BIGUNION (IMAGE (\n. BIGUNION (IMAGE f (count n))) UNIV)`
   >> (KILL_TAC
       ++ ONCE_REWRITE_TAC [EXTENSION]
       ++ RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_UNIV]
       ++ EQ_TAC
       >> (RW_TAC std_ss []
           ++ Q.EXISTS_TAC `BIGUNION (IMAGE f (count (SUC x')))`
           ++ RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_COUNT]
           ++ PROVE_TAC [prim_recTheory.LESS_SUC_REFL])
       ++ RW_TAC std_ss []
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_COUNT]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ POP_ASSUM MATCH_MP_TAC
   ++ REVERSE (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_COUNT, IN_IMAGE,
                              COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY])
   >> (Q.EXISTS_TAC `f x'`
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `x'`
       ++ DECIDE_TAC)
   ++ MATCH_MP_TAC ALGEBRA_FINITE_UNION
   ++ POP_ASSUM MP_TAC
   ++ REVERSE (RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF, IN_IMAGE])
   >> PROVE_TAC []
   ++ MATCH_MP_TAC IMAGE_FINITE
   ++ RW_TAC std_ss [FINITE_COUNT]);


val SIGMA_ALGEBRA_ALT_DISJOINT = store_thm
  ("SIGMA_ALGEBRA_ALT_DISJOINT",
   ``!a.
       sigma_algebra a =
       algebra a /\
       (!f.
          f IN (UNIV -> (subsets a)) /\
          (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN (subsets a))``,
   Strip
   ++ EQ_TAC >> RW_TAC std_ss [SIGMA_ALGEBRA_ALT]
   ++ RW_TAC std_ss [SIGMA_ALGEBRA_ALT_MONO, IN_FUNSET, IN_UNIV]
   ++ Q.PAT_ASSUM `!f. P f ==> Q f` (MP_TAC o Q.SPEC `\n. f (SUC n) DIFF f n`)
   ++ RW_TAC std_ss []
   ++ Know
      `BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE (\n. f (SUC n) DIFF f n) UNIV)`
   >> (POP_ASSUM K_TAC
       ++ ONCE_REWRITE_TAC [EXTENSION]
       ++ RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_DIFF]
       ++ REVERSE EQ_TAC
       >> (RW_TAC std_ss []
           ++ POP_ASSUM MP_TAC
           ++ RW_TAC std_ss [IN_DIFF]
           ++ PROVE_TAC [])
       ++ RW_TAC std_ss []
       ++ Induct_on `x'` >> RW_TAC std_ss [NOT_IN_EMPTY]
       ++ RW_TAC std_ss []
       ++ Cases_on `x IN f x'` >> PROVE_TAC []
       ++ Q.EXISTS_TAC `f (SUC x') DIFF f x'`
       ++ RW_TAC std_ss [EXTENSION, IN_DIFF]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ POP_ASSUM MATCH_MP_TAC
   ++ CONJ_TAC >> RW_TAC std_ss [ALGEBRA_DIFF]
   ++ HO_MATCH_MP_TAC TRANSFORM_2D_NUM
   ++ CONJ_TAC >> PROVE_TAC [DISJOINT_SYM]
   ++ RW_TAC arith_ss []
   ++ Suff `f (SUC m) SUBSET f (m + n)`
   >> (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
                      IN_INTER, IN_DIFF, SUBSET_DEF]
       ++ PROVE_TAC [])
   ++ Cases_on `n` >> PROVE_TAC [ADD_CLAUSES]
   ++ POP_ASSUM K_TAC
   ++ Know `m + SUC n' = SUC m + n'` >> DECIDE_TAC
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ Induct_on `n'` >> RW_TAC arith_ss [SUBSET_REFL]
   ++ MATCH_MP_TAC SUBSET_TRANS
   ++ Q.EXISTS_TAC `f (SUC m + n')`
   ++ PROVE_TAC [ADD_CLAUSES]);


val SUBADDITIVE = store_thm
  ("SUBADDITIVE",
   ``!m s t u.
       subadditive m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       (u = s UNION t) ==>
       measure m u <= measure m s + measure m t``,
   RW_TAC std_ss [subadditive_def]);


val ADDITIVE = store_thm
  ("ADDITIVE",
   ``!m s t u.
       additive m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       DISJOINT s t /\ (u = s UNION t) ==>
       (measure m u = measure m s + measure m t)``,
   RW_TAC std_ss [additive_def]);


val COUNTABLY_SUBADDITIVE = store_thm
  ("COUNTABLY_SUBADDITIVE",
   ``!m f s.
       countably_subadditive m /\ f IN (UNIV -> measurable_sets m) /\
       summable (measure m o f) /\ (s = BIGUNION (IMAGE f UNIV)) /\
       (s IN measurable_sets m) ==>
       measure m s <= suminf (measure m o f)``,
   PROVE_TAC [countably_subadditive_def]);


val ADDITIVE_SUM = store_thm
  ("ADDITIVE_SUM",
   ``!m f n.
       algebra (m_space m, measurable_sets m) /\ positive m /\ additive m /\
       f IN (UNIV -> measurable_sets m) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       (sum (0, n) (measure m o f) =
        measure m (BIGUNION (IMAGE f (count n))))``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   ++ Induct_on `n`
   >> (RW_TAC std_ss [sum, COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY]
       ++ PROVE_TAC [positive_def])
   ++ RW_TAC std_ss [sum, COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT, ADD_CLAUSES,
                     o_DEF]
   ++ MATCH_MP_TAC EQ_SYM
   ++ ONCE_REWRITE_TAC [REAL_ADD_SYM]
   ++ MATCH_MP_TAC ADDITIVE
   ++ RW_TAC std_ss [DISJOINT_COUNT]
   ++ MATCH_MP_TAC ((REWRITE_RULE [subsets_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_FINITE_UNION)
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT]
   ++ PROVE_TAC [FINITE_COUNT, IMAGE_FINITE]);

val INCREASING_ADDITIVE_SUMMABLE = store_thm
  ("INCREASING_ADDITIVE_SUMMABLE",
   ``!m f.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m /\
       additive m /\ f IN (UNIV -> measurable_sets m) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       summable (measure m o f)``,
   RW_TAC std_ss [increasing_def]
   ++ MATCH_MP_TAC POS_SUMMABLE
   ++ CONJ_TAC
   >> FULL_SIMP_TAC std_ss [o_DEF, IN_FUNSET, IN_UNIV, positive_def]
   ++ Q.EXISTS_TAC `measure m (m_space m)`
   ++ RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`m`, `f`, `n`] ADDITIVE_SUM)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ Q.PAT_ASSUM `!(s : 'a -> bool). P s` MATCH_MP_TAC
   ++ CONJ_TAC
   >> (MATCH_MP_TAC ((REWRITE_RULE [subsets_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_FINITE_UNION)
       ++ Q.PAT_ASSUM `f IN x` MP_TAC
       ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF, IN_IMAGE]
       ++ PROVE_TAC [IMAGE_FINITE, FINITE_COUNT])
   ++ CONJ_TAC >> PROVE_TAC [ALGEBRA_SPACE, space_def, subsets_def]
   ++ Q.PAT_ASSUM `f IN x` MP_TAC
   ++ Q.PAT_ASSUM `algebra a` MP_TAC
   ++ RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_COUNT,
		     IN_FUNSET, IN_UNIV, algebra_def, space_def, subsets_def, subset_class_def]
   ++ PROVE_TAC []);

val LAMBDA_SYSTEM_POSITIVE = store_thm
  ("LAMBDA_SYSTEM_POSITIVE",
   ``!g0 lam. positive (space g0, subsets g0, lam) ==> positive (space g0, lambda_system g0 lam, lam)``,
   RW_TAC std_ss [positive_def, lambda_system_def, GSPECIFICATION,
                  measure_def, measurable_sets_def]);

val LAMBDA_SYSTEM_INCREASING = store_thm
  ("LAMBDA_SYSTEM_INCREASING",
   ``!g0 lam. increasing (space g0, subsets g0, lam) ==> increasing (space g0, lambda_system g0 lam, lam)``,
   RW_TAC std_ss [increasing_def, lambda_system_def, GSPECIFICATION,
                  measure_def, measurable_sets_def]);

val LAMBDA_SYSTEM_STRONG_SUM = store_thm
  ("LAMBDA_SYSTEM_STRONG_SUM",
   ``!g0 lam g f n.
       algebra g0 /\ positive (space g0, subsets g0, lam) /\ g IN (subsets g0) /\
       f IN (UNIV -> lambda_system g0 lam) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       (sum (0, n) (lam o (\s. s INTER g) o f) =
        lam (BIGUNION (IMAGE f (count n)) INTER g))``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   ++ Induct_on `n`
   >> (RW_TAC std_ss [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, sum, INTER_EMPTY]
       ++ PROVE_TAC [positive_def, measure_def])
   ++ RW_TAC arith_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT, sum, o_DEF]
   ++ ONCE_REWRITE_TAC [REAL_ADD_SYM]
   ++ MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC LAMBDA_SYSTEM_STRONG_ADDITIVE
   ++ Q.EXISTS_TAC `g0`
   ++ RW_TAC std_ss [DISJOINT_COUNT]
   ++ MATCH_MP_TAC ((REWRITE_RULE [subsets_def] o Q.SPEC `(space g0,lambda_system g0 lam)`) ALGEBRA_FINITE_UNION)
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, LAMBDA_SYSTEM_ALGEBRA]
   ++ PROVE_TAC [IMAGE_FINITE, FINITE_COUNT]);

val SIGMA_ALGEBRA_ALGEBRA = store_thm
  ("SIGMA_ALGEBRA_ALGEBRA",
   ``!a. sigma_algebra a ==> algebra a``,
   PROVE_TAC [sigma_algebra_def]);

val OUTER_MEASURE_SPACE_POSITIVE = store_thm
  ("OUTER_MEASURE_SPACE_POSITIVE",
   ``!m. outer_measure_space m ==> positive m``,
   PROVE_TAC [outer_measure_space_def]);

val LAMBDA_SYSTEM_CARATHEODORY = store_thm
  ("LAMBDA_SYSTEM_CARATHEODORY",
   ``!gsig lam.
       sigma_algebra gsig /\ outer_measure_space (space gsig, subsets gsig, lam) ==>
       (!f.
          f IN (UNIV -> lambda_system gsig lam) /\
          (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN lambda_system gsig lam /\
          ((lam o f) sums lam (BIGUNION (IMAGE f UNIV))))``,
   NTAC 5 STRIP_TAC
   ++ Know `summable (lam o f)`
   >> (Suff `summable (measure (space gsig, lambda_system gsig lam, lam) o f)`
       >> RW_TAC std_ss [measure_def]
       ++ MATCH_MP_TAC INCREASING_ADDITIVE_SUMMABLE
       ++ REWRITE_TAC [measurable_sets_def, m_space_def]
       ++ CONJ_TAC
       >> (MATCH_MP_TAC LAMBDA_SYSTEM_ALGEBRA
           ++ CONJ_TAC >> PROVE_TAC [sigma_algebra_def]
           ++ PROVE_TAC [outer_measure_space_def])
       ++ CONJ_TAC
       >> PROVE_TAC [LAMBDA_SYSTEM_POSITIVE, outer_measure_space_def]
       ++ CONJ_TAC
       >> PROVE_TAC [LAMBDA_SYSTEM_INCREASING, outer_measure_space_def]
       ++ CONJ_TAC
       >> PROVE_TAC [LAMBDA_SYSTEM_ADDITIVE, outer_measure_space_def,
                     sigma_algebra_def]
       ++ RW_TAC std_ss [])
   ++ STRIP_TAC
   ++ Know `BIGUNION (IMAGE f UNIV) IN subsets gsig`
   >> (Q.PAT_ASSUM `sigma_algebra a` MP_TAC
       ++ Q.PAT_ASSUM `f IN s` MP_TAC
       ++ RW_TAC std_ss [SIGMA_ALGEBRA_ALT, IN_FUNSET, IN_UNIV]
       ++ POP_ASSUM MATCH_MP_TAC
       ++ RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!x. P x` MP_TAC
       ++ RW_TAC std_ss [lambda_system_def, GSPECIFICATION])
   ++ STRIP_TAC
   ++ Suff
      `!g l.
         g IN subsets gsig /\ (BIGUNION (IMAGE f (UNIV : num -> bool)) = l) ==>
         (lam (l INTER g) + lam ((space gsig DIFF l) INTER g) = lam g) /\
         (lam (l INTER g) = suminf (lam o (\s. s INTER g) o f))`
   >> (RW_TAC std_ss [lambda_system_def, GSPECIFICATION, SUMS_EQ]
       ++ POP_ASSUM
          (MP_TAC o Q.SPEC `BIGUNION (IMAGE (f : num -> 'a -> bool) UNIV)`)
       ++ RW_TAC std_ss [INTER_IDEMPOT]
       ++ Suff `(\s. s INTER BIGUNION (IMAGE f UNIV)) o f = f`
       >> RW_TAC std_ss []
       ++ KILL_TAC
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ RW_TAC std_ss [o_DEF, EXTENSION, IN_INTER, IN_BIGUNION,
                         GSPECIFICATION, IN_IMAGE, IN_UNIV]
       ++ METIS_TAC [IN_INTER,SPECIFICATION,IN_BIGUNION_IMAGE,IN_UNIV])
   ++ !! GEN_TAC
   ++ STRIP_TAC
   ++ Know `summable (lam o (\s. s INTER g) o f)`
   >> (MATCH_MP_TAC SER_COMPAR
       ++ Q.EXISTS_TAC `lam o f`
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC arith_ss [o_DEF]
       ++ Q.PAT_ASSUM `outer_measure_space (space gsig,subsets gsig,lam)` MP_TAC
       ++ RW_TAC std_ss [outer_measure_space_def, increasing_def, positive_def,
                         measure_def, measurable_sets_def]
       ++ Know `f n IN subsets gsig`
       >> (Q.PAT_ASSUM `f IN x` MP_TAC
           ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, lambda_system_def,
                             GSPECIFICATION])
       ++ STRIP_TAC
       ++ Know `f n INTER g IN subsets gsig`
       >> PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def]
       ++ STRIP_TAC
       ++ Know `0 <= lam (f n INTER g)` >> PROVE_TAC []
       ++ RW_TAC std_ss [abs]
       ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
       ++ RW_TAC std_ss [SUBSET_DEF, IN_INTER])
   ++ STRIP_TAC
   ++ Suff
      `lam g <= lam (l INTER g) + lam ((space gsig DIFF l) INTER g) /\
       lam (l INTER g) <= suminf (lam o (\s. s INTER g) o f) /\
       suminf (lam o (\s. s INTER g) o f) + lam ((space gsig DIFF l) INTER g) <= lam g`
   >> REAL_ARITH_TAC
   ++ Strip <<
   [Know `lam = measure (space gsig,subsets gsig,lam)` >> RW_TAC std_ss [measure_def]
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC SUBADDITIVE
    ++ REWRITE_TAC [measurable_sets_def]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC COUNTABLY_SUBADDITIVE_SUBADDITIVE
        ++ REWRITE_TAC [measurable_sets_def, m_space_def, SPACE]
        ++ PROVE_TAC [outer_measure_space_def, sigma_algebra_def])
    ++ CONJ_TAC >> PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def]
    ++ CONJ_TAC >> PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def, ALGEBRA_COMPL]
    ++ RW_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_DIFF,
                      IN_UNION]
    ++ FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def, SUBSET_DEF, subset_class_def]
    ++ PROVE_TAC [],
    Q.PAT_ASSUM `f IN (x -> y)` MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV]
    ++ Know `lam = measure (space gsig,subsets gsig,lam)` >> RW_TAC std_ss [measure_def]
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC COUNTABLY_SUBADDITIVE
    ++ REWRITE_TAC [measurable_sets_def, measure_def]
    ++ CONJ_TAC >> PROVE_TAC [outer_measure_space_def]
    ++ CONJ_TAC
    >> (RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_DEF]
        ++ POP_ASSUM (MP_TAC o Q.SPEC `x`)
        ++ RW_TAC std_ss [lambda_system_def, GSPECIFICATION]
        ++ PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def])
    ++ CONJ_TAC >> PROVE_TAC []
    ++ CONJ_TAC
    >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION, IN_IMAGE, IN_UNIV,
                       o_DEF]
        ++ REVERSE EQ_TAC >> PROVE_TAC []
        ++ RW_TAC std_ss [GSYM EXTENSION]
        ++ Q.EXISTS_TAC `f x' INTER g`
        ++ RW_TAC std_ss [IN_INTER]
        ++ PROVE_TAC [])
    ++ PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def],
    Suff `suminf (lam o (\s. s INTER g) o f) <= lam g - lam ((space gsig DIFF l) INTER g)`
    >> REAL_ARITH_TAC
    ++ MATCH_MP_TAC SUMMABLE_LE
    ++ CONJ_TAC >> PROVE_TAC []
    ++ GEN_TAC
    ++ MP_TAC (Q.SPECL [`gsig`, `lam`, `g`, `f`, `n`] LAMBDA_SYSTEM_STRONG_SUM)
    ++ RW_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA, OUTER_MEASURE_SPACE_POSITIVE]
    ++ POP_ASSUM K_TAC
    ++ Suff
       `(lam g = lam (BIGUNION (IMAGE f (count n)) INTER g) +
                 lam ((space gsig DIFF BIGUNION (IMAGE f (count n))) INTER g)) /\
        lam ((space gsig DIFF BIGUNION (IMAGE f UNIV)) INTER g) <=
        lam ((space gsig DIFF BIGUNION (IMAGE f (count n))) INTER g)`
    >> REAL_ARITH_TAC
    ++ CONJ_TAC
    >> (Suff `BIGUNION (IMAGE f (count n)) IN lambda_system gsig lam`
        >> RW_TAC std_ss [lambda_system_def, GSPECIFICATION]
        ++ MATCH_MP_TAC ((REWRITE_RULE [subsets_def] o Q.SPEC `(space gsig,lambda_system gsig lam)`) ALGEBRA_FINITE_UNION)
        ++ Q.PAT_ASSUM `f IN (x -> y)` MP_TAC
        ++ RW_TAC std_ss [SUBSET_DEF, IN_FUNSET, IN_UNIV, IN_IMAGE]
        ++ PROVE_TAC [LAMBDA_SYSTEM_ALGEBRA, SIGMA_ALGEBRA_ALGEBRA,
                      OUTER_MEASURE_SPACE_POSITIVE, IMAGE_FINITE, FINITE_COUNT])
    ++ Q.PAT_ASSUM `outer_measure_space (space gsig,subsets gsig,lam)` MP_TAC
    ++ RW_TAC std_ss [outer_measure_space_def, increasing_def, measure_def,
                      measurable_sets_def]
    ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
    ++ CONJ_TAC
    >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_COMPL, ALGEBRA_INTER]
    ++ CONJ_TAC
    >> (Know `algebra gsig` >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA]
        ++ STRIP_TAC
        ++ MATCH_MP_TAC ALGEBRA_INTER
        ++ RW_TAC std_ss []
        ++ MATCH_MP_TAC ALGEBRA_COMPL
        ++ RW_TAC std_ss []
        ++ MATCH_MP_TAC ALGEBRA_FINITE_UNION
        ++ Q.PAT_ASSUM `f IN x` MP_TAC
        ++ RW_TAC std_ss [SUBSET_DEF, IN_FUNSET, IN_UNIV, lambda_system_def,
                          GSPECIFICATION, IN_IMAGE]
        ++ PROVE_TAC [IMAGE_FINITE, FINITE_COUNT])
    ++ RW_TAC std_ss [SUBSET_DEF, IN_INTER, IN_COMPL, IN_IMAGE, IN_BIGUNION,
                      IN_UNIV, IN_DIFF]
    ++ PROVE_TAC []]);

val CARATHEODORY_LEMMA = store_thm
  ("CARATHEODORY_LEMMA",
   ``!gsig lam.
       sigma_algebra gsig /\ outer_measure_space (space gsig, subsets gsig, lam) ==>
       measure_space (space gsig, lambda_system gsig lam, lam)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`gsig`, `lam`] LAMBDA_SYSTEM_CARATHEODORY)
   ++ RW_TAC std_ss [measure_space_def, countably_additive_def,
                     measurable_sets_def, measure_def, m_space_def] <<
   [RW_TAC std_ss [SIGMA_ALGEBRA_ALT_DISJOINT, subsets_def]
    ++ PROVE_TAC [LAMBDA_SYSTEM_ALGEBRA, SIGMA_ALGEBRA_ALGEBRA,
                  outer_measure_space_def],
    PROVE_TAC [outer_measure_space_def, LAMBDA_SYSTEM_POSITIVE]]);

val INF_MEASURE_NONEMPTY = store_thm
  ("INF_MEASURE_NONEMPTY",
   ``!m g s.
       algebra (m_space m, measurable_sets m) /\ positive m /\ s IN measurable_sets m /\
       g SUBSET s ==>
       measure m s IN
       {r |
        ?f.
          f IN (UNIV -> measurable_sets m) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
          g SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r}``,
   RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, positive_def]
   ++ Q.EXISTS_TAC `\n. if n = 0 then s else {}`
   ++ BasicProvers.NORM_TAC std_ss
      [SUBSET_DEF, IN_BIGUNION, DISJOINT_EMPTY,
       IN_IMAGE, IN_UNIV, o_DEF, IN_FUNSET, ALGEBRA_EMPTY]
   << [PROVE_TAC [subsets_def, ALGEBRA_EMPTY],
       PROVE_TAC [],
      Know `measure m s = sum (0,1) (\x. measure m (if x = 0 then s else {}))`
      >> (ASM_SIMP_TAC bool_ss [sum, ONE, REAL_ADD_LID] ++ RW_TAC arith_ss [])
      ++ DISCH_THEN (REWRITE_TAC o wrap)
      ++ MATCH_MP_TAC SER_0
      ++ RW_TAC arith_ss []]);

val INF_MEASURE_POS0 = store_thm
  ("INF_MEASURE_POS0",
   ``!m g x.
       algebra (m_space m,measurable_sets m) /\ positive m /\
       x IN
       {r |
        ?f.
          f IN (UNIV -> measurable_sets m) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
          g SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r} ==>
       0 <= x``,
   RW_TAC std_ss [GSPECIFICATION, SUMS_EQ, IN_FUNSET, IN_UNIV, positive_def]
   ++ MATCH_MP_TAC SER_POS
   ++ RW_TAC std_ss [o_DEF]);

val INF_MEASURE_POS = store_thm
  ("INF_MEASURE_POS",
   ``!m g. algebra (m_space m, measurable_sets m) /\ positive m /\ g SUBSET m_space m ==> 0 <= inf_measure m g``,
   RW_TAC std_ss [GSPECIFICATION, inf_measure_def]
   ++ MATCH_MP_TAC LE_INF
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `measure m (m_space m)`
       ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
       ++ PROVE_TAC [ALGEBRA_SPACE, space_def, subsets_def])
   ++ METIS_TAC [INF_MEASURE_POS0]);

val INCREASING = store_thm
  ("INCREASING",
   ``!m s t.
       increasing m /\ s SUBSET t /\ s IN measurable_sets m /\
       t IN measurable_sets m ==>
       measure m s <= measure m t``,
   PROVE_TAC [increasing_def]);

val ADDITIVE_INCREASING = store_thm
  ("ADDITIVE_INCREASING",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ additive m ==>
       increasing m``,
   RW_TAC std_ss [increasing_def, positive_def]
   ++ Suff
      `?u. u IN measurable_sets m /\ (measure m t = measure m s + measure m u)`
   >> (RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!s. P s` (MP_TAC o Q.SPEC `u`)
       ++ RW_TAC std_ss []
       ++ NTAC 2 (POP_ASSUM MP_TAC)
       ++ REAL_ARITH_TAC)
   ++ Q.EXISTS_TAC `t DIFF s`
   ++ STRONG_CONJ_TAC >> PROVE_TAC [ALGEBRA_DIFF, subsets_def]
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC ADDITIVE
   ++ RW_TAC std_ss [DISJOINT_DEF, IN_DIFF, IN_UNION, EXTENSION, IN_INTER,
                     NOT_IN_EMPTY]
   ++ PROVE_TAC [SUBSET_DEF]);

val COUNTABLY_ADDITIVE_ADDITIVE = store_thm
  ("COUNTABLY_ADDITIVE_ADDITIVE",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ countably_additive m ==>
       additive m``,
   RW_TAC std_ss [additive_def, positive_def, countably_additive_def]
   ++ Q.PAT_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n : num. if n = 0 then s else if n = 1 then t else {}`)
   ++ Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       s UNION t`
   >> (RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_UNION]
       ++ EQ_TAC >> PROVE_TAC [NOT_IN_EMPTY]
       ++ Know `~(1 = (0:num))` >> DECIDE_TAC
       ++ RW_TAC std_ss [] >> PROVE_TAC []
       ++ Q.EXISTS_TAC `t`
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `1`
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   ++ Suff
      `measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))) sums
       (measure m s + measure m t) /\
       measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))) sums
       measure m (s UNION t)`
   >> PROVE_TAC [SUM_UNIQ]
   ++ CONJ_TAC
   >> (Know
       `measure m s + measure m t =
        sum (0, 2)
        (measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))))`
       >> (ASM_SIMP_TAC bool_ss [TWO, ONE, sum]
           ++ RW_TAC std_ss []
           ++ RW_TAC arith_ss [REAL_ADD_LID, o_THM])
       ++ DISCH_THEN (REWRITE_TAC o wrap)
       ++ MATCH_MP_TAC SER_0
       ++ RW_TAC arith_ss [o_THM])
   ++ POP_ASSUM MATCH_MP_TAC
   ++ CONJ_TAC >> PROVE_TAC [ALGEBRA_EMPTY, space_def, subsets_def]
   ++ RW_TAC std_ss [DISJOINT_EMPTY]
   ++ PROVE_TAC [DISJOINT_SYM, ALGEBRA_UNION, subsets_def]);

val COUNTABLY_ADDITIVE = store_thm
  ("COUNTABLY_ADDITIVE",
   ``!m s f.
       countably_additive m /\ f IN (UNIV -> measurable_sets m)
       /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (s = BIGUNION (IMAGE f UNIV)) /\ s IN measurable_sets m ==>
       measure m o f sums measure m s``,
   RW_TAC std_ss []
   ++ PROVE_TAC [countably_additive_def]);

val INF_MEASURE_AGREES = store_thm
  ("INF_MEASURE_AGREES",
   ``!m s.
       algebra (m_space m, measurable_sets m) /\ positive m /\ countably_additive m /\
       s IN measurable_sets m ==>
       (inf_measure m s = measure m s)``,
   RW_TAC std_ss [inf_measure_def]
   ++ ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   ++ CONJ_TAC
   >> (MATCH_MP_TAC INF_LE
       ++ CONJ_TAC
       >> (Q.EXISTS_TAC `0`
           ++ METIS_TAC [INF_MEASURE_POS0])
       ++ Q.EXISTS_TAC `measure m s`
       ++ REVERSE CONJ_TAC >> RW_TAC std_ss [REAL_LE_REFL]
       ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
       ++ RW_TAC std_ss [SUBSET_REFL])
   ++ MATCH_MP_TAC LE_INF
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `measure m s`
       ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
       ++ RW_TAC std_ss [SUBSET_REFL])
   ++ RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, IN_FUNSET, IN_UNIV,
                     IN_BIGUNION, IN_IMAGE, SUMS_EQ]
   ++ MP_TAC (Q.SPECL [`m`] countably_additive_def)
   ++ RW_TAC std_ss []
   ++ POP_ASSUM (MP_TAC o Q.SPEC `(\g. g INTER s) o f`)
   ++ Know `BIGUNION (IMAGE ((\g. g INTER s) o f) UNIV) = s`
   >> (RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_INTER, o_THM]
       ++ EQ_TAC >> PROVE_TAC []
       ++ RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
       ++ RW_TAC std_ss [IN_UNIV]
       ++ Q.EXISTS_TAC `s INTER f x'`
       ++ RW_TAC std_ss [IN_INTER]
       ++ PROVE_TAC [EXTENSION])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ RW_TAC std_ss [o_THM, IN_FUNSET, IN_UNIV, IN_INTER]
   ++ Suff `measure m o (\g. g INTER s) o f sums measure m s`
   >> (RW_TAC std_ss [SUMS_EQ]
       ++ POP_ASSUM (REWRITE_TAC o wrap o GSYM)
       ++ MATCH_MP_TAC SER_LE
       ++ RW_TAC std_ss [o_THM]
       ++ MATCH_MP_TAC INCREASING
       ++ RW_TAC std_ss [ALGEBRA_INTER, INTER_SUBSET]
       >> (MATCH_MP_TAC ADDITIVE_INCREASING
           ++ RW_TAC std_ss []
           ++ MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
           ++ RW_TAC std_ss [])
       ++ PROVE_TAC [ALGEBRA_INTER, subsets_def])
   ++ POP_ASSUM MATCH_MP_TAC
   ++ CONJ_TAC >> PROVE_TAC [ALGEBRA_INTER, subsets_def]
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m'`, `n`])
   ++ RW_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, EXTENSION]
   ++ PROVE_TAC []);

val MEASURE_DOWN = store_thm
  ("MEASURE_DOWN",
   ``!m0 m1.
       sigma_algebra (m_space m0,measurable_sets m0) /\
       measurable_sets m0 SUBSET measurable_sets m1 /\
       (measure m0 = measure m1) /\ measure_space m1 ==>
       measure_space m0``,
   RW_TAC std_ss [measure_space_def, positive_def, SUBSET_DEF,
                  countably_additive_def, IN_FUNSET, IN_UNIV]);

val SIGMA_ALGEBRA_SIGMA = store_thm
  ("SIGMA_ALGEBRA_SIGMA",
   ``!sp sts. subset_class sp sts ==> sigma_algebra (sigma sp sts)``,
   SIMP_TAC std_ss [subset_class_def]
   ++ NTAC 3 STRIP_TAC
   ++ RW_TAC std_ss [sigma_def, sigma_algebra_def, algebra_def,
                     subsets_def, space_def, IN_BIGINTER,
                     GSPECIFICATION, subset_class_def]
   >> (POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [IN_POW, DIFF_SUBSET, UNION_SUBSET, EMPTY_SUBSET] o
       Q.ISPEC `POW (sp :'a -> bool)`)
       ++ RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_BIGUNION]
       ++ PROVE_TAC [])
   ++ POP_ASSUM (fn th => MATCH_MP_TAC th ++ ASSUME_TAC th)
   ++ RW_TAC std_ss [SUBSET_DEF]
   ++ Q.PAT_ASSUM `c SUBSET PP` MP_TAC
   ++ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [SUBSET_DEF]))
   ++ DISCH_THEN (MP_TAC o Q.SPEC `x`)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN MATCH_MP_TAC
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [SUBSET_DEF]);

val POW_ALGEBRA = store_thm
  ("POW_ALGEBRA",
   ``algebra (sp, POW sp)``,
   RW_TAC std_ss [algebra_def, IN_POW, space_def, subsets_def, subset_class_def,
		  EMPTY_SUBSET, DIFF_SUBSET, UNION_SUBSET]);

val POW_SIGMA_ALGEBRA = store_thm
  ("POW_SIGMA_ALGEBRA",
   ``sigma_algebra (sp, POW sp)``,
   RW_TAC std_ss [sigma_algebra_def, IN_POW, space_def, subsets_def,
		  POW_ALGEBRA, SUBSET_DEF, IN_BIGUNION]
   ++ PROVE_TAC []);

val UNIV_SIGMA_ALGEBRA = store_thm
  ("UNIV_SIGMA_ALGEBRA",
   ``sigma_algebra ((UNIV :'a -> bool),(UNIV :('a -> bool) -> bool))``,
    Know `(UNIV :('a -> bool) -> bool) = POW (UNIV :'a -> bool)`
    >> RW_TAC std_ss [EXTENSION, IN_POW, IN_UNIV, SUBSET_UNIV]
    ++ RW_TAC std_ss [POW_SIGMA_ALGEBRA]);

val INF_MEASURE_EMPTY = store_thm
  ("INF_MEASURE_EMPTY",
   ``!m. algebra (m_space m, measurable_sets m) /\ positive m ==> (inf_measure m {} = 0)``,
   RW_TAC std_ss []
   ++ ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   ++ REVERSE CONJ_TAC >> PROVE_TAC [INF_MEASURE_POS, EMPTY_SUBSET]
   ++ RW_TAC std_ss [inf_measure_def]
   ++ MATCH_MP_TAC INF_LE
   ++ CONJ_TAC >> METIS_TAC [INF_MEASURE_POS0, EMPTY_SUBSET]
   ++ Q.EXISTS_TAC `0`
   ++ RW_TAC std_ss [GSPECIFICATION, REAL_LE_REFL]
   ++ Q.EXISTS_TAC `K {}`
   ++ RW_TAC bool_ss [IN_FUNSET, IN_UNIV, ALGEBRA_EMPTY, DISJOINT_EMPTY, K_THM,
                      SUBSET_DEF, NOT_IN_EMPTY, IN_BIGUNION, IN_IMAGE]
   >> PROVE_TAC [subsets_def, space_def, ALGEBRA_EMPTY]
   ++ Know `0 = sum (0, 0) (measure m o K {})` >> RW_TAC std_ss [sum]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ MATCH_MP_TAC SER_0
   ++ RW_TAC std_ss [K_THM, o_THM]
   ++ PROVE_TAC [positive_def]);

val INF_MEASURE_POSITIVE = store_thm
  ("INF_MEASURE_POSITIVE",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m ==>
       positive (m_space m, POW (m_space m), inf_measure m)``,
   RW_TAC std_ss [positive_def, INF_MEASURE_EMPTY, INF_MEASURE_POS,
                  measure_def, measurable_sets_def, IN_POW]);

val INF_MEASURE_INCREASING = store_thm
  ("INF_MEASURE_INCREASING",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m ==>
       increasing (m_space m, POW (m_space m), inf_measure m)``,
   RW_TAC std_ss [increasing_def, inf_measure_def, measurable_sets_def, IN_POW, measure_def]
   ++ MATCH_MP_TAC LE_INF
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `measure m (m_space m)`
       ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [ALGEBRA_SPACE, subsets_def, space_def, m_space_def, measurable_sets_def])
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC INF_LE
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `0`
       ++ METIS_TAC [INF_MEASURE_POS0])
   ++ Q.EXISTS_TAC `x`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [GSPECIFICATION, REAL_LE_REFL]
   ++ PROVE_TAC [SUBSET_TRANS]);

val INF_MEASURE_LE = store_thm
  ("INF_MEASURE_LE",
   ``!m s x.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m /\
       x IN
       {r | ?f.
          f IN (UNIV -> measurable_sets m) /\
          s SUBSET BIGUNION (IMAGE f UNIV) /\
          measure m o f sums r} ==>
       inf_measure m s <= x``,
   RW_TAC std_ss [GSPECIFICATION, SUMS_EQ, IN_FUNSET, IN_UNIV]
   ++ RW_TAC std_ss [inf_measure_def]
   ++ MATCH_MP_TAC INF_LE
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `0`
       ++ METIS_TAC [INF_MEASURE_POS0])
   ++ RW_TAC std_ss [GSPECIFICATION, SUMS_EQ]
   ++ CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV THENC SWAP_EXISTS_CONV)
   ++ Q.EXISTS_TAC `\n. f n DIFF (BIGUNION (IMAGE f (count n)))`
   ++ Q.EXISTS_TAC
      `suminf (measure m o (\n. f n DIFF (BIGUNION (IMAGE f (count n)))))`
   ++ REWRITE_TAC [GSYM CONJ_ASSOC, IN_FUNSET, IN_UNIV]
   ++ BETA_TAC
   ++ STRONG_CONJ_TAC
   >> (STRIP_TAC
       ++ MATCH_MP_TAC ((REWRITE_RULE [space_def, subsets_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_DIFF)
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC ((REWRITE_RULE [space_def, subsets_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_FINITE_UNION)
       ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE]
       ++ PROVE_TAC [IMAGE_FINITE, FINITE_COUNT])
   ++ STRIP_TAC
   ++ Know
      `summable (measure m o (\n. f n DIFF (BIGUNION (IMAGE f (count n))))) /\
       suminf (measure m o (\n. f n DIFF (BIGUNION (IMAGE f (count n))))) <=
       suminf (measure m o f)`
   >> (MATCH_MP_TAC SER_POS_COMPARE
       ++ RW_TAC std_ss [o_THM] >> PROVE_TAC [positive_def]
       ++ MATCH_MP_TAC INCREASING
       ++ PROVE_TAC [DIFF_SUBSET])
   ++ RW_TAC std_ss [] <<
   [RW_TAC arith_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, EXTENSION, IN_DIFF,
                     IN_BIGUNION, IN_IMAGE, IN_COUNT]
    ++ Know `m' < n \/ n < m'` >> DECIDE_TAC
    ++ PROVE_TAC [],
    Q.PAT_ASSUM `s SUBSET g` MP_TAC
    ++ RW_TAC arith_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_UNIV]
    ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
    ++ RW_TAC std_ss []
    ++ Know `?n. x IN f n` >> PROVE_TAC []
    ++ DISCH_THEN (MP_TAC o Ho_Rewrite.REWRITE_RULE [MINIMAL_EXISTS])
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC
       `f (minimal (\n. x IN f n)) DIFF
        BIGUNION (IMAGE f (count (minimal (\n. x IN f n))))`
    ++ REVERSE CONJ_TAC >> PROVE_TAC []
    ++ RW_TAC std_ss [IN_DIFF, IN_BIGUNION, IN_IMAGE, IN_COUNT]
    ++ PROVE_TAC []]);

val INF_MEASURE_CLOSE = store_thm
  ("INF_MEASURE_CLOSE",
   ``!m s e.
       algebra (m_space m, measurable_sets m) /\ positive m /\ 0 < e /\ s SUBSET (m_space m) ==>
       ?f l.
         f IN (UNIV -> measurable_sets m) /\ s SUBSET BIGUNION (IMAGE f UNIV) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
         (measure m o f) sums l /\ l <= inf_measure m s + e``,
   RW_TAC std_ss [inf_measure_def]
   ++ Suff
      `?l.
         l IN {r | ?f.
            f IN (UNIV -> measurable_sets m) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
            s SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r} /\
         l < inf {r | ?f.
            f IN (UNIV -> measurable_sets m) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
            s SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r} + e`
   >> (RW_TAC std_ss [GSPECIFICATION]
       ++ Q.EXISTS_TAC `f`
       ++ Q.EXISTS_TAC `l`
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [REAL_LT_IMP_LE])
   ++ MATCH_MP_TAC INF_CLOSE
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `measure m (m_space m)`
   ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [ALGEBRA_SPACE, m_space_def, measurable_sets_def, subsets_def, space_def]);

val INF_MEASURE_COUNTABLY_SUBADDITIVE = store_thm
  ("INF_MEASURE_COUNTABLY_SUBADDITIVE",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m ==>
       countably_subadditive (m_space m, POW (m_space m), inf_measure m)``,
   RW_TAC std_ss [countably_subadditive_def, IN_FUNSET, IN_UNIV]
   ++ MATCH_MP_TAC REAL_LE_EPSILON
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC REAL_LE_TRANS
   ++ Know
      `!n. ?g l.
         g IN (UNIV -> measurable_sets m) /\
         f n SUBSET BIGUNION (IMAGE g UNIV) /\
         (!m n. ~(m = n) ==> DISJOINT (g m) (g n)) /\
         (measure m o g) sums l /\
         l <= inf_measure m (f n) + e * (1 / 2) pow (n + 1)`
   >> (STRIP_TAC
       ++ MATCH_MP_TAC INF_MEASURE_CLOSE
       ++ PROVE_TAC [REAL_LT_MUL, POW_HALF_POS, measurable_sets_def, IN_POW])
   ++ CONV_TAC (REDEPTH_CONV (CHANGED_CONV SKOLEM_CONV))
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `suminf l`
   ++ Know `!n. 0 <= l n`
   >> (RW_TAC std_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
       ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUMS_EQ]
       ++ Q.PAT_ASSUM `a = b` (REWRITE_TAC o wrap o GSYM)
       ++ MATCH_MP_TAC SUMINF_POS
       ++ RW_TAC std_ss [o_THM]
       ++ PROVE_TAC [positive_def])
   ++ STRIP_TAC
   ++ Know
      `summable l /\
       suminf l <= suminf (\n. inf_measure m (f n)) + e`
   >> (Know `(\n. e * (1 / 2) pow (n + 1)) sums (e * 1)`
       >> (HO_MATCH_MP_TAC SER_CMUL
           ++ RW_TAC std_ss [POW_HALF_SER])
       ++ PURE_REWRITE_TAC [REAL_MUL_RID, SUMS_EQ]
       ++ STRIP_TAC
       ++ POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM)
       ++ Know
          `summable (\n. inf_measure m (f n) + e * (1 / 2) pow (n + 1)) /\
           (suminf (\n. inf_measure m (f n)) +
            suminf (\n. e * (1 / 2) pow (n + 1)) =
            suminf (\n. inf_measure m (f n) + e * (1 / 2) pow (n + 1)))`
       >> (HO_MATCH_MP_TAC SUMINF_ADD
           ++ Q.PAT_ASSUM `summable (a o b)` MP_TAC
           ++ RW_TAC std_ss [o_DEF, measure_def])
       ++ STRIP_TAC
       ++ POP_ASSUM (ONCE_REWRITE_TAC o wrap)
       ++ MATCH_MP_TAC SER_POS_COMPARE
       ++ RW_TAC std_ss [])
   ++ RW_TAC std_ss [o_DEF, measure_def]
   ++ MATCH_MP_TAC INF_MEASURE_LE
   ++ RW_TAC std_ss [GSPECIFICATION]
   ++ MP_TAC NUM_2D_BIJ_INV
   ++ STRIP_TAC
   ++ Q.EXISTS_TAC `UNCURRY g o f'`
   ++ Q.PAT_ASSUM `!n. P n /\ Q n` MP_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, SUBSET_DEF, IN_BIGUNION,
                     IN_IMAGE] <<
   [Cases_on `f' x`
    ++ RW_TAC std_ss [UNCURRY_DEF],
    Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `x'`)
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `!n. P n` K_TAC
    ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC `g x' x''`
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `BIJ a b c` MP_TAC
    ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_CROSS]
    ++ POP_ASSUM (MP_TAC o Q.SPEC `(x', x'')`)
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC `y`
    ++ RW_TAC std_ss [UNCURRY_DEF],
    Know `measure m o UNCURRY g o f' = UNCURRY (\m'. measure m o g m') o f'`
    >> (RW_TAC std_ss [FUN_EQ_THM]
        ++ RW_TAC std_ss [o_DEF]
        ++ Cases_on `f' x`
        ++ RW_TAC std_ss [UNCURRY_DEF])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC SUMINF_2D
    ++ RW_TAC std_ss [o_THM]
    ++ PROVE_TAC [positive_def]]);

val INF_MEASURE_OUTER = store_thm
  ("INF_MEASURE_OUTER",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m ==>
       outer_measure_space (m_space m, POW(m_space m), inf_measure m)``,
   RW_TAC std_ss [outer_measure_space_def, INF_MEASURE_POSITIVE,
                  INF_MEASURE_INCREASING, INF_MEASURE_COUNTABLY_SUBADDITIVE]);

val SIGMA_SUBSET = store_thm
  ("SIGMA_SUBSET",
   ``!a b. sigma_algebra b /\ a SUBSET (subsets b) ==> subsets (sigma (space b) a) SUBSET (subsets b)``,
   RW_TAC std_ss [sigma_def, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION, subsets_def]
   ++ POP_ASSUM (MATCH_MP_TAC o Q.SPEC `subsets b`)
   ++ RW_TAC std_ss [SPACE]);

val ALGEBRA_SUBSET_LAMBDA_SYSTEM = store_thm
  ("ALGEBRA_SUBSET_LAMBDA_SYSTEM",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m /\
       additive m ==>
       measurable_sets m SUBSET lambda_system (m_space m, POW (m_space m)) (inf_measure m)``,
   RW_TAC std_ss [SUBSET_DEF, lambda_system_def, GSPECIFICATION,
                           IN_UNIV, GSYM REAL_LE_ANTISYM, space_def, subsets_def, IN_POW]
   << [FULL_SIMP_TAC std_ss [algebra_def, subset_class_def, m_space_def, measurable_sets_def,
			     space_def, subsets_def, SUBSET_DEF]
       ++ PROVE_TAC [],
       MATCH_MP_TAC REAL_LE_EPSILON
   ++ RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`m`, `s`, `e`] INF_MEASURE_CLOSE)
   ++ Know `s SUBSET m_space m`
   >> PROVE_TAC [SUBSET_DEF, algebra_def, subset_class_def, subsets_def, space_def]
   ++ RW_TAC std_ss [SUMS_EQ, IN_FUNSET, IN_UNIV]
   ++ MATCH_MP_TAC REAL_LE_TRANS
   ++ Q.EXISTS_TAC `suminf (measure m o f)`
   ++ RW_TAC std_ss []
   ++ POP_ASSUM K_TAC
   ++ Know
      `!x.
         x IN measurable_sets m ==>
         summable (measure m o (\s. x INTER s) o f) /\
         inf_measure m (x INTER s) <= suminf (measure m o (\s. x INTER s) o f)`
   >> (NTAC 2 STRIP_TAC
       ++ STRONG_CONJ_TAC
       >> (MATCH_MP_TAC SER_COMPAR
           ++ Q.EXISTS_TAC `measure m o f`
           ++ RW_TAC std_ss [GREATER_EQ]
           ++ Q.EXISTS_TAC `0`
           ++ REVERSE (RW_TAC arith_ss [o_THM, abs])
           >> PROVE_TAC [positive_def, (REWRITE_RULE [subsets_def, space_def] o
	      		 Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_INTER]
           ++ MATCH_MP_TAC INCREASING
           ++ RW_TAC std_ss [INTER_SUBSET, (REWRITE_RULE [subsets_def, space_def] o
	      	     	    		   Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_INTER])
       ++ RW_TAC std_ss [inf_measure_def]
       ++ MATCH_MP_TAC INF_LE
       ++ CONJ_TAC
       >> (Q.EXISTS_TAC `0`
           ++ METIS_TAC [INF_MEASURE_POS0])
       ++ Q.EXISTS_TAC `suminf (measure m o (\s. x' INTER s) o f)`
       ++ RW_TAC std_ss [REAL_LE_REFL, GSPECIFICATION]
       ++ Q.EXISTS_TAC `(\s. x' INTER s) o f`
       ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV,
		(REWRITE_RULE [subsets_def, space_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_INTER, o_THM, SUMS_EQ]
       >> (Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPECL [`m'`, `n`])
           ++ RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
           ++ PROVE_TAC [])
       ++ Q.PAT_ASSUM `s SUBSET ss` MP_TAC
       ++ RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_INTER, IN_IMAGE,
                         IN_UNIV, o_THM]
       ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x''`)
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [IN_INTER])
   ++ DISCH_THEN
      (fn th => MP_TAC (Q.SPEC `x` th) ++ MP_TAC (Q.SPEC `m_space m DIFF x` th))
   ++ RW_TAC std_ss [(REWRITE_RULE [subsets_def, space_def] o
      	     	     Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_COMPL]
   ++ MATCH_MP_TAC REAL_LE_TRANS
   ++ Q.EXISTS_TAC
      `suminf (measure m o (\s. x INTER s) o f) +
       suminf (measure m o (\s. (m_space m DIFF x) INTER s) o f)`
   ++ CONJ_TAC
   >> (Q.PAT_ASSUM `(a:real) <= b` MP_TAC
       ++ Q.PAT_ASSUM `(a:real) <= b` MP_TAC
       ++ REAL_ARITH_TAC)
   ++ RW_TAC std_ss [SUMINF_ADD, o_THM]
   ++ Know `!a b : real. (a = b) ==> a <= b` >> REAL_ARITH_TAC
   ++ DISCH_THEN MATCH_MP_TAC
   ++ AP_TERM_TAC
   ++ RW_TAC std_ss [FUN_EQ_THM]
   ++ RW_TAC std_ss [o_THM]
   ++ MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC ADDITIVE
   ++ RW_TAC std_ss [(REWRITE_RULE [subsets_def, space_def] o
      	     	      Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_INTER,
		     (REWRITE_RULE [subsets_def, space_def] o
		      Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_COMPL,
		     DISJOINT_DEF, IN_INTER, IN_DIFF, NOT_IN_EMPTY, EXTENSION, IN_UNION]
   ++ PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF, space_def, subsets_def],
   Know `inf_measure m = measure (m_space m, POW (m_space m), inf_measure m)`
       >> RW_TAC std_ss [measure_def]
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ MATCH_MP_TAC SUBADDITIVE
       ++ RW_TAC std_ss [IN_UNIV, EXTENSION, IN_INTER, IN_DIFF, IN_UNION, IN_POW,
                         measurable_sets_def, SUBSET_DEF]
       ++ PROVE_TAC [INF_MEASURE_COUNTABLY_SUBADDITIVE,
                     INF_MEASURE_POSITIVE, POW_ALGEBRA,
                     COUNTABLY_SUBADDITIVE_SUBADDITIVE,
                     measurable_sets_def, m_space_def]]);

val CARATHEODORY = store_thm
  ("CARATHEODORY",
   ``!m0.
       algebra (m_space m0, measurable_sets m0) /\ positive m0 /\ countably_additive m0 ==>
       ?m.
         (!s. s IN measurable_sets m0 ==> (measure m s = measure m0 s)) /\
         ((m_space m, measurable_sets m) =
	  sigma (m_space m0) (measurable_sets m0)) /\ measure_space m``,
   RW_TAC std_ss []
   ++ Q.EXISTS_TAC `(space (sigma (m_space m0) (measurable_sets m0)),
      		     subsets (sigma (m_space m0) (measurable_sets m0)),
		     inf_measure m0)`
   ++ CONJ_TAC >> PROVE_TAC [INF_MEASURE_AGREES, measure_def]
   ++ CONJ_TAC >> RW_TAC std_ss [measurable_sets_def, subsets_def, space_def, m_space_def, SPACE]
   ++ MATCH_MP_TAC MEASURE_DOWN
   ++ Q.EXISTS_TAC
      `(m_space m0,
        lambda_system (m_space m0, POW (m_space m0)) (inf_measure m0),
	inf_measure m0)`
   ++ REWRITE_TAC [measurable_sets_def, measure_def, space_def, m_space_def, subsets_def, SPACE]
   ++ STRONG_CONJ_TAC >> FULL_SIMP_TAC std_ss [algebra_def, SIGMA_ALGEBRA_SIGMA,
      		      	 	       	       space_def, subsets_def]
   ++ STRIP_TAC
   ++ ONCE_REWRITE_TAC [CONJ_COMM]
   ++ STRONG_CONJ_TAC
   >> ((MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
       Q.SPEC `(m_space m0,POW (m_space m0))`) CARATHEODORY_LEMMA
       ++ CONJ_TAC >> RW_TAC std_ss [POW_SIGMA_ALGEBRA]
       ++ PROVE_TAC [INF_MEASURE_OUTER, COUNTABLY_ADDITIVE_ADDITIVE,
                     ADDITIVE_INCREASING])
   ++ RW_TAC std_ss []
   ++ (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
	Q.SPECL [`(measurable_sets m0)`, `(m_space m0,
				   	   lambda_system (m_space m0, POW (m_space m0))
					   (inf_measure m0))`]) SIGMA_SUBSET
   ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [measure_space_def, measurable_sets_def, m_space_def]
   ++ PROVE_TAC [ALGEBRA_SUBSET_LAMBDA_SYSTEM, COUNTABLY_ADDITIVE_ADDITIVE,
                 ADDITIVE_INCREASING]);

val SIGMA_SUBSET_SUBSETS = store_thm
  ("SIGMA_SUBSET_SUBSETS",
   ``!sp a. a SUBSET subsets (sigma sp a)``,
   RW_TAC std_ss [sigma_def, IN_BIGINTER, SUBSET_DEF, GSPECIFICATION, subsets_def]);

val IN_SIGMA = store_thm
  ("IN_SIGMA",
   ``!sp a x. x IN a ==> x IN subsets (sigma sp a)``,
   MP_TAC SIGMA_SUBSET_SUBSETS
   ++ RW_TAC std_ss [SUBSET_DEF]);

val SIGMA_ALGEBRA = store_thm
  ("SIGMA_ALGEBRA",
   ``!p.
       sigma_algebra p =
       subset_class (space p) (subsets p) /\
       {} IN subsets p /\ (!s. s IN subsets p ==> (space p DIFF s) IN subsets p) /\
       (!c. countable c /\ c SUBSET subsets p ==> BIGUNION c IN subsets p)``,
   RW_TAC std_ss [sigma_algebra_def, algebra_def]
   ++ EQ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `!c. P c` (MP_TAC o Q.SPEC `{s; t}`)
   ++ RW_TAC std_ss [COUNTABLE_ALT, FINITE_INSERT, FINITE_EMPTY, SUBSET_DEF,
                     BIGUNION_PAIR, IN_INSERT, NOT_IN_EMPTY]
   ++ PROVE_TAC []);

val SIGMA_ALGEBRA_COUNTABLE_UNION = store_thm
  ("SIGMA_ALGEBRA_COUNTABLE_UNION",
   ``!a c. sigma_algebra a /\ countable c /\ c SUBSET subsets a ==> BIGUNION c IN subsets a``,
   PROVE_TAC [sigma_algebra_def]);

val SIGMA_ALGEBRA_ENUM = store_thm
  ("SIGMA_ALGEBRA_ENUM",
   ``!a (f : num -> ('a -> bool)).
       sigma_algebra a /\ f IN (UNIV -> subsets a) ==> BIGUNION (IMAGE f UNIV) IN subsets a``,
   RW_TAC std_ss [SIGMA_ALGEBRA_ALT]);

val MEASURE_COMPL = store_thm
  ("MEASURE_COMPL",
   ``!m s.
       measure_space m /\ s IN measurable_sets m ==>
       (measure m (m_space m DIFF s) = measure m (m_space m) - measure m s)``,
   RW_TAC std_ss []
   ++ Suff `measure m (m_space m) = measure m s + measure m (m_space m DIFF s)`
   >> REAL_ARITH_TAC
   ++ MATCH_MP_TAC ADDITIVE
   ++ Q.PAT_ASSUM `measure_space m` MP_TAC
   ++ RW_TAC std_ss [measure_space_def, sigma_algebra_def, DISJOINT_DEF,
                     EXTENSION, IN_DIFF, IN_UNIV, IN_UNION, IN_INTER,
                     NOT_IN_EMPTY]
   ++ PROVE_TAC [COUNTABLY_ADDITIVE_ADDITIVE, ALGEBRA_COMPL, subsets_def, space_def,
		 algebra_def, subset_class_def, SUBSET_DEF]);

val SIGMA_PROPERTY = store_thm
  ("SIGMA_PROPERTY",
   ``!sp p a.
       subset_class sp p /\ {} IN p /\ a SUBSET p /\
       (!s. s IN (p INTER subsets (sigma sp a)) ==> (sp DIFF s) IN p) /\
       (!c. countable c /\ c SUBSET (p INTER subsets (sigma sp a)) ==>
            BIGUNION c IN p) ==>
       subsets (sigma sp a) SUBSET p``,
   RW_TAC std_ss []
   ++ Suff `subsets (sigma sp a) SUBSET p INTER subsets (sigma sp a)`
   >> SIMP_TAC std_ss [SUBSET_INTER]
   ++ Suff `p INTER subsets (sigma sp a) IN {b | a SUBSET b /\ sigma_algebra (sp,b)}`
   >> (KILL_TAC
       ++ RW_TAC std_ss [sigma_def, GSPECIFICATION, SUBSET_DEF, INTER_DEF, BIGINTER, subsets_def])
   ++ RW_TAC std_ss [GSPECIFICATION]
   >> PROVE_TAC [SUBSET_DEF, IN_INTER, IN_SIGMA]
   ++ Know `subset_class sp a` >> PROVE_TAC [subset_class_def, SUBSET_DEF]
   ++ STRIP_TAC
   ++ Know `sigma_algebra (sigma sp a)` >> PROVE_TAC [subset_class_def, SUBSET_DEF,
      	   		  	    	   	      SIGMA_ALGEBRA_SIGMA]
   ++ STRIP_TAC
   ++ RW_TAC std_ss [SIGMA_ALGEBRA, IN_INTER, space_def, subsets_def, SIGMA_ALGEBRA_ALGEBRA,
      	     	     ALGEBRA_EMPTY]
   << [PROVE_TAC [subset_class_def, IN_INTER, SUBSET_DEF],
       (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
        Q.SPEC `(sp, subsets (sigma sp a))`) ALGEBRA_COMPL
       ++ FULL_SIMP_TAC std_ss [sigma_def, sigma_algebra_def, subsets_def],
       FULL_SIMP_TAC std_ss [sigma_algebra_def]
       ++ Q.PAT_ASSUM `!c. P c ==> BIGUNION c IN subsets (sigma sp a)` MATCH_MP_TAC
       ++ FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]]);

val MEASURE_EMPTY = store_thm
  ("MEASURE_EMPTY",
   ``!m. measure_space m ==> (measure m {} = 0)``,
   RW_TAC std_ss [measure_space_def, positive_def]);

val SIGMA_SUBSET_MEASURABLE_SETS = store_thm
  ("SIGMA_SUBSET_MEASURABLE_SETS",
   ``!a m.
       measure_space m /\ a SUBSET measurable_sets m ==>
       subsets (sigma (m_space m) a) SUBSET measurable_sets m``,
   RW_TAC std_ss [measure_space_def]
   ++ MATCH_MP_TAC SIGMA_PROPERTY
   ++ RW_TAC std_ss [IN_INTER, SUBSET_INTER]
   ++ PROVE_TAC [SIGMA_ALGEBRA, space_def, subsets_def]);

val SIGMA_ALGEBRA_FN = store_thm
  ("SIGMA_ALGEBRA_FN",
   ``!a.
       sigma_algebra a =
       subset_class (space a) (subsets a) /\
       {} IN subsets a /\ (!s. s IN subsets a ==> (space a DIFF s) IN subsets a) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> subsets a) ==> BIGUNION (IMAGE f UNIV) IN subsets a)``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_UNIV, SUBSET_DEF]
   ++ EQ_TAC
   >> (RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!c. P c ==> Q c` MATCH_MP_TAC
       ++ RW_TAC std_ss [COUNTABLE_IMAGE_NUM, IN_IMAGE]
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss [COUNTABLE_ENUM]
   >> RW_TAC std_ss [BIGUNION_EMPTY]
   ++ Q.PAT_ASSUM `!f. (!x. P x f) ==> Q f` MATCH_MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
   ++ PROVE_TAC []);

val SIGMA_ALGEBRA_FN_DISJOINT = store_thm
  ("SIGMA_ALGEBRA_FN_DISJOINT",
   ``!a.
       sigma_algebra a =
       subset_class (space a) (subsets a) /\
       {} IN subsets a /\ (!s. s IN subsets a ==> (space a DIFF s) IN subsets a) /\
       (!s t. s IN subsets a /\ t IN subsets a ==> s UNION t IN subsets a) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> subsets a) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN subsets a)``,
   RW_TAC std_ss [SIGMA_ALGEBRA_ALT_DISJOINT, algebra_def]
   ++ EQ_TAC
   ++ RW_TAC std_ss []);

val SIGMA_PROPERTY_ALT = store_thm
  ("SIGMA_PROPERTY_ALT",
   ``!sp p a.
       subset_class sp p /\
       {} IN p /\ a SUBSET p /\ (!s. s IN (p INTER subsets (sigma sp a)) ==> sp DIFF s IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER subsets (sigma sp a)) ==> BIGUNION (IMAGE f UNIV) IN p) ==>
       subsets (sigma sp a) SUBSET p``,
   RW_TAC std_ss []
   ++ Suff `subsets (sigma sp a) SUBSET p INTER subsets (sigma sp a)`
   >> SIMP_TAC std_ss [SUBSET_INTER]
   ++ Suff `p INTER subsets (sigma sp a) IN {b | a SUBSET b /\ sigma_algebra (sp, b)}`
   >> (KILL_TAC
       ++ RW_TAC std_ss [sigma_def, GSPECIFICATION, SUBSET_DEF, INTER_DEF, BIGINTER, subsets_def])
   ++ RW_TAC std_ss [GSPECIFICATION]
   >> PROVE_TAC [SUBSET_DEF, IN_INTER, IN_SIGMA]
   ++ POP_ASSUM MP_TAC
   ++ Know `sigma_algebra (sigma sp a)` >> PROVE_TAC [subset_class_def, SUBSET_DEF,
      	   		  	    	   	      SIGMA_ALGEBRA_SIGMA]
   ++ STRIP_TAC
   ++ RW_TAC std_ss [SIGMA_ALGEBRA_FN, IN_INTER, FUNSET_INTER, subsets_def, space_def,
      	     	     SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY]
   << [PROVE_TAC [subset_class_def, IN_INTER, SUBSET_DEF],
       (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
        Q.SPEC `(sp, subsets (sigma sp a))`) ALGEBRA_COMPL
       ++ FULL_SIMP_TAC std_ss [sigma_def, sigma_algebra_def, subsets_def],
       FULL_SIMP_TAC std_ss [(Q.SPEC `(sigma sp a)`) SIGMA_ALGEBRA_FN]]);

val SIGMA_PROPERTY_DISJOINT_WEAK = store_thm
  ("SIGMA_PROPERTY_DISJOINT_WEAK",
   ``!sp p a.
       subset_class sp p /\
       {} IN p /\ a SUBSET p /\ (!s. s IN (p INTER subsets (sigma sp a)) ==> (sp DIFF s) IN p) /\
       (!s t. s IN p /\ t IN p ==> s UNION t IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER subsets (sigma sp a)) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       subsets (sigma sp a) SUBSET p``,
   RW_TAC std_ss []
   ++ Suff `subsets (sigma sp a) SUBSET p INTER subsets (sigma sp a)`
   >> SIMP_TAC std_ss [SUBSET_INTER]
   ++ Suff `p INTER subsets (sigma sp a) IN {b | a SUBSET b /\ sigma_algebra (sp, b)}`
   >> (KILL_TAC
       ++ RW_TAC std_ss [sigma_def, GSPECIFICATION, SUBSET_DEF, INTER_DEF, BIGINTER, subsets_def, space_def])
   ++ RW_TAC std_ss [GSPECIFICATION]
   >> PROVE_TAC [SUBSET_DEF, IN_INTER, IN_SIGMA]
   ++ POP_ASSUM MP_TAC
   ++ Know `sigma_algebra (sigma sp a)` >> PROVE_TAC [subset_class_def, SUBSET_DEF,
      	   		  	    	   	      SIGMA_ALGEBRA_SIGMA]
   ++ STRIP_TAC
   ++ RW_TAC std_ss [SIGMA_ALGEBRA_FN_DISJOINT, IN_INTER, FUNSET_INTER, subsets_def, space_def,
      	     	     SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY]
   << [PROVE_TAC [subset_class_def, IN_INTER, SUBSET_DEF],
       (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
        Q.SPEC `(sp, subsets (sigma sp a))`) ALGEBRA_COMPL
       ++ FULL_SIMP_TAC std_ss [sigma_def, sigma_algebra_def, subsets_def],
       (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
        Q.SPEC `(sp, subsets (sigma sp a))`) ALGEBRA_UNION
       ++ FULL_SIMP_TAC std_ss [sigma_def, sigma_algebra_def, subsets_def],
       FULL_SIMP_TAC std_ss [(Q.SPEC `(sigma sp a)`) SIGMA_ALGEBRA_FN_DISJOINT]]);

val SPACE_SMALLEST_CLOSED_CDI = store_thm
  ("SPACE_SMALLEST_CLOSED_CDI",
   ``!a. space (smallest_closed_cdi a) = space a``,
  RW_TAC std_ss [smallest_closed_cdi_def, space_def]);

val SMALLEST_CLOSED_CDI = store_thm
  ("SMALLEST_CLOSED_CDI",
   ``!a. algebra a ==> subsets a SUBSET subsets (smallest_closed_cdi a) /\
   	 	       closed_cdi (smallest_closed_cdi a) /\
	 subset_class (space a) (subsets (smallest_closed_cdi a))``,
   Know `!a. algebra a ==> subsets a SUBSET subsets (smallest_closed_cdi a) /\
   	     	       	   closed_cdi (smallest_closed_cdi a)`
   >> (RW_TAC std_ss [smallest_closed_cdi_def, GSPECIFICATION, SUBSET_DEF, INTER_DEF, BIGINTER,
		       subset_class_def, algebra_def, subsets_def]
        ++ RW_TAC std_ss [closed_cdi_def, GSPECIFICATION, IN_BIGINTER, IN_FUNSET,
                          IN_UNIV, subsets_def, space_def, subset_class_def]
   	++ POP_ASSUM (MP_TAC o Q.SPEC `{x | x SUBSET space a}`)
       	++ RW_TAC std_ss [GSPECIFICATION]
        ++ POP_ASSUM MATCH_MP_TAC
        ++ RW_TAC std_ss [SUBSET_DEF]
        ++ PROVE_TAC [IN_DIFF, IN_BIGUNION, IN_IMAGE, IN_UNIV])
   ++ SIMP_TAC std_ss []
   ++ RW_TAC std_ss [closed_cdi_def, SPACE_SMALLEST_CLOSED_CDI]);

val CLOSED_CDI_DUNION = store_thm
  ("CLOSED_CDI_DUNION",
   ``!p s t.
       {} IN subsets p /\ closed_cdi p /\ s IN subsets p /\ t IN subsets p /\ DISJOINT s t ==>
       s UNION t IN subsets p``,
   RW_TAC std_ss [closed_cdi_def]
   ++ Q.PAT_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n. if n = 0 then s else if n = 1 then t else {}`)
   ++ Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        (count 2))`
   >> (MATCH_MP_TAC BIGUNION_IMAGE_UNIV
       ++ RW_TAC arith_ss [])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ RW_TAC bool_ss [COUNT_SUC, IMAGE_INSERT, TWO, ONE, BIGUNION_INSERT,
                      COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
   ++ ONCE_REWRITE_TAC [UNION_COMM]
   ++ POP_ASSUM MATCH_MP_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, DISJOINT_EMPTY]
   ++ PROVE_TAC [DISJOINT_SYM]);

val CLOSED_CDI_COMPL = store_thm
  ("CLOSED_CDI_COMPL",
   ``!p s. closed_cdi p /\ s IN subsets p ==> space p DIFF s IN subsets p``,
   RW_TAC std_ss [closed_cdi_def]);

val CLOSED_CDI_DISJOINT = store_thm
  ("CLOSED_CDI_DISJOINT",
   ``!p f.
       closed_cdi p /\ f IN (UNIV -> subsets p) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       BIGUNION (IMAGE f UNIV) IN subsets p``,
   RW_TAC std_ss [closed_cdi_def]);

val CLOSED_CDI_INCREASING = store_thm
  ("CLOSED_CDI_INCREASING",
   ``!p f.
       closed_cdi p /\ f IN (UNIV -> subsets p) /\ (f 0 = {}) /\
       (!n. f n SUBSET f (SUC n)) ==>
       BIGUNION (IMAGE f UNIV) IN subsets p``,
   RW_TAC std_ss [closed_cdi_def]);

val SIGMA_PROPERTY_DISJOINT_LEMMA1 = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA1",
   ``!a.
       algebra a ==>
       (!s t.
          s IN subsets a /\ t IN subsets (smallest_closed_cdi a) ==>
          s INTER t IN subsets (smallest_closed_cdi a))``,
   RW_TAC std_ss [IN_BIGINTER, GSPECIFICATION, smallest_closed_cdi_def, subsets_def]
   ++ Suff
      `t IN
       {b | b IN subsets (smallest_closed_cdi a) /\ s INTER b IN subsets (smallest_closed_cdi a)}`
   >> RW_TAC std_ss [GSPECIFICATION, IN_BIGINTER, smallest_closed_cdi_def, subsets_def]
   ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
   ++ STRONG_CONJ_TAC
   >> (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_BIGINTER,
                      smallest_closed_cdi_def, subsets_def]
       ++ PROVE_TAC [ALGEBRA_INTER])
   ++ RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, closed_cdi_def, space_def, subsets_def] <<
   [(MP_TAC o UNDISCH o Q.SPEC `a`) SMALLEST_CLOSED_CDI
    ++ RW_TAC std_ss [subset_class_def, SUBSET_DEF, GSPECIFICATION]
    ++ PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF],
    PROVE_TAC [closed_cdi_def, SMALLEST_CLOSED_CDI, SPACE_SMALLEST_CLOSED_CDI],
    Know `s INTER (space a DIFF s') =
    	  space (smallest_closed_cdi a) DIFF
	  	(space (smallest_closed_cdi a) DIFF s UNION (s INTER s'))`
    >> (RW_TAC std_ss [EXTENSION, INTER_DEF, COMPL_DEF, UNION_DEF, GSPECIFICATION, IN_UNIV,
       	       	       IN_DIFF]
        ++ PROVE_TAC [SPACE_SMALLEST_CLOSED_CDI])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_COMPL
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    ++ MATCH_MP_TAC CLOSED_CDI_DUNION
    ++ CONJ_TAC
    >> PROVE_TAC [ALGEBRA_EMPTY, SMALLEST_CLOSED_CDI, SUBSET_DEF]
    ++ CONJ_TAC >> RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC CLOSED_CDI_COMPL
        ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI])
    ++ CONJ_TAC >> PROVE_TAC [SMALLEST_CLOSED_CDI, SUBSET_DEF]
    ++ RW_TAC std_ss [DISJOINT_DEF, COMPL_DEF, INTER_DEF, IN_DIFF, IN_UNIV, GSPECIFICATION,
       	      	      EXTENSION, NOT_IN_EMPTY]
    ++ DECIDE_TAC,
    Q.PAT_ASSUM `f IN x` MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ MATCH_MP_TAC CLOSED_CDI_INCREASING
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF],
    Know
    `s INTER BIGUNION (IMAGE f UNIV) =
     BIGUNION (IMAGE (\m. case m of 0 => {} | SUC n => s INTER f n) UNIV)`
    >> (KILL_TAC
        ++ RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
	   	  	  IN_INTER]
        ++ (EQ_TAC ++ RW_TAC std_ss [NOT_IN_EMPTY]) <<
        [Q.EXISTS_TAC `s INTER f x'`
         ++ RW_TAC std_ss [IN_INTER]
         ++ Q.EXISTS_TAC `SUC x'`
         ++ RW_TAC arith_ss [IN_INTER, num_case_def],
         POP_ASSUM (MP_TAC)
         ++ Cases_on `m` >> RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         ++ RW_TAC arith_ss [num_case_def, IN_INTER],
         POP_ASSUM (MP_TAC)
         ++ Cases_on `m` >> RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         ++ RW_TAC arith_ss [num_case_def, IN_INTER]
         ++ Q.EXISTS_TAC `f n`
         ++ RW_TAC std_ss []
         ++ PROVE_TAC []])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_INCREASING
    ++ Q.PAT_ASSUM `f IN X` MP_TAC
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> (REVERSE (Cases_on `m`) >> RW_TAC arith_ss []
        ++ RW_TAC arith_ss []
        ++ PROVE_TAC [SMALLEST_CLOSED_CDI, ALGEBRA_EMPTY, SUBSET_DEF])
    ++ Cases_on `n` >> RW_TAC arith_ss [num_case_def, EMPTY_SUBSET]
    ++ RW_TAC arith_ss [num_case_def, SUBSET_DEF, IN_INTER],
    Q.PAT_ASSUM `f IN x` MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ MATCH_MP_TAC CLOSED_CDI_DISJOINT
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF],
    Know
    `s INTER BIGUNION (IMAGE f UNIV) =
     BIGUNION (IMAGE (\n. s INTER f n) UNIV)`
    >> (KILL_TAC
        ++ RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
	   	  	  IN_INTER]
        ++ (EQ_TAC ++ RW_TAC std_ss []) <<
        [Q.EXISTS_TAC `s INTER f x'`
         ++ RW_TAC std_ss [IN_INTER]
         ++ Q.EXISTS_TAC `x'`
         ++ RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC)
         ++ RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC)
         ++ RW_TAC arith_ss [IN_INTER]
         ++ Q.EXISTS_TAC `f n`
         ++ RW_TAC std_ss []
         ++ PROVE_TAC []])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_DISJOINT
    ++ Q.PAT_ASSUM `f IN X` MP_TAC
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ Q.PAT_ASSUM `!m n. PP m n` (MP_TAC o Q.SPECL [`m`, `n`])
    ++ RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
    ++ PROVE_TAC []]);

val SIGMA_PROPERTY_DISJOINT_LEMMA2 = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA2",
   ``!a.
       algebra a ==>
       (!s t.
          s IN subsets (smallest_closed_cdi a) /\ t IN subsets (smallest_closed_cdi a) ==>
          s INTER t IN subsets (smallest_closed_cdi a))``,
   RW_TAC std_ss []
   ++ POP_ASSUM MP_TAC
   ++ SIMP_TAC std_ss [smallest_closed_cdi_def, IN_BIGINTER, GSPECIFICATION, subsets_def]
   ++ STRIP_TAC ++ Q.X_GEN_TAC `P`
   ++ Suff
      `t IN
       {b | b IN subsets (smallest_closed_cdi a) /\ s INTER b IN subsets (smallest_closed_cdi a)}`
   >> RW_TAC std_ss [GSPECIFICATION, IN_BIGINTER, smallest_closed_cdi_def, subsets_def]
   ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
   ++ STRONG_CONJ_TAC
   >> (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] <<
       [PROVE_TAC [SMALLEST_CLOSED_CDI, SUBSET_DEF],
        PROVE_TAC [SIGMA_PROPERTY_DISJOINT_LEMMA1, INTER_COMM]])
   ++ SIMP_TAC std_ss [GSPECIFICATION, SUBSET_DEF, closed_cdi_def, space_def, subsets_def]
   ++ STRIP_TAC ++ REPEAT CONJ_TAC <<
   [(MP_TAC o UNDISCH o Q.SPEC `a`) SMALLEST_CLOSED_CDI
    ++ RW_TAC std_ss [subset_class_def, SUBSET_DEF, GSPECIFICATION]
    ++ PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF],
    Q.X_GEN_TAC `s'`
    ++ REPEAT STRIP_TAC
    >> PROVE_TAC [closed_cdi_def, SMALLEST_CLOSED_CDI,
                  SPACE_SMALLEST_CLOSED_CDI]
    ++ Know `s INTER (space a DIFF s') =
             space (smallest_closed_cdi a) DIFF
             (space (smallest_closed_cdi a) DIFF s UNION (s INTER s'))`
    >> (RW_TAC std_ss [EXTENSION, INTER_DEF, COMPL_DEF, UNION_DEF, GSPECIFICATION, IN_UNIV,
       	       	       IN_DIFF, SPACE_SMALLEST_CLOSED_CDI]
        ++ DECIDE_TAC)
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_COMPL
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    ++ MATCH_MP_TAC CLOSED_CDI_DUNION
    ++ CONJ_TAC
    >> PROVE_TAC [ALGEBRA_EMPTY, SMALLEST_CLOSED_CDI, SUBSET_DEF]
    ++ CONJ_TAC >> RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC CLOSED_CDI_COMPL
        ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI])
    ++ CONJ_TAC >> PROVE_TAC [SMALLEST_CLOSED_CDI, SUBSET_DEF]
    ++ RW_TAC std_ss [DISJOINT_DEF, COMPL_DEF, INTER_DEF, IN_DIFF, IN_UNIV, GSPECIFICATION,
       	      	      EXTENSION, NOT_IN_EMPTY]
    ++ DECIDE_TAC,
    Q.X_GEN_TAC `f` ++ REPEAT STRIP_TAC
    >> (Q.PAT_ASSUM `f IN x` MP_TAC
        ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
        ++ MATCH_MP_TAC CLOSED_CDI_INCREASING
        ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF])
    ++ Know
         `s INTER BIGUNION (IMAGE f UNIV) =
          BIGUNION (IMAGE (\m. case m of 0 => {} | SUC n => s INTER f n) UNIV)`
    >> (KILL_TAC
        ++ RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
	   	  	  IN_INTER]
        ++ (EQ_TAC ++ RW_TAC std_ss [NOT_IN_EMPTY]) <<
        [Q.EXISTS_TAC `s INTER f x'`
         ++ RW_TAC std_ss [IN_INTER]
         ++ Q.EXISTS_TAC `SUC x'`
         ++ RW_TAC arith_ss [IN_INTER, num_case_def],
         POP_ASSUM (MP_TAC)
         ++ Cases_on `m` >> RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         ++ RW_TAC arith_ss [num_case_def, IN_INTER],
         POP_ASSUM (MP_TAC)
         ++ Cases_on `m` >> RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         ++ RW_TAC arith_ss [num_case_def, IN_INTER]
         ++ Q.EXISTS_TAC `f n`
         ++ RW_TAC std_ss []
         ++ PROVE_TAC []])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_INCREASING
    ++ Q.PAT_ASSUM `f IN X` MP_TAC
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> (REVERSE (Cases_on `m`) >> RW_TAC arith_ss []
        ++ RW_TAC arith_ss []
        ++ PROVE_TAC [SMALLEST_CLOSED_CDI, ALGEBRA_EMPTY, SUBSET_DEF])
    ++ Cases_on `n` >> RW_TAC arith_ss [num_case_def, EMPTY_SUBSET]
    ++ RW_TAC arith_ss [num_case_def, SUBSET_DEF, IN_INTER],
    Q.X_GEN_TAC `f` ++ REPEAT STRIP_TAC
    >> (Q.PAT_ASSUM `f IN x` MP_TAC
        ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
        ++ MATCH_MP_TAC CLOSED_CDI_DISJOINT
        ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF])
    ++ Know
        `s INTER BIGUNION (IMAGE f UNIV) =
         BIGUNION (IMAGE (\n. s INTER f n) UNIV)`
    >> (KILL_TAC
        ++ RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
	   	  	  IN_INTER]
        ++ (EQ_TAC ++ RW_TAC std_ss []) <<
        [Q.EXISTS_TAC `s INTER f x'`
         ++ RW_TAC std_ss [IN_INTER]
         ++ Q.EXISTS_TAC `x'`
         ++ RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC)
         ++ RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC)
         ++ RW_TAC arith_ss [IN_INTER]
         ++ Q.EXISTS_TAC `f n`
         ++ RW_TAC std_ss []
         ++ PROVE_TAC []])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_DISJOINT
    ++ Q.PAT_ASSUM `f IN X` MP_TAC
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ Q.PAT_ASSUM `!m n. PP m n` (MP_TAC o Q.SPECL [`m`, `n`])
    ++ RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
    ++ PROVE_TAC []]);

val SIGMA_PROPERTY_DISJOINT_LEMMA = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA",
   ``!sp a p. algebra (sp, a) /\ a SUBSET p /\ closed_cdi (sp, p)
   	 ==> subsets (sigma sp a) SUBSET p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC SUBSET_TRANS
   ++ Q.EXISTS_TAC `subsets (smallest_closed_cdi (sp, a))`
   ++ REVERSE CONJ_TAC
   >> (RW_TAC std_ss [SUBSET_DEF, smallest_closed_cdi_def, IN_BIGINTER,
                      GSPECIFICATION, subsets_def, space_def]
       ++ PROVE_TAC [SUBSET_DEF])
   ++ NTAC 2 (POP_ASSUM K_TAC)
   ++ Suff `subsets (smallest_closed_cdi (sp, a)) IN {b | a SUBSET b /\ sigma_algebra (sp,b)}`
   >> (KILL_TAC
       ++ RW_TAC std_ss [sigma_def, BIGINTER, SUBSET_DEF, GSPECIFICATION,subsets_def])
   ++ RW_TAC std_ss [GSPECIFICATION, SIGMA_ALGEBRA_ALT_DISJOINT,
                     ALGEBRA_ALT_INTER, space_def, subsets_def] <<
   [PROVE_TAC [SMALLEST_CLOSED_CDI, subsets_def],
    PROVE_TAC [SMALLEST_CLOSED_CDI, space_def],
    PROVE_TAC [ALGEBRA_EMPTY, SUBSET_DEF, SMALLEST_CLOSED_CDI, space_def],
    PROVE_TAC [SMALLEST_CLOSED_CDI, CLOSED_CDI_COMPL, space_def, SPACE_SMALLEST_CLOSED_CDI],
    PROVE_TAC [SIGMA_PROPERTY_DISJOINT_LEMMA2],
    PROVE_TAC [SMALLEST_CLOSED_CDI, CLOSED_CDI_DISJOINT]]);

val SIGMA_PROPERTY_DISJOINT_WEAK = store_thm
  ("SIGMA_PROPERTY_DISJOINT_WEAK",
   ``!sp p a.
       algebra (sp, a) /\ a SUBSET p /\
       subset_class sp p /\
       (!s. s IN p ==> sp DIFF s IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       subsets (sigma sp a) SUBSET p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC (Q.SPECL [`sp`, `a`, `p`] SIGMA_PROPERTY_DISJOINT_LEMMA)
   ++ RW_TAC std_ss [closed_cdi_def, space_def, subsets_def]);

val SIGMA_PROPERTY_DISJOINT = store_thm
  ("SIGMA_PROPERTY_DISJOINT",
   ``!sp p a.
       algebra (sp,a) /\ a SUBSET p /\
       (!s. s IN (p INTER subsets (sigma sp a)) ==> sp DIFF s IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER subsets (sigma sp a)) /\ (f 0 = {}) /\
          (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER subsets (sigma sp a)) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       subsets (sigma sp a) SUBSET p``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INTER]
   ++ Suff `subsets (sigma sp a) SUBSET p INTER subsets (sigma sp a)`
   >> (KILL_TAC
       ++ SIMP_TAC std_ss [SUBSET_INTER])
   ++ MATCH_MP_TAC
      (Q.SPECL [`sp`, `p INTER subsets (sigma sp a)`, `a`] SIGMA_PROPERTY_DISJOINT_WEAK)
   ++ RW_TAC std_ss [SUBSET_INTER, IN_INTER, IN_FUNSET, IN_UNIV] <<
   [PROVE_TAC [SUBSET_DEF, IN_SIGMA],
    (MP_TAC o Q.SPECL [`sp`,`a`]) SIGMA_ALGEBRA_SIGMA
    ++ Q.PAT_ASSUM `algebra (sp,a)` MP_TAC
    ++ RW_TAC std_ss [algebra_def, space_def, subsets_def]
    ++ POP_ASSUM MP_TAC
    ++ NTAC 3 (POP_ASSUM (K ALL_TAC))
    ++ RW_TAC std_ss [sigma_algebra_def, algebra_def, space_def, subsets_def]
    ++ NTAC 4 (POP_ASSUM (K ALL_TAC))
    ++ POP_ASSUM MP_TAC
    ++ Know `space (sigma sp a) = sp` >> RW_TAC std_ss [sigma_def, space_def]
    ++ RW_TAC std_ss [subset_class_def, IN_INTER],
    (MP_TAC o Q.SPECL [`sp`,`a`]) SIGMA_ALGEBRA_SIGMA
    ++ Q.PAT_ASSUM `algebra (sp,a)` MP_TAC
    ++ RW_TAC std_ss [algebra_def, space_def, subsets_def]
    ++ POP_ASSUM MP_TAC
    ++ NTAC 3 (POP_ASSUM (K ALL_TAC))
    ++ Know `space (sigma sp a) = sp` >> RW_TAC std_ss [sigma_def, space_def]
    ++ RW_TAC std_ss [SIGMA_ALGEBRA, algebra_def, subsets_def, space_def],
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
    ++ Q.PAT_ASSUM `algebra (sp,a)` MP_TAC
    ++ RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA, COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV, algebra_def, subsets_def, space_def]
    ++ PROVE_TAC [],
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
    ++ Q.PAT_ASSUM `algebra (sp,a)` MP_TAC
    ++ RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA, COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV, algebra_def, subsets_def, space_def]
    ++ PROVE_TAC []]);

val MEASURE_COUNTABLY_ADDITIVE = store_thm
  ("MEASURE_COUNTABLY_ADDITIVE",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       measure m o f sums measure m s``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC COUNTABLY_ADDITIVE
   ++ RW_TAC std_ss []
   >> PROVE_TAC [measure_space_def]
   ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
	 Q.SPEC `(m_space m, measurable_sets m)`) SIGMA_ALGEBRA_COUNTABLE_UNION
   ++ CONJ_TAC >> PROVE_TAC [measure_space_def]
   ++ Q.PAT_ASSUM `f IN P` MP_TAC
   ++ RW_TAC std_ss [COUNTABLE_IMAGE_NUM, SUBSET_DEF, IN_IMAGE, IN_UNIV,
                     IN_FUNSET]
   ++ PROVE_TAC []);

val MEASURE_SPACE_ADDITIVE = store_thm
  ("MEASURE_SPACE_ADDITIVE",
   ``!m. measure_space m ==> additive m``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
   ++ PROVE_TAC [measure_space_def, SIGMA_ALGEBRA_ALGEBRA]);

val MEASURE_ADDITIVE = store_thm
  ("MEASURE_ADDITIVE",
   ``!m s t u.
       measure_space m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       DISJOINT s t /\ (u = s UNION t) ==>
       (measure m u = measure m s + measure m t)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC ADDITIVE
   ++ RW_TAC std_ss [MEASURE_SPACE_ADDITIVE]);

val MEASURE_COUNTABLE_INCREASING = store_thm
  ("MEASURE_COUNTABLE_INCREASING",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       measure m o f --> measure m s``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   ++ Know
      `measure m o f = (\n. sum (0, n) (measure m o (\m. f (SUC m) DIFF f m)))`
   >> (RW_TAC std_ss [FUN_EQ_THM]
       ++ Induct_on `n` >> RW_TAC std_ss [o_THM, sum, MEASURE_EMPTY]
       ++ POP_ASSUM (MP_TAC o SYM)
       ++ RW_TAC arith_ss [o_THM, sum]
       ++ MATCH_MP_TAC MEASURE_ADDITIVE
       ++ FULL_SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF, DISJOINT_DEF, NOT_IN_EMPTY,
       	  		        IN_INTER, SUBSET_DEF]
       ++ Know `algebra (m_space m, measurable_sets m)`
       >> FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
       	  		       	space_def, subsets_def]
       ++ STRIP_TAC
       ++ (MP_TAC o REWRITE_RULE [subsets_def, space_def] o
           Q.SPEC `(m_space m, measurable_sets m)`) ALGEBRA_DIFF
       ++ PROVE_TAC [])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ RW_TAC std_ss [GSYM sums]
   ++ MATCH_MP_TAC COUNTABLY_ADDITIVE
   ++ CONJ_TAC >> PROVE_TAC [measure_space_def]
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_FUNSET, IN_UNIV]
       ++ Know `algebra (m_space m, measurable_sets m)`
       >> FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
       	  		        space_def, subsets_def]
       ++ STRIP_TAC
       ++ (MP_TAC o REWRITE_RULE [subsets_def, space_def] o
       	   Q.SPEC `(m_space m, measurable_sets m)`) ALGEBRA_DIFF
       ++ PROVE_TAC [])
   ++ CONJ_TAC
   >> (REPEAT STRIP_TAC
       ++ MATCH_MP_TAC DISJOINT_DIFFS
       ++ Q.EXISTS_TAC `f`
       ++ RW_TAC std_ss [])
   ++ CONJ_TAC
   >> (FULL_SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF, DISJOINT_DEF, NOT_IN_EMPTY, IN_INTER,
			     SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_UNIV, DIFF_DEF]
       ++ STRIP_TAC
       ++ REVERSE (EQ_TAC ++ RW_TAC std_ss [])
       >> PROVE_TAC []
       ++ Know `x IN f x'` >> PROVE_TAC []
       ++ NTAC 2 (POP_ASSUM K_TAC)
       ++ Induct_on `x'` >> RW_TAC std_ss []
       ++ POP_ASSUM MP_TAC
       ++ Cases_on `x IN f x'` >> RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `f (SUC x') DIFF f x'`
       ++ RW_TAC std_ss [EXTENSION, DIFF_DEF, GSPECIFICATION]
       ++ PROVE_TAC [])
   ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
	Q.SPEC `(m_space m, measurable_sets m)`) SIGMA_ALGEBRA_COUNTABLE_UNION
   ++ CONJ_TAC >> PROVE_TAC [measure_space_def]
   ++ RW_TAC std_ss [COUNTABLE_IMAGE_NUM]
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV]
   ++ PROVE_TAC []);

val MEASURE_SPACE_REDUCE = store_thm
  ("MEASURE_SPACE_REDUCE",
   ``!m. (m_space m, measurable_sets m, measure m) = m``,
   Cases
   ++ Q.SPEC_TAC (`r`, `r`)
   ++ Cases
   ++ RW_TAC std_ss [m_space_def, measurable_sets_def, measure_def]);

val SPACE_SIGMA = store_thm
  ("SPACE_SIGMA",
   ``!sp a. space (sigma sp a) = sp``,
   RW_TAC std_ss [sigma_def, space_def]);

val MONOTONE_CONVERGENCE = store_thm
  ("MONOTONE_CONVERGENCE",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       measure m o f --> measure m s``,
   RW_TAC std_ss [measure_space_def, IN_FUNSET, IN_UNIV]
   ++ (MP_TAC o
       INST_TYPE [beta |-> ``:num``] o
       Q.SPECL [`m`, `BIGUNION (IMAGE f UNIV)`, `\x. num_CASE x {} f`])
      MEASURE_COUNTABLE_INCREASING
   ++ Cond
   >> (RW_TAC std_ss [IN_FUNSET, IN_UNIV, num_case_def, measure_space_def] <<
       [Cases_on `x` <<
        [RW_TAC std_ss [num_case_def]
         ++ PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY, subsets_def],
         RW_TAC std_ss [num_case_def]],
        Cases_on `n`
        ++ RW_TAC std_ss [num_case_def, EMPTY_SUBSET],
        RW_TAC std_ss [EXTENSION,GSPECIFICATION]
        ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV]
        ++ EQ_TAC <<
        [RW_TAC std_ss []
         ++ Q.EXISTS_TAC `SUC x'`
         ++ RW_TAC std_ss [num_case_def],
         RW_TAC std_ss []
         ++ POP_ASSUM MP_TAC
         ++ Cases_on `x'` >> RW_TAC std_ss [NOT_IN_EMPTY, num_case_def]
         ++ RW_TAC std_ss [num_case_def]
         ++ PROVE_TAC []]])
   ++ RW_TAC std_ss []
   ++ Know `measure m o f = (\n. (measure m o (\x. num_CASE x {} f)) (SUC n))`
   >> (RW_TAC std_ss [FUN_EQ_THM]
       ++ RW_TAC std_ss [num_case_def, o_THM])
   ++ Rewr
   ++ Ho_Rewrite.REWRITE_TAC [GSYM SEQ_SUC]
   ++ RW_TAC std_ss' []);

val SIGMA_REDUCE = store_thm
  ("SIGMA_REDUCE",
   ``!sp a. (sp, subsets (sigma sp a)) = sigma sp a``,
   PROVE_TAC [SPACE_SIGMA, SPACE]);

val MEASURABLE_SETS_SUBSET_SPACE = store_thm
  ("MEASURABLE_SETS_SUBSET_SPACE",
   ``!m s. measure_space m /\ s IN measurable_sets m ==>
		s SUBSET m_space m``,
   RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def, subsets_def, space_def,
   	  	  subset_class_def]);

val MEASURABLE_DIFF_PROPERTY = store_thm
  ("MEASURABLE_DIFF_PROPERTY",
   ``!a b f. sigma_algebra a /\ sigma_algebra b /\
	     f IN (space a -> space b) /\
	     (!s. s IN subsets b ==> PREIMAGE f s IN subsets a) ==>
	(!s. s IN subsets b ==>
		(PREIMAGE f (space b DIFF s) = space a DIFF PREIMAGE f s))``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, subsets_def, space_def, GSPECIFICATION,
		  PREIMAGE_DIFF, IN_IMAGE]
   ++ MATCH_MP_TAC SUBSET_ANTISYM
   ++ RW_TAC std_ss [SUBSET_DEF, IN_DIFF, IN_PREIMAGE]
   ++ Q.PAT_ASSUM `!s. s IN subsets b ==> PREIMAGE f s IN subsets a`
        (MP_TAC o Q.SPEC `space b DIFF s`)
   ++ Know `x IN PREIMAGE f (space b DIFF s)`
   >> RW_TAC std_ss [IN_PREIMAGE, IN_DIFF]
   ++ PROVE_TAC [subset_class_def, SUBSET_DEF]);

val MEASURABLE_BIGUNION_PROPERTY = store_thm
  ("MEASURABLE_BIGUNION_PROPERTY",
   ``!a b f. sigma_algebra a /\ sigma_algebra b /\
	     f IN (space a -> space b) /\
	     (!s. s IN subsets b ==> PREIMAGE f s IN subsets a) ==>
	(!c. c SUBSET subsets b ==>
		(PREIMAGE f (BIGUNION c) = BIGUNION (IMAGE (PREIMAGE f) c)))``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, subsets_def, space_def, GSPECIFICATION,
		  PREIMAGE_BIGUNION, IN_IMAGE]);

val MEASUBABLE_BIGUNION_LEMMA = store_thm
  ("MEASUBABLE_BIGUNION_LEMMA",
   ``!a b f. sigma_algebra a /\ sigma_algebra b /\
	     f IN (space a -> space b) /\
	     (!s. s IN subsets b ==> PREIMAGE f s IN subsets a) ==>
	(!c. countable c /\ c SUBSET (IMAGE (PREIMAGE f) (subsets b)) ==>
		BIGUNION c IN IMAGE (PREIMAGE f) (subsets b))``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_IMAGE]
   ++ Q.EXISTS_TAC `BIGUNION (IMAGE (\x. @x'. x' IN subsets b /\ (PREIMAGE f x' = x)) c)`
   ++ REVERSE CONJ_TAC
   >> (Q.PAT_ASSUM `!c. countable c /\ c SUBSET subsets b ==> BIGUNION c IN subsets b`
           MATCH_MP_TAC
       ++ RW_TAC std_ss [COUNTABLE_IMAGE, SUBSET_DEF, IN_IMAGE]
       ++ Suff `(\x''. x'' IN subsets b) (@x''. x'' IN subsets b /\ (PREIMAGE f x'' = x'))`
       >> RW_TAC std_ss []
       ++ MATCH_MP_TAC SELECT_ELIM_THM
       ++ FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE]
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss [PREIMAGE_BIGUNION, IMAGE_IMAGE]
   ++ RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_IMAGE]
   ++ FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE]
   ++ EQ_TAC
   >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `s` ++ ASM_REWRITE_TAC []
       ++ Q.PAT_ASSUM `!x. x IN c ==> ?x'. (x = PREIMAGE f x') /\ x' IN subsets b`
       	     (MP_TAC o Q.SPEC `s`)
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `PREIMAGE f x'` ++ ASM_REWRITE_TAC []
       ++ Suff `(\x''. PREIMAGE f x' = PREIMAGE f x'')
		(@x''. x'' IN subsets b /\ (PREIMAGE f x'' = PREIMAGE f x'))`
       >> METIS_TAC []
       ++ MATCH_MP_TAC SELECT_ELIM_THM
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `x'`
   ++ ASM_REWRITE_TAC []
   ++ Know `(\x''. x IN PREIMAGE f x'' ==> x IN x')
      	   	   (@x''. x'' IN subsets b /\ (PREIMAGE f x'' = x'))`
   >> (MATCH_MP_TAC SELECT_ELIM_THM
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss []);

val MEASURABLE_SIGMA_PREIMAGES = store_thm
  ("MEASURABLE_SIGMA_PREIMAGES",
   ``!a b f. sigma_algebra a /\ sigma_algebra b /\
	     f IN (space a -> space b) /\
	     (!s. s IN subsets b ==> PREIMAGE f s IN subsets a) ==>
	     sigma_algebra (space a, IMAGE (PREIMAGE f) (subsets b))``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, subsets_def, space_def]
   << [FULL_SIMP_TAC std_ss [subset_class_def, GSPECIFICATION, IN_IMAGE]
       ++ PROVE_TAC [],
       RW_TAC std_ss [IN_IMAGE]
       ++ Q.EXISTS_TAC `{}`
       ++ RW_TAC std_ss [PREIMAGE_EMPTY],
       RW_TAC std_ss [IN_IMAGE, PREIMAGE_DIFF]
       ++ FULL_SIMP_TAC std_ss [IN_IMAGE]
       ++ Q.EXISTS_TAC `space b DIFF x`
       ++ RW_TAC std_ss [PREIMAGE_DIFF]
       ++ MATCH_MP_TAC SUBSET_ANTISYM
       ++ RW_TAC std_ss [SUBSET_DEF, IN_DIFF, IN_PREIMAGE]
       ++ Q.PAT_ASSUM `!s. s IN subsets b ==> PREIMAGE f s IN subsets a`
       	     (MP_TAC o Q.SPEC `space b DIFF x`)
       ++ Know `x' IN PREIMAGE f (space b DIFF x)`
       >> RW_TAC std_ss [IN_PREIMAGE, IN_DIFF]
       ++ PROVE_TAC [subset_class_def, SUBSET_DEF],
       (MP_TAC o REWRITE_RULE [IN_FUNSET, SIGMA_ALGEBRA] o Q.SPECL [`a`, `b`, `f`])
       	       MEASUBABLE_BIGUNION_LEMMA
       ++ RW_TAC std_ss []]);

val IN_MEASURABLE = store_thm
  ("IN_MEASURABLE",
   ``!a b f. f IN measurable a b =
		sigma_algebra a /\
		sigma_algebra b /\
		f IN (space a -> space b) /\
		(!s. s IN subsets b ==> ((PREIMAGE f s)INTER(space a)) IN subsets a)``,
   RW_TAC std_ss [measurable_def, GSPECIFICATION]);

val MEASURABLE_SIGMA = store_thm
  ("MEASURABLE_SIGMA",
   ``!f a b sp.
       sigma_algebra a /\
       subset_class sp b /\
       f IN (space a -> sp) /\
       (!s. s IN b ==> ((PREIMAGE f s)INTER(space a)) IN subsets a)
        ==>
       f IN measurable a (sigma sp b)``,
   RW_TAC std_ss []
   ++ REWRITE_TAC [IN_MEASURABLE]
   ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [sigma_def, space_def]
   ++ RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA, SPACE_SIGMA, subsets_def, GSPECIFICATION]
   ++ Know `subsets (sigma sp b) SUBSET {x' | ((PREIMAGE f x')INTER(space a)) IN subsets a /\
      	   	    	      	         x' SUBSET sp}`
   >> (MATCH_MP_TAC SIGMA_PROPERTY
       ++ RW_TAC std_ss [subset_class_def, GSPECIFICATION, IN_INTER, EMPTY_SUBSET,
		         PREIMAGE_EMPTY, PREIMAGE_DIFF, SUBSET_INTER, SIGMA_ALGEBRA,
			 DIFF_SUBSET, SUBSET_DEF, NOT_IN_EMPTY, IN_DIFF,
			 PREIMAGE_BIGUNION, IN_BIGUNION]
       << [FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, INTER_EMPTY],
	   PROVE_TAC [subset_class_def, SUBSET_DEF],
	   Know `(PREIMAGE f sp DIFF PREIMAGE f s') INTER space a =
		 (PREIMAGE f sp INTER space a) DIFF (PREIMAGE f s' INTER space a)`
           >> (RW_TAC std_ss [Once EXTENSION, IN_DIFF, IN_INTER, IN_PREIMAGE] ++ DECIDE_TAC)
           ++ RW_TAC std_ss []
	   ++ Know `PREIMAGE f sp INTER space a = space a`
	   >> (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE] ++ METIS_TAC [IN_FUNSET])
	   ++ FULL_SIMP_TAC std_ss [sigma_algebra_def, ALGEBRA_COMPL],
	   FULL_SIMP_TAC std_ss [sigma_algebra_def]
	   ++ `BIGUNION (IMAGE (PREIMAGE f) c) INTER space a =
	       BIGUNION (IMAGE (\x. (PREIMAGE f x) INTER (space a)) c)`
		by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE]
		    ++ FULL_SIMP_TAC std_ss [IN_FUNSET]
	            ++ EQ_TAC
		    >> (RW_TAC std_ss []
		        ++ Q.EXISTS_TAC `PREIMAGE f x' INTER space a`
			++ ASM_REWRITE_TAC [IN_INTER]
			++ Q.EXISTS_TAC `x'` ++ RW_TAC std_ss [])
		    ++ RW_TAC std_ss [] ++ METIS_TAC [IN_INTER, IN_PREIMAGE])
	   ++ RW_TAC std_ss []
           ++ Q.PAT_ASSUM `!c. countable c /\ c SUBSET subsets a ==>
	         BIGUNION c IN subsets a` MATCH_MP_TAC
           ++ RW_TAC std_ss [COUNTABLE_IMAGE, SUBSET_DEF, IN_IMAGE]
	   ++ PROVE_TAC [],
	   PROVE_TAC []])
   ++ RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION]);

val MEASURABLE_SUBSET = store_thm
  ("MEASURABLE_SUBSET",
   ``!a b. measurable a b SUBSET measurable a (sigma (space b) (subsets b))``,
   RW_TAC std_ss [SUBSET_DEF]
   ++ MATCH_MP_TAC MEASURABLE_SIGMA
   ++ FULL_SIMP_TAC std_ss [IN_MEASURABLE, SIGMA_ALGEBRA, space_def, subsets_def]);

val MEASURABLE_LIFT = store_thm
  ("MEASURABLE_LIFT",
   ``!f a b.
       f IN measurable a b ==> f IN measurable a (sigma (space b) (subsets b))``,
   PROVE_TAC [MEASURABLE_SUBSET, SUBSET_DEF]);

val IN_MEASURE_PRESERVING = store_thm
  ("IN_MEASURE_PRESERVING",
   ``!m1 m2 f.
       f IN measure_preserving m1 m2 =
       f IN measurable (m_space m1, measurable_sets m1) (m_space m2, measurable_sets m2) /\
       measure_space m1 /\ measure_space m2 /\
       !s.
         s IN measurable_sets m2 ==>
         (measure m1 ((PREIMAGE f s)INTER(m_space m1)) = measure m2 s)``,
   RW_TAC std_ss [measure_preserving_def, GSPECIFICATION]);

val MEASURE_PRESERVING_LIFT = store_thm
  ("MEASURE_PRESERVING_LIFT",
   ``!m1 m2 a f.
       measure_space m1 /\ measure_space m2 /\
       (measurable_sets m2 = subsets (sigma (m_space m2) a)) /\
       f IN measure_preserving m1 (m_space m2, a, measure m2) ==>
       f IN measure_preserving m1 m2``,
   RW_TAC std_ss []
   ++ REVERSE (Cases_on `algebra (m_space m2, a)`)
   >> FULL_SIMP_TAC std_ss [IN_MEASURE_PRESERVING, IN_MEASURABLE, m_space_def,
      		    	    measurable_sets_def, sigma_algebra_def]
   ++ Suff `f IN measure_preserving m1 (m_space m2, measurable_sets m2, measure m2)`
   >> RW_TAC std_ss [MEASURE_SPACE_REDUCE]
   ++ ASM_REWRITE_TAC []
   ++ Q.PAT_ASSUM `f IN X` MP_TAC
   ++ REWRITE_TAC [IN_MEASURE_PRESERVING, measurable_sets_def, measure_def, m_space_def]
   ++ STRIP_TAC
   ++ STRONG_CONJ_TAC
   >> (Know `(m_space m2,subsets (sigma (m_space m2) a)) = sigma (m_space m2) a`
       >> (Q.ABBREV_TAC `Q = (m_space m2,subsets (sigma (m_space m2) a))`
	   ++ Know `sigma (m_space m2) a = (space (sigma (m_space m2) a),
	      	   	  	            subsets (sigma (m_space m2) a))`
	   >> RW_TAC std_ss [SPACE]
           ++ STRIP_TAC ++ POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
	   ++ Q.UNABBREV_TAC `Q`
	   ++ RW_TAC std_ss [PAIR_EQ, sigma_def, space_def])
       ++ RW_TAC std_ss []
       ++ POP_ASSUM (K ALL_TAC)
       ++ Know `(sigma (m_space m2) a) = sigma (space (m_space m2, a)) (subsets (m_space m2, a))`
       >> RW_TAC std_ss [space_def, subsets_def]
       ++ STRIP_TAC ++ POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       ++ MATCH_MP_TAC MEASURABLE_LIFT
       ++ ASM_REWRITE_TAC [])
   ++ Q.PAT_ASSUM `f IN X` K_TAC
   ++ REWRITE_TAC [IN_MEASURABLE, space_def, subsets_def]
   ++ STRIP_TAC
   ++ ASM_REWRITE_TAC []
   ++ CONJ_TAC
   >> (Q.PAT_ASSUM `measurable_sets m2 = subsets (sigma (m_space m2) a)` (MP_TAC o GSYM)
       ++ RW_TAC std_ss [MEASURE_SPACE_REDUCE])
   ++ Suff `subsets (sigma (m_space m2) a) SUBSET
      	   	 {s | measure m1 ((PREIMAGE f s) INTER (m_space m1)) = measure m2 s}`
   >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
   ++ MATCH_MP_TAC SIGMA_PROPERTY_DISJOINT
   ++ RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, IN_INTER, IN_FUNSET,
                     IN_UNIV, PREIMAGE_COMPL, PREIMAGE_BIGUNION, IMAGE_IMAGE,
                     MEASURE_COMPL] <<
   [Q.PAT_ASSUM `measure m1 (PREIMAGE f s INTER m_space m1) = measure m2 s`
   		(fn thm => ONCE_REWRITE_TAC [GSYM thm])
    ++ Know `m_space m2 IN a` >> PROVE_TAC [ALGEBRA_SPACE, subsets_def, space_def]
    ++ STRIP_TAC
    ++ Q.PAT_ASSUM `!s. s IN a ==> (measure m1 (PREIMAGE f s INTER m_space m1) = measure m2 s)`
	((fn thm => ONCE_REWRITE_TAC [GSYM thm]) o UNDISCH o Q.SPEC `m_space m2`)
    ++ Know `PREIMAGE f (m_space m2) INTER m_space m1 = m_space m1`
    >> (FULL_SIMP_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE, IN_FUNSET] ++ METIS_TAC [])
    ++ RW_TAC std_ss [PREIMAGE_DIFF]
    ++ `((PREIMAGE f (m_space m2) DIFF PREIMAGE f s) INTER m_space m1) =
	((PREIMAGE f (m_space m2) INTER m_space m1) DIFF (PREIMAGE f s INTER m_space m1))`
	by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_DIFF, IN_PREIMAGE] ++ DECIDE_TAC)
    ++ RW_TAC std_ss [MEASURE_COMPL],
    `BIGUNION (IMAGE (PREIMAGE f o f') UNIV) INTER m_space m1 =
     BIGUNION (IMAGE (\x:num. (PREIMAGE f o f') x INTER m_space m1) UNIV)`
	by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV]
	    ++ FULL_SIMP_TAC std_ss [IN_FUNSET]
	    ++ EQ_TAC
	    >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `PREIMAGE f (f' x') INTER m_space m1`
		++ ASM_REWRITE_TAC [IN_INTER] ++ Q.EXISTS_TAC `x'` ++ RW_TAC std_ss [])
	    ++ RW_TAC std_ss [] ++ METIS_TAC [IN_PREIMAGE, IN_INTER])
    ++ POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
    ++ Suff
    `(measure m2 o f') --> measure m2 (BIGUNION (IMAGE f' UNIV)) /\
     (measure m2 o f') -->
     measure m1 (BIGUNION (IMAGE (\x. (PREIMAGE f o f') x INTER m_space m1) UNIV))`
    >> PROVE_TAC [SEQ_UNIQ]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING
        ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF])
    ++ Know `measure m2 o f' = measure m1 o (\x. (PREIMAGE f o f') x INTER m_space m1)`
    >> (RW_TAC std_ss [FUN_EQ_THM]
        ++ RW_TAC std_ss [o_THM])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, PREIMAGE_EMPTY, INTER_EMPTY]
    ++ Suff `PREIMAGE f (f' n) SUBSET PREIMAGE f (f' (SUC n))`
    >> RW_TAC std_ss [SUBSET_DEF, IN_INTER]
    ++ MATCH_MP_TAC PREIMAGE_SUBSET
    ++ RW_TAC std_ss [SUBSET_DEF],
    `BIGUNION (IMAGE (PREIMAGE f o f') UNIV) INTER m_space m1 =
     BIGUNION (IMAGE (\x:num. (PREIMAGE f o f') x INTER m_space m1) UNIV)`
	by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV]
	    ++ FULL_SIMP_TAC std_ss [IN_FUNSET]
	    ++ EQ_TAC
	    >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `PREIMAGE f (f' x') INTER m_space m1`
		++ ASM_REWRITE_TAC [IN_INTER] ++ Q.EXISTS_TAC `x'` ++ RW_TAC std_ss [])
	    ++ RW_TAC std_ss [] ++ METIS_TAC [IN_PREIMAGE, IN_INTER])
    ++ POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
    ++ Suff
    `(measure m2 o f') sums measure m2 (BIGUNION (IMAGE f' UNIV)) /\
     (measure m2 o f') sums
     measure m1 (BIGUNION (IMAGE (\x. (PREIMAGE f o f') x INTER m_space m1) UNIV))`
    >> PROVE_TAC [SUM_UNIQ]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE
        ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV])
    ++ Know `measure m2 o f' = measure m1 o (\x. (PREIMAGE f o f') x INTER m_space m1)`
    >> (RW_TAC std_ss [FUN_EQ_THM]
        ++ RW_TAC std_ss [o_THM])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, IN_DISJOINT, PREIMAGE_DISJOINT, IN_INTER]
    ++ METIS_TAC [IN_DISJOINT, PREIMAGE_DISJOINT]]);

val MEASURE_PRESERVING_SUBSET = store_thm
  ("MEASURE_PRESERVING_SUBSET",
   ``!m1 m2 a.
       measure_space m1 /\ measure_space m2 /\
       (measurable_sets m2 = subsets (sigma (m_space m2) a)) ==>
       measure_preserving m1 (m_space m2, a, measure m2) SUBSET
       measure_preserving m1 m2``,
   RW_TAC std_ss [SUBSET_DEF]
   ++ MATCH_MP_TAC MEASURE_PRESERVING_LIFT
   ++ PROVE_TAC []);

val MEASURABLE_I = store_thm
  ("MEASURABLE_I",
   ``!a. sigma_algebra a ==> I IN measurable a a``,
   RW_TAC std_ss [IN_MEASURABLE, I_THM, PREIMAGE_I, IN_FUNSET, GSPEC_ID, SPACE, SUBSET_REFL]
   ++ Know `s INTER space a = s`
   >> (FULL_SIMP_TAC std_ss [Once EXTENSION, sigma_algebra_def, algebra_def, IN_INTER,
      		     	     subset_class_def, SUBSET_DEF]
       ++ METIS_TAC [])
   ++ RW_TAC std_ss []);

val MEASURABLE_COMP = store_thm
  ("MEASURABLE_COMP",
   ``!f g a b c.
       f IN measurable a b /\ g IN measurable b c ==>
       (g o f) IN measurable a c``,
   RW_TAC std_ss [IN_MEASURABLE, GSYM PREIMAGE_COMP, IN_FUNSET, SIGMA_ALGEBRA, space_def,
   	  	  subsets_def, GSPECIFICATION]
   ++ `PREIMAGE f (PREIMAGE g s) INTER space a =
       PREIMAGE f (PREIMAGE g s INTER space b) INTER space a`
	by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE] ++ METIS_TAC [])
   ++ METIS_TAC []);

val MEASURABLE_COMP_STRONG = store_thm
  ("MEASURABLE_COMP_STRONG",
   ``!f g a b c.
       f IN measurable a b /\
       sigma_algebra c /\
       g IN (space b -> space c) /\
       (!x. x IN (subsets c) ==> PREIMAGE g x INTER (IMAGE f (space a)) IN subsets b) ==>
       (g o f) IN measurable a c``,
   RW_TAC bool_ss [IN_MEASURABLE]
   << [FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET] ++ PROVE_TAC [],
       RW_TAC std_ss [PREIMAGE_ALT]
       ++ ONCE_REWRITE_TAC [o_ASSOC]
       ++ ONCE_REWRITE_TAC [GSYM PREIMAGE_ALT]
       ++ Know `PREIMAGE f (s o g) INTER space a =
       	        PREIMAGE f (s o g INTER (IMAGE f (space a))) INTER space a`
       >> (RW_TAC std_ss [GSYM PREIMAGE_ALT]
           ++ RW_TAC std_ss [Once EXTENSION, IN_PREIMAGE, IN_INTER, IN_IMAGE]
	   ++ EQ_TAC
           ++ RW_TAC std_ss []
           ++ FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_PREIMAGE]
           ++ Q.EXISTS_TAC `x`
           ++ Know `g (f x) IN space c`
           >> (FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subset_class_def, SUBSET_DEF] ++ PROVE_TAC [])
           ++ PROVE_TAC [])
       ++ STRIP_TAC ++ POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       ++ FULL_SIMP_TAC std_ss [PREIMAGE_ALT]]);

val MEASURABLE_COMP_STRONGER = store_thm
  ("MEASURABLE_COMP_STRONGER",
   ``!f g a b c t.
       f IN measurable a b /\
       sigma_algebra c /\
       g IN (space b -> space c) /\
       (IMAGE f (space a)) SUBSET t /\
       (!s. s IN subsets c ==> (PREIMAGE g s INTER t) IN subsets b) ==>
       (g o f) IN measurable a c``,
   RW_TAC bool_ss [IN_MEASURABLE]
   << [FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET] ++ PROVE_TAC [],
       RW_TAC std_ss [PREIMAGE_ALT]
       ++ ONCE_REWRITE_TAC [o_ASSOC]
       ++ ONCE_REWRITE_TAC [GSYM PREIMAGE_ALT]
       ++ Know `(PREIMAGE (f:'a->'b) (((s : 'c -> bool) o (g :'b -> 'c)) INTER
		(t :'b -> bool)) INTER space a = PREIMAGE f (s o g) INTER space a)`
       >> (RW_TAC std_ss [GSYM PREIMAGE_ALT]
	   ++ RW_TAC std_ss [Once EXTENSION, IN_PREIMAGE, IN_INTER, IN_IMAGE]
           ++ EQ_TAC
           ++ RW_TAC std_ss []
            ++ Know `g (f x) IN space c`
           >> (FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subset_class_def, SUBSET_DEF] ++ PROVE_TAC [])
	   ++ STRIP_TAC
           ++ Know `(f x) IN space b`
	   >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_FUNSET]
           ++ STRIP_TAC
           ++ Know `x IN space a`
           >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_PREIMAGE]
           ++ STRIP_TAC
           ++ FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE]
           ++ Q.PAT_ASSUM `!x. (?x'. (x = f x') /\ x' IN space a) ==> x IN t` MATCH_MP_TAC
           ++ Q.EXISTS_TAC `x`
	   ++ ASM_REWRITE_TAC [])
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap o GSYM)
       ++ RW_TAC std_ss [PREIMAGE_ALT]
       ++ RW_TAC std_ss [GSYM PREIMAGE_ALT, GSYM PREIMAGE_COMP]]);

val MEASURABLE_UP_LIFT = store_thm
  ("MEASURABLE_UP_LIFT",
   ``!sp a b c f. f IN measurable (sp, a) c /\
	       sigma_algebra (sp, b) /\ a SUBSET b ==> f IN measurable (sp,b) c``,
   RW_TAC std_ss [IN_MEASURABLE, GSPECIFICATION, SUBSET_DEF, IN_FUNSET, space_def, subsets_def]);

val MEASURABLE_UP_SUBSET = store_thm
  ("MEASURABLE_UP_SUBSET",
   ``!sp a b c. a SUBSET b /\ sigma_algebra (sp, b)
	==> measurable (sp, a) c SUBSET measurable (sp, b) c``,
   RW_TAC std_ss [MEASURABLE_UP_LIFT, SUBSET_DEF]
   ++ MATCH_MP_TAC MEASURABLE_UP_LIFT
   ++ Q.EXISTS_TAC `a`
   ++ ASM_REWRITE_TAC [SUBSET_DEF]);

val MEASURABLE_UP_SIGMA = store_thm
  ("MEASURABLE_UP_SIGMA",
   ``!a b. measurable a b SUBSET measurable (sigma (space a) (subsets a)) b``,
   RW_TAC std_ss [SUBSET_DEF, IN_MEASURABLE, space_def, subsets_def, SPACE_SIGMA]
   >> (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA ++ FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA])
   ++ PROVE_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF]);

val MEASURE_PRESERVING_UP_LIFT = store_thm
  ("MEASURE_PRESERVING_UP_LIFT",
   ``!m1 m2 f.
       measure_space m1 /\
       f IN measure_preserving (m_space m1, a, measure m1) m2 /\
       sigma_algebra (m_space m1, measurable_sets m1) /\
       a SUBSET measurable_sets m1 ==>
       f IN measure_preserving m1 m2``,
   RW_TAC std_ss [measure_preserving_def, GSPECIFICATION, SUBSET_DEF,
                  measure_def, measurable_sets_def, m_space_def, SPACE]
   ++ MATCH_MP_TAC MEASURABLE_UP_LIFT
   ++ Q.EXISTS_TAC `a`
   ++ RW_TAC std_ss [SUBSET_DEF]);

val MEASURE_PRESERVING_UP_SUBSET = store_thm
  ("MEASURE_PRESERVING_UP_SUBSET",
   ``!m1 m2.
       measure_space m1 /\
       a SUBSET measurable_sets m1 /\
       sigma_algebra (m_space m1, measurable_sets m1) ==>
       measure_preserving (m_space m1, a, measure m1) m2 SUBSET measure_preserving m1 m2``,
   RW_TAC std_ss [MEASURE_PRESERVING_UP_LIFT, SUBSET_DEF]
   ++ MATCH_MP_TAC MEASURE_PRESERVING_UP_LIFT
   ++ PROVE_TAC [SUBSET_DEF]);

val MEASURE_PRESERVING_UP_SIGMA = store_thm
  ("MEASURE_PRESERVING_UP_SIGMA",
   ``!m1 m2 a.
	measure_space m1 /\
       (measurable_sets m1 = subsets (sigma (m_space m1) a)) ==>
       measure_preserving (m_space m1, a, measure m1) m2 SUBSET measure_preserving m1 m2``,
   RW_TAC std_ss [MEASURE_PRESERVING_UP_LIFT, SUBSET_DEF]
   ++ MATCH_MP_TAC MEASURE_PRESERVING_UP_LIFT
   ++ ASM_REWRITE_TAC [SIGMA_SUBSET_SUBSETS, SIGMA_REDUCE]
   ++ FULL_SIMP_TAC std_ss [IN_MEASURE_PRESERVING, IN_MEASURABLE, m_space_def,
      		    	    measurable_sets_def]
   ++ MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
   ++ FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, space_def, subsets_def]);

(* ****************** *)

val MEASURABLE_PROD_SIGMA = store_thm
  ("MEASURABLE_PROD_SIGMA",
   ``!a a1 a2 f.
       sigma_algebra a /\
       (FST o f) IN measurable a a1 /\
       (SND o f) IN measurable a a2 ==>
       f IN measurable a (sigma ((space a1) CROSS (space a2))
       	    	       	 	(prod_sets (subsets a1) (subsets a2)))``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC MEASURABLE_SIGMA
   ++ FULL_SIMP_TAC std_ss [IN_MEASURABLE]
   ++ CONJ_TAC
   >> (RW_TAC std_ss [subset_class_def, subsets_def, space_def, IN_PROD_SETS]
      ++ PROVE_TAC [SIGMA_ALGEBRA, CROSS_SUBSET, SUBSET_DEF, subset_class_def, subsets_def,
      	 	    space_def])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_FUNSET, SPACE_SIGMA, IN_CROSS]
       ++ FULL_SIMP_TAC std_ss [IN_FUNSET, o_DEF])
   ++ RW_TAC std_ss [IN_PROD_SETS]
   ++ RW_TAC std_ss [PREIMAGE_CROSS]
   ++ `PREIMAGE (FST o f) t INTER PREIMAGE (SND o f) u INTER space a =
       (PREIMAGE (FST o f) t INTER space a) INTER (PREIMAGE (SND o f) u INTER space a)`
	by (RW_TAC std_ss [Once EXTENSION, IN_INTER] ++ DECIDE_TAC)
   ++ PROVE_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val MEASURABLE_RANGE_REDUCE = store_thm
  ("MEASURABLE_RANGE_REDUCE",
   ``!m f s. measure_space m /\
	   f IN measurable (m_space m, measurable_sets m) (s, POW s) /\
	     (~(s = {})) ==>
		f IN measurable (m_space m, measurable_sets m)
	(s INTER (IMAGE f (m_space m)), POW (s INTER (IMAGE f (m_space m))))``,
   RW_TAC std_ss [IN_MEASURABLE, POW_SIGMA_ALGEBRA, subsets_def, space_def, IN_FUNSET,
		  IN_INTER, IN_IMAGE, IN_POW, SUBSET_INTER,
		  MEASURABLE_SETS_SUBSET_SPACE, INTER_SUBSET]
   ++ METIS_TAC []);

val MEASURABLE_POW_TO_POW = store_thm
  ("MEASURABLE_POW_TO_POW",
   ``!m f.
	measure_space m /\
	(measurable_sets m = POW (m_space m)) ==>
	f IN measurable (m_space m, measurable_sets m) (UNIV, POW(UNIV))``,
   RW_TAC std_ss [IN_MEASURABLE, IN_POW, IN_UNIV, POW_SIGMA_ALGEBRA, subsets_def, space_def,
   	  	  IN_FUNSET, PREIMAGE_UNIV, SUBSET_UNIV, measure_space_def, SUBSET_DEF,
		  IN_INTER]);

val MEASURABLE_POW_TO_POW_IMAGE = store_thm
  ("MEASURABLE_POW_TO_POW_IMAGE",
   ``!m f.
        measure_space m /\
	(measurable_sets m = POW (m_space m)) ==>
	f IN measurable (m_space m, measurable_sets m)
	     		(IMAGE f (m_space m), POW(IMAGE f (m_space m)))``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`m`,`f`,`UNIV`]) MEASURABLE_RANGE_REDUCE
   ++ ASM_SIMP_TAC std_ss [UNIV_NEQ_EMPTY, INTER_UNIV, MEASURABLE_POW_TO_POW]);

val MEASURE_SPACE_SUBSET = store_thm
  ("MEASURE_SPACE_SUBSET",
   ``!s s' m. s' SUBSET s /\ measure_space (s,POW s, m) ==>
		measure_space (s',POW s', m)``,
   RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def, POW_SIGMA_ALGEBRA,
		  positive_def, measure_def, IN_POW, countably_additive_def, IN_FUNSET, IN_POW]
   ++ METIS_TAC [SUBSET_TRANS, SUBSET_REFL]);

val STRONG_MEASURE_SPACE_SUBSET = store_thm
  ("STRONG_MEASURE_SPACE_SUBSET",
   ``!s s'. s' SUBSET m_space s /\ measure_space s /\ POW s' SUBSET measurable_sets s ==>
		measure_space (s',POW s', measure s)``,
   REPEAT STRIP_TAC ++ MATCH_MP_TAC MEASURE_DOWN
   ++ Q.EXISTS_TAC `s`
   ++ RW_TAC std_ss [measure_def, m_space_def, measurable_sets_def, POW_SIGMA_ALGEBRA]);

val MEASURE_REAL_SUM_IMAGE = store_thm
  ("MEASURE_REAL_SUM_IMAGE",
   ``!m s. measure_space m /\ s IN measurable_sets m /\
                (!x. x IN s ==> {x} IN measurable_sets m) /\ FINITE s ==>
		(measure m s = SIGMA (\x. measure m {x}) s)``,
   Suff `!s. FINITE s ==>
	(\s. !m. measure_space m /\ s IN measurable_sets m /\
	     (!x. x IN s ==> {x} IN measurable_sets m) ==>
		(measure m s = SIGMA (\x. measure m {x}) s)) s`
   >> METIS_TAC []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, MEASURE_EMPTY, DELETE_NON_ELEMENT, IN_INSERT]
   ++ Q.PAT_ASSUM `!p.
            measure_space m /\ s IN measurable_set m /\
            (!x. x IN s ==> {x} IN measurable_sets m) ==>
            (measure m s = SIGMA (\x. measure m {x}) s)` (MP_TAC o GSYM o Q.SPEC `m`)
   ++ RW_TAC std_ss []
   ++ `s IN measurable_sets m`
	by (`s = (e INSERT s) DIFF {e}`
		by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DIFF, IN_SING]
		    ++ METIS_TAC [GSYM DELETE_NON_ELEMENT])
	    ++ POP_ORW
	    ++ FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def]
	    ++ METIS_TAC [space_def, subsets_def, ALGEBRA_DIFF])
   ++ ASM_SIMP_TAC std_ss []
   ++ MATCH_MP_TAC MEASURE_ADDITIVE
   ++ RW_TAC std_ss [IN_DISJOINT, IN_SING, Once INSERT_SING_UNION]
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]);

val SIGMA_POW = store_thm
  ("SIGMA_POW",
   ``!s. sigma s (POW s) = (s,POW s)``,
   RW_TAC std_ss [sigma_def, PAIR_EQ, EXTENSION, IN_BIGINTER, IN_POW, GSPECIFICATION]
   ++ EQ_TAC
   >> (RW_TAC std_ss [] ++ POP_ASSUM (MP_TAC o Q.SPEC `POW s`)
       ++ METIS_TAC [IN_POW, POW_SIGMA_ALGEBRA, SUBSET_REFL])
   ++ RW_TAC std_ss [SUBSET_DEF, IN_POW] ++ METIS_TAC []);

val finite_additivity_sufficient_for_finite_spaces = store_thm
  ("finite_additivity_sufficient_for_finite_spaces",
   ``!s m. sigma_algebra s /\ FINITE (space s) /\
	   positive (space s, subsets s, m) /\
	   additive (space s, subsets s, m) ==>
		measure_space (space s, subsets s, m)``,
   RW_TAC std_ss [countably_additive_def, additive_def, measurable_sets_def, measure_def,
		  IN_FUNSET, IN_UNIV, measure_space_def, m_space_def, SPACE]
   ++ `FINITE (subsets s)`
	by (Suff `subsets s SUBSET (POW (space s))`
	    >> METIS_TAC [SUBSET_FINITE, FINITE_POW]
	    ++ FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subset_class_def, SUBSET_DEF, IN_POW]
	    ++ METIS_TAC [])
   ++ `?N. !n. n >= N ==> (f n = {})`
	by METIS_TAC [finite_enumeration_of_sets_has_max_non_empty]
   ++ FULL_SIMP_TAC std_ss [GREATER_EQ]
   ++ `BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE f (count N))`
	by METIS_TAC [BIGUNION_IMAGE_UNIV]
   ++ RW_TAC std_ss [sums, SEQ]
   ++ Q.EXISTS_TAC `N`
   ++ RW_TAC std_ss [GREATER_EQ]
   ++ Suff `!n. N <= n ==> (sum (0,n) (m o f) = m(BIGUNION (IMAGE f (count N))))`
   >> RW_TAC real_ss [LESS_EQ_REFL]
   ++ Induct
   >> (RW_TAC std_ss [sum] ++ `count 0 = {}` by RW_TAC real_ss [EXTENSION, IN_COUNT, NOT_IN_EMPTY]
       ++ FULL_SIMP_TAC std_ss [IMAGE_EMPTY, BIGUNION_EMPTY, positive_def, measure_def])
   ++ STRIP_TAC
   ++ Cases_on `SUC n' = N`
   >> (POP_ORW
       ++ `m = measure (space s, subsets s,m)` by RW_TAC std_ss [measure_def]
       ++ POP_ORW
       ++ MATCH_MP_TAC ADDITIVE_SUM
       ++ RW_TAC std_ss [m_space_def, measurable_sets_def, IN_FUNSET, IN_UNIV, additive_def,
			 measure_def, SIGMA_ALGEBRA_ALGEBRA, SPACE])
   ++ `N <= n'`
	by (NTAC 2 (POP_ASSUM MP_TAC) ++ DECIDE_TAC)
   ++ FULL_SIMP_TAC std_ss []
   ++ RW_TAC std_ss [sum]
   ++ FULL_SIMP_TAC real_ss [positive_def, measure_def]);

val finite_additivity_sufficient_for_finite_spaces2 = store_thm
  ("finite_additivity_sufficient_for_finite_spaces2",
   ``!m. sigma_algebra (m_space m, measurable_sets m) /\ FINITE (m_space m) /\
	   positive m /\
	   additive m ==>
		measure_space m``,
   REPEAT STRIP_TAC
   ++ Suff `measure_space (space (m_space m, measurable_sets m),
      	   		   subsets (m_space m, measurable_sets m), measure m)`
   >> RW_TAC std_ss [space_def, subsets_def, MEASURE_SPACE_REDUCE]
   ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   ++ RW_TAC std_ss [space_def, subsets_def, MEASURE_SPACE_REDUCE]);

val IMAGE_SING = store_thm
 ("IMAGE_SING", ``!f x. IMAGE f {x} = {f x}``,
  RW_TAC std_ss [EXTENSION,IN_SING,IN_IMAGE] ++ METIS_TAC []);

val SUBSET_BIGINTER = store_thm
("SUBSET_BIGINTER", ``!X P. X SUBSET BIGINTER P <=> !Y. Y IN P ==> X SUBSET Y``,
  RW_TAC std_ss [SUBSET_DEF,IN_BIGINTER]
  ++ METIS_TAC []);

val MEASURE_SPACE_INCREASING = store_thm
  ("MEASURE_SPACE_INCREASING",``!m. measure_space m ==> increasing m``,
  RW_TAC real_ss [] ++ `additive m` by RW_TAC real_ss [MEASURE_SPACE_ADDITIVE]
  ++ FULL_SIMP_TAC real_ss [measure_space_def,sigma_algebra_def,ADDITIVE_INCREASING]);

val MEASURE_SPACE_POSITIVE = store_thm
  ("MEASURE_SPACE_POSITIVE",``!m. measure_space m ==> positive m``,
  PROVE_TAC [measure_space_def]);

val MEASURE_SPACE_INTER = store_thm
  ("MEASURE_SPACE_INTER",``!m s t. (measure_space m) /\ (s IN measurable_sets m) /\
  			(t IN measurable_sets m) ==> (s INTER t IN measurable_sets m)``,
  METIS_TAC [measure_space_def,sigma_algebra_def,subsets_def,
   	    (REWRITE_RULE [subsets_def] (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_INTER))]);

val MEASURE_SPACE_UNION = store_thm
  ("MEASURE_SPACE_UNION",``!m s t. (measure_space m) /\ (s IN measurable_sets m) /\
  			      (t IN measurable_sets m) ==> (s UNION t IN measurable_sets m)``,
  METIS_TAC [measure_space_def,sigma_algebra_def,subsets_def,
              (REWRITE_RULE [subsets_def] (Q.SPEC `(m_space m,measurable_sets m)`
              ALGEBRA_UNION))]);

val MEASURE_SPACE_DIFF = store_thm
  ("MEASURE_SPACE_DIFF",``!m s t. (measure_space m) /\ (s IN measurable_sets m) /\
                    (t IN measurable_sets m) ==> (s DIFF t IN measurable_sets m)``,
   METIS_TAC [measure_space_def,sigma_algebra_def,subsets_def,
       (REWRITE_RULE [subsets_def] (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_DIFF))]);

val MEASURE_COMPL_SUBSET = store_thm
  ("MEASURE_COMPL_SUBSET",
   ``!m s.
       measure_space m /\ s IN measurable_sets m /\ t IN measurable_sets m /\ (t SUBSET s) ==>
       (measure m (s DIFF t) = measure m s - measure m t)``,
   RW_TAC std_ss []
   ++ Suff `measure m s = measure m t + measure m (s DIFF t)`
   >> REAL_ARITH_TAC
   ++ MATCH_MP_TAC ADDITIVE
   ++ Q.PAT_ASSUM `measure_space m` MP_TAC
   ++ RW_TAC std_ss [measure_space_def, sigma_algebra_def, DISJOINT_DEF,
                            EXTENSION, IN_DIFF, IN_UNIV, IN_UNION, IN_INTER,
                            NOT_IN_EMPTY]
   ++ METIS_TAC [COUNTABLY_ADDITIVE_ADDITIVE,MEASURE_SPACE_DIFF,measure_space_def,
      		 sigma_algebra_def,SUBSET_DEF]);

val MEASURE_SPACE_BIGUNION = store_thm
  ("MEASURE_SPACE_BIGUNION",``!m s. measure_space m /\ (!n:num. s n IN measurable_sets m)
              ==> (BIGUNION (IMAGE s UNIV) IN measurable_sets m)``,
  RW_TAC std_ss []
  ++ (MP_TAC o REWRITE_RULE [subsets_def,space_def,IN_UNIV,IN_FUNSET] o
               Q.SPEC `(m_space m,measurable_sets m)`) SIGMA_ALGEBRA_FN
  ++ METIS_TAC [measure_space_def]);

val MEASURE_SPACE_IN_MSPACE = store_thm
  ("MEASURE_SPACE_IN_MSPACE",``!m A. measure_space m /\ A IN measurable_sets m
             ==> (!x. x IN A ==> x IN m_space m)``,
   METIS_TAC [measure_space_def,sigma_algebra_def,algebra_def,measurable_sets_def,space_def,
              subset_class_def,subsets_def,SUBSET_DEF]);

val MEASURE_SPACE_SUBSET_MSPACE = store_thm
  ("MEASURE_SPACE_SUBSET_MSPACE", ``!A m. measure_space m /\ A IN measurable_sets m
                  ==> A SUBSET m_space m``,
   RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,subset_class_def,
                  subsets_def, space_def]);

val MEASURE_SPACE_EMPTY_MEASURABLE = store_thm
  ("MEASURE_SPACE_EMPTY_MEASURABLE",``!m. measure_space m
                              ==> {} IN measurable_sets m``,
   RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,subsets_def, space_def]);

val MEASURE_SPACE_MSPACE_MEASURABLE = store_thm
  ("MEASURE_SPACE_MSPACE_MEASURABLE",``!m. measure_space m ==> (m_space m) IN measurable_sets m``,
   RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def, subsets_def, space_def]
   ++ METIS_TAC [DIFF_EMPTY]);

val SIGMA_ALGEBRA_FN_BIGINTER = store_thm
  ("SIGMA_ALGEBRA_FN_BIGINTER",
   ``!a.
       sigma_algebra a ==> subset_class (space a) (subsets a) /\ {} IN subsets a /\
       (!s. s IN subsets a ==> (space a DIFF s) IN subsets a) /\
       (!f : num -> 'a -> bool. f IN (UNIV -> subsets a)
             ==> BIGINTER (IMAGE f UNIV) IN subsets a)``,
  RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_UNIV, SUBSET_DEF]
  ++ ASSUME_TAC (Q.SPECL [`space a`,`(IMAGE (f:num -> 'a -> bool) UNIV)`] DIFF_BIGINTER)
  ++ `!t. t IN IMAGE f UNIV ==> t SUBSET space a`
  	by (FULL_SIMP_TAC std_ss [IN_IMAGE,sigma_algebra_def,algebra_def,subsets_def,
                                  space_def,subset_class_def,IN_UNIV]
  	    ++ RW_TAC std_ss []
  	    ++ METIS_TAC [])
  ++ `IMAGE f UNIV <> {}` by RW_TAC std_ss [IMAGE_EQ_EMPTY,UNIV_NOT_EMPTY]
  ++ FULL_SIMP_TAC std_ss []
  ++ `BIGUNION (IMAGE (\u. space a DIFF u) (IMAGE f UNIV)) IN subsets a`
        by (Q.PAT_ASSUM `!c. M ==> BIGUNION c IN subsets a` (MATCH_MP_TAC)
            ++ RW_TAC std_ss []
	    >> (MATCH_MP_TAC COUNTABLE_IMAGE
            	++ RW_TAC std_ss [COUNTABLE_ENUM]
            	++ Q.EXISTS_TAC `f`
            	++ RW_TAC std_ss [])
   	    ++ FULL_SIMP_TAC std_ss [IN_IMAGE])
  ++ METIS_TAC []);

val MEASURE_SPACE_BIGINTER = store_thm
  ("MEASURE_SPACE_BIGINTER",``!m s. measure_space m /\ (!n:num. s n IN measurable_sets m)
                  ==> (BIGINTER (IMAGE s UNIV) IN measurable_sets m)``,
  RW_TAC std_ss []
  ++ (MP_TAC o REWRITE_RULE [subsets_def,space_def,IN_UNIV,IN_FUNSET] o
               Q.SPEC `(m_space m,measurable_sets m)`) SIGMA_ALGEBRA_FN_BIGINTER
  ++ METIS_TAC [measure_space_def]);

val MONOTONE_CONVERGENCE2 = store_thm
  ("MONOTONE_CONVERGENCE2", ``!m f. measure_space m /\
       f IN (UNIV -> measurable_sets m) /\ (!n. f n SUBSET f (SUC n)) ==>
       (measure m o f --> measure m (BIGUNION (IMAGE f UNIV)))``,
  METIS_TAC [MONOTONE_CONVERGENCE]);

val MONOTONE_CONVERGENCE_BIGINTER = store_thm
  ("MONOTONE_CONVERGENCE_BIGINTER",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!n. f (SUC n) SUBSET f n) /\ (s = BIGINTER (IMAGE f UNIV)) ==>
       measure m o f --> measure m s``,
  RW_TAC std_ss [IN_FUNSET, IN_UNIV]
  ++ `BIGINTER (IMAGE f UNIV) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_BIGINTER]
  ++ `!n. f n SUBSET f 0`
       by (Induct_on `n` >> RW_TAC std_ss [SUBSET_REFL]
	     ++ METIS_TAC [SUBSET_TRANS])
  ++ `BIGINTER (IMAGE f UNIV) SUBSET (f 0)`
       by (MATCH_MP_TAC BIGINTER_SUBSET
           ++ METIS_TAC [IMAGE_EQ_EMPTY,UNIV_NOT_EMPTY,IN_IMAGE,IN_UNIV])
  ++ Q.ABBREV_TAC `g = (\n. (f 0) DIFF (f n))`
  ++ FULL_SIMP_TAC std_ss [o_DEF]
  ++ `!n. measure m (f 0) - measure m (f n) = measure m (g n)` by METIS_TAC [MEASURE_COMPL_SUBSET]
  ++ `(\x. measure m (f x)) = (\x. (\x. measure m (f 0)) x - (\x. measure m (g x)) x)`
       by (RW_TAC std_ss [FUN_EQ_THM]
           ++ METIS_TAC [REAL_EQ_SUB_LADD,REAL_EQ_SUB_RADD,real_sub,REAL_ADD_COMM])
  ++ POP_ORW
  ++ `BIGINTER (IMAGE f UNIV) = (f 0) DIFF BIGUNION (IMAGE (\u. (f 0) DIFF u) (IMAGE f UNIV))`
      by (MATCH_MP_TAC DIFF_BIGINTER
          ++ METIS_TAC [IN_IMAGE,IN_UNIV,IMAGE_EQ_EMPTY,UNIV_NOT_EMPTY])
  ++ POP_ORW
  ++ `BIGUNION (IMAGE (\u. f 0 DIFF u) (IMAGE f UNIV)) = BIGUNION (IMAGE (\n. f 0 DIFF f n) UNIV)`
        by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_UNIV,IN_IMAGE]
            ++ METIS_TAC [SUBSET_DEF,IN_DIFF])
  ++ POP_ORW
  ++ RW_TAC std_ss []
  ++ `(\n. measure m (g n)) --> measure m (BIGUNION (IMAGE g UNIV))`
       by ((MATCH_MP_TAC o REWRITE_RULE [o_DEF]) MONOTONE_CONVERGENCE2
           ++ RW_TAC std_ss [IN_FUNSET,IN_UNIV]
	   >> METIS_TAC [MEASURE_SPACE_DIFF]
	   ++ Q.UNABBREV_TAC `g`
	   ++ RW_TAC std_ss [SUBSET_DEF,IN_DIFF,GSPECIFICATION]
           ++ METIS_TAC [SUBSET_DEF])
  ++ Suff `measure m (f 0 DIFF BIGUNION (IMAGE (\n. f 0 DIFF f n) UNIV)) =
           measure m (f 0) - measure m (BIGUNION (IMAGE (\n. f 0 DIFF f n) UNIV))`
  >> (RW_TAC std_ss []
      ++ `(\x. measure m (f 0) - measure m (g x)) =
      	  (\x. (\x. measure m (f 0)) x - (\x. measure m (g x)) x)`
            by RW_TAC std_ss [FUN_EQ_THM]
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_SUB
      ++ METIS_TAC [SEQ_CONST])
  ++ MATCH_MP_TAC MEASURE_COMPL_SUBSET
  ++ RW_TAC std_ss []
  >> (MATCH_MP_TAC MEASURE_SPACE_BIGUNION
      ++ METIS_TAC [MEASURE_SPACE_DIFF])
  ++ RW_TAC std_ss [BIGUNION_SUBSET,IN_IMAGE,IN_UNIV]
  ++ METIS_TAC [DIFF_SUBSET]);

val MONOTONE_CONVERGENCE_BIGINTER2 = store_thm
  ("MONOTONE_CONVERGENCE_BIGINTER2",
   ``!m f. measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!n. f (SUC n) SUBSET f n) ==>
       measure m o f --> measure m (BIGINTER (IMAGE f UNIV))``,
  METIS_TAC [MONOTONE_CONVERGENCE_BIGINTER]);

val MEASURE_SPACE_RESTRICTED = store_thm
("MEASURE_SPACE_RESTRICTED", ``!m s. measure_space m /\ s IN measurable_sets m ==>
   measure_space (s, IMAGE (\t. s INTER t) (measurable_sets m), measure m)``,
  RW_TAC std_ss []
  ++ `positive (s,IMAGE (\t. s INTER t) (measurable_sets m),measure m)`
        by (RW_TAC std_ss [positive_def,measure_def,measurable_sets_def,IN_IMAGE]
            ++ METIS_TAC [MEASURE_SPACE_POSITIVE,MEASURE_SPACE_INTER,positive_def])
  ++ `countably_additive (s,IMAGE (\t. s INTER t) (measurable_sets m),measure m)`
        by (RW_TAC std_ss [countably_additive_def,measure_def,measurable_sets_def,
                           IN_IMAGE,IN_FUNSET,IN_UNIV]
            ++ `!x. f x IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_INTER]
            ++ `BIGUNION (IMAGE f univ(:num)) IN measurable_sets m`
                 by METIS_TAC [MEASURE_SPACE_INTER]
	    ++ `countably_additive m` by METIS_TAC [measure_space_def]
	    ++ FULL_SIMP_TAC std_ss [countably_additive_def,IN_FUNSET,IN_UNIV])
  ++ RW_TAC std_ss [measure_space_def,sigma_algebra_def,measurable_sets_def,subsets_def,
                    m_space_def,IN_IMAGE]
  >> (RW_TAC std_ss [algebra_def,space_def,subsets_def,subset_class_def,IN_IMAGE]
      << [RW_TAC std_ss [INTER_SUBSET],
	  METIS_TAC [INTER_EMPTY,MEASURE_SPACE_EMPTY_MEASURABLE],
	  Q.EXISTS_TAC `m_space m DIFF t`
	  ++ RW_TAC std_ss [MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE,EXTENSION,
                            IN_DIFF,IN_INTER]
	  ++ METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF],
	  Q.EXISTS_TAC `t' UNION t''`
	  ++ RW_TAC std_ss [MEASURE_SPACE_UNION,UNION_OVER_INTER]])
  ++ `BIGUNION c SUBSET s`
       by (RW_TAC std_ss [SUBSET_DEF,IN_BIGUNION]
           ++ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_IMAGE]
	   ++ `?t. (s' = s INTER t) /\ t IN measurable_sets m` by METIS_TAC []
           ++ METIS_TAC [IN_INTER])
  ++ Q.EXISTS_TAC `BIGUNION c`
  ++ RW_TAC std_ss [SUBSET_INTER2]
  ++ Suff `BIGUNION c IN subsets (m_space m, measurable_sets m)`
  >> RW_TAC std_ss [subsets_def]
  ++ MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
  ++ RW_TAC std_ss [subsets_def]
  >> FULL_SIMP_TAC std_ss [measure_space_def]
  ++ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_IMAGE]
  ++ METIS_TAC [MEASURE_SPACE_INTER]);

val MEASURE_SPACE_CMUL = store_thm
  ("MEASURE_SPACE_CMUL", ``!m c. measure_space m /\ 0 <= c ==>
                   measure_space (m_space m, measurable_sets m, (\a. c * measure m a))``,
  RW_TAC real_ss [measure_space_def,m_space_def,measurable_sets_def,measure_def,positive_def]
  >> METIS_TAC [REAL_LE_MUL]
  ++ RW_TAC std_ss [countably_additive_def,measure_def,measurable_sets_def,o_DEF]
  ++ METIS_TAC [SER_CMUL,countably_additive_def]);

val BIGUNION_IMAGE_Q = store_thm
  ("BIGUNION_IMAGE_Q",
   ``!a f: extreal -> 'a -> bool. sigma_algebra a /\ f IN (Q_set -> subsets a)
            ==> BIGUNION (IMAGE f Q_set) IN subsets a``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_UNIV, SUBSET_DEF]
   ++ Q.PAT_ASSUM `!c. countable c /\ P c ==> Q c` MATCH_MP_TAC
   ++ RW_TAC std_ss [COUNTABLE_IMAGE, IN_IMAGE,Q_COUNTABLE]
   ++ METIS_TAC []);


(* ******************************************* *)
(*    ------------------------------------     *)
(*    Borel Space and Measurable functions     *)
(*    ------------------------------------     *)
(* ******************************************* *)

val Borel_def = Define
   `Borel = sigma (UNIV:extreal->bool) (IMAGE (\a. {x | x < a}) UNIV)`;

val SIGMA_ALGEBRA_BOREL = store_thm
 ("SIGMA_ALGEBRA_BOREL",``sigma_algebra Borel``,
  RW_TAC std_ss [Borel_def]
  ++ MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
  ++ RW_TAC std_ss [subset_class_def,SUBSET_UNIV]);

val MEASURABLE_BOREL = store_thm
 ("MEASURABLE_BOREL",``!f a. (f IN measurable a Borel) = (sigma_algebra a) /\
                        (f IN (space a -> UNIV)) /\
                        (!c. ((PREIMAGE f {x| x < c}) INTER (space a)) IN subsets a)``,
  RW_TAC std_ss []
  ++ `sigma_algebra Borel` by RW_TAC std_ss [SIGMA_ALGEBRA_BOREL]
  ++ `space Borel = UNIV` by RW_TAC std_ss [Borel_def,space_def,SPACE_SIGMA]
  ++ EQ_TAC
  >> (RW_TAC std_ss [Borel_def,IN_MEASURABLE,IN_FUNSET,IN_UNIV,subsets_def,GSPECIFICATION]
      ++ POP_ASSUM MATCH_MP_TAC
      ++ MATCH_MP_TAC IN_SIGMA
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ RW_TAC std_ss [Borel_def]
  ++ MATCH_MP_TAC MEASURABLE_SIGMA
  ++ RW_TAC std_ss [subset_class_def,SUBSET_UNIV,IN_IMAGE,IN_UNIV]
  ++ METIS_TAC []);

val IN_MEASURABLE_BOREL = store_thm
  ("IN_MEASURABLE_BOREL", ``!f a. f IN measurable a Borel =
	( sigma_algebra a /\ f IN (space a -> UNIV) /\
	!c. ({x | f x < c} INTER space a) IN subsets a)``,
  RW_TAC std_ss []
  ++ `!c. {x | f x < c} = PREIMAGE f {x| x < c}`
       by RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION]
  ++ RW_TAC std_ss [MEASURABLE_BOREL]);

val IN_MEASURABLE_BOREL_NEGINF = store_thm
  ("IN_MEASURABLE_BOREL_NEGINF", ``!f a. f IN measurable a Borel ==>
	({x | f x = NegInf} INTER space a IN subsets a )``,
  RW_TAC std_ss [IN_MEASURABLE_BOREL,GSPECIFICATION,IN_FUNSET,IN_UNIV]
  ++ `{x | f x = NegInf} INTER space a =
      BIGINTER (IMAGE (\n. {x | f x < -(&n)} INTER space a) UNIV)`
       by (RW_TAC std_ss [EXTENSION,IN_BIGINTER_IMAGE,IN_UNIV,GSPECIFICATION,IN_INTER]
           ++ EQ_TAC >> METIS_TAC [num_not_infty,lt_infty,extreal_ainv_def,extreal_of_num_def]
	   ++ RW_TAC std_ss []
	   ++ SPOSE_NOT_THEN ASSUME_TAC
	   ++ METIS_TAC [SIMP_EXTREAL_ARCH,extreal_lt_def,extreal_ainv_def,neg_neg,lt_neg])
  ++ RW_TAC std_ss []
  ++ RW_TAC std_ss [IN_FUNSET,IN_UNIV,SIGMA_ALGEBRA_FN_BIGINTER]);

val IN_MEASURABLE_BOREL_ALT1 = store_thm
  ("IN_MEASURABLE_BOREL_ALT1", ``!f a. f IN measurable a Borel =
	( sigma_algebra a /\ f IN (space a -> UNIV) /\
	!c. ({x | c <= f x} INTER space a) IN subsets a )``,
  RW_TAC std_ss [IN_MEASURABLE_BOREL,GSPECIFICATION,IN_FUNSET,IN_UNIV]
  ++ EQ_TAC
  >> (RW_TAC std_ss []
      ++ `{x | c <= f x} = PREIMAGE f {x | c <= x}` by RW_TAC std_ss[PREIMAGE_def, GSPECIFICATION]
      ++ `!c. {x | f x < c} = PREIMAGE f {x | x < c}`
          by RW_TAC std_ss[PREIMAGE_def, GSPECIFICATION]
      ++ `!c. space a DIFF ((PREIMAGE f {x | x < c}) INTER space a) IN subsets a`
          by METIS_TAC [sigma_algebra_def,algebra_def]
      ++ `!c. space a DIFF (PREIMAGE f {x | x < c}) IN subsets a`
          by METIS_TAC [DIFF_INTER2]
      ++ `!c. (PREIMAGE f (COMPL {x | x < c}) INTER space a) IN subsets a`
          by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
      ++ `!c. COMPL {x | x < c} = {x | c <= x}`
          by RW_TAC std_ss [EXTENSION, IN_COMPL, IN_UNIV, IN_DIFF, GSPECIFICATION, extreal_lt_def]
      ++ FULL_SIMP_TAC std_ss [])
  ++ RW_TAC std_ss []
  ++ `{x | f x < c} = PREIMAGE f {x | x < c}`
      by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
  ++ `!c. {x | c <= f x} = PREIMAGE f {x | c <= x}`
      by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
  ++ `!c. space a DIFF ((PREIMAGE f {x | c <= x}) INTER space a) IN subsets a`
      by METIS_TAC [sigma_algebra_def,algebra_def]
  ++ `!c. space a DIFF (PREIMAGE f {x | c <= x}) IN subsets a`
      by METIS_TAC [DIFF_INTER2]
  ++ `!c. (PREIMAGE f (COMPL {x | c <= x}) INTER space a) IN subsets a`
      by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
  ++ `!c. COMPL {x | c <= x} = {x | x < c}`
      by RW_TAC std_ss [EXTENSION, IN_COMPL, IN_UNIV, IN_DIFF, GSPECIFICATION, extreal_lt_def]
  ++ METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT2 = store_thm
("IN_MEASURABLE_BOREL_ALT2", ``!f a. f IN measurable a Borel =
	(sigma_algebra a /\ f IN (space a -> UNIV) /\
	 !c. ({x | f x <= c } INTER space a) IN subsets a)``,
  RW_TAC std_ss []
  ++ EQ_TAC
  >> (RW_TAC std_ss [IN_MEASURABLE_BOREL]
      ++ Cases_on `c = NegInf`
      >> (RW_TAC std_ss [le_infty] ++ METIS_TAC [IN_MEASURABLE_BOREL, IN_MEASURABLE_BOREL_NEGINF])
      ++ Cases_on `c = PosInf`
      >> (RW_TAC std_ss [le_infty,GSPEC_T,INTER_UNIV]
	  ++ FULL_SIMP_TAC std_ss [ALGEBRA_SPACE,sigma_algebra_def])
      ++  `?r. c = Normal r` by METIS_TAC [extreal_cases]
      ++ RW_TAC std_ss []
      ++ `{x | f x <= Normal r} INTER (space a) =
      	  BIGINTER (IMAGE (\n:num. {x | f x < Normal (r + (1 / 2) pow n)} INTER space a) UNIV)`
  	by (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV,IN_INTER]
	    ++ EQ_TAC
            >> (RW_TAC std_ss [GSPECIFICATION,GSYM extreal_add_def]
                ++ `0:real < (1 / 2) pow n` by RW_TAC real_ss [REAL_POW_LT]
                ++ `0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_of_num_def, extreal_lt_eq]
                ++ Cases_on `f x = NegInf` >> METIS_TAC [lt_infty,extreal_add_def]
                ++ METIS_TAC [let_add2,extreal_of_num_def,extreal_not_infty, add_rzero, le_infty])
	     ++ RW_TAC std_ss [GSPECIFICATION]
	     ++ `!n. f x < Normal (r + (1 / 2) pow n)` by METIS_TAC []
	     ++ `(\n. r + (1 / 2) pow n) = (\n. (\n. r) n + (\n. (1 / 2) pow n) n) `
	     	 by RW_TAC real_ss [FUN_EQ_THM]
	     ++ `(\n. r) --> r` by RW_TAC std_ss [SEQ_CONST]
	     ++ `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
	     ++ `(\n. r + (1 / 2) pow n) --> r`
	     	 by METIS_TAC [Q.SPECL [`(\n. r)`,`r`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD,
		    	       REAL_ADD_RID]
	     ++ Cases_on `f x = NegInf` >> METIS_TAC [le_infty]
             ++ `f x <> PosInf` by METIS_TAC [lt_infty]
             ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
             ++ FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
 	     ++ METIS_TAC [REAL_LT_IMP_LE,
	     		   Q.SPECL [`r'`,`r`,`(\n. r + (1 / 2) pow n)`] LE_SEQ_IMP_LE_LIM])
    ++ `BIGINTER (IMAGE (\n:num. {x | f x < Normal (r + (1 / 2) pow n)} INTER space a) UNIV)
       		 IN subsets a`
	 by (RW_TAC std_ss []
	     ++ (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN_BIGINTER
	     ++ RW_TAC std_ss []
	     ++ `(\n. {x | f x < Normal (r + (1/2) pow n)} INTER space a) IN (UNIV -> subsets a)` by (RW_TAC std_ss [IN_FUNSET])
	     ++ METIS_TAC [])
    ++ METIS_TAC [])
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL]
  ++ `!c. {x | c < f x} INTER space a IN subsets a`
       by (RW_TAC std_ss []
           ++ `{x | c < f x} INTER space a = (space a) DIFF ({x | f x <= c} INTER space a)`
                by (RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION,IN_DIFF]
		    ++ METIS_TAC [extreal_lt_def])
           ++ METIS_TAC [sigma_algebra_def,algebra_def])
  ++ `{x | f x = PosInf} INTER space a = BIGINTER (IMAGE (\n. {x | &n < f x} INTER space a) UNIV)`
       by (RW_TAC std_ss [EXTENSION,IN_BIGINTER_IMAGE,IN_UNIV,GSPECIFICATION,IN_INTER]
           ++ EQ_TAC >> METIS_TAC [num_not_infty,lt_infty]
	   ++ RW_TAC std_ss []
	   ++ SPOSE_NOT_THEN ASSUME_TAC
	   ++ METIS_TAC [SIMP_EXTREAL_ARCH,extreal_lt_def])
  ++ `{x | f x = PosInf} INTER space a IN subsets a`
      by  RW_TAC std_ss [IN_FUNSET,IN_UNIV,SIGMA_ALGEBRA_FN_BIGINTER]
  ++ `{x | f x <> PosInf} INTER space a = (space a) DIFF ({x | f x = PosInf} INTER (space a))`
       by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION, IN_SING, IN_DIFF] ++ METIS_TAC [])
  ++ Cases_on `c = PosInf`
  >> (RW_TAC std_ss [GSYM lt_infty] ++ METIS_TAC [sigma_algebra_def, algebra_def, lt_infty])
  ++ Cases_on `c = NegInf`
  >> (RW_TAC std_ss [lt_infty,GSPEC_F,INTER_EMPTY]
      ++ FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def])
  ++ `?r. c = Normal r` by METIS_TAC [extreal_cases]
  ++ RW_TAC std_ss []
  ++ `{x | f x < Normal r} INTER (space a) =
      BIGUNION (IMAGE (\n:num. {x | f x <= Normal (r - (1/2) pow n)} INTER space a) UNIV)`
	by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER, GSPECIFICATION]
  	    ++ `(\n. r - (1 / 2) pow n) = (\n. (\n. r) n - (\n. (1 / 2) pow n) n)`
	        by RW_TAC real_ss [FUN_EQ_THM]
  	    ++ `(\n. r) --> r` by RW_TAC std_ss [SEQ_CONST]
  	    ++ `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
  	    ++ `(\n. r - (1 / 2) pow n) --> r`
	        by METIS_TAC [Q.SPECL [`(\n. r)`,`r`,`(\n. (1/2) pow n)`,`0`] SEQ_SUB,
		   	      REAL_SUB_RZERO]
	    ++ EQ_TAC
	    >> (RW_TAC std_ss []
                ++ Cases_on `f x = NegInf` >> METIS_TAC [le_infty]
                ++ `f x <> PosInf` by METIS_TAC [lt_infty]
                ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
                ++ FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
		++ `!e:real. 0 < e ==> ?N. !n. n >= N ==> abs ((1 / 2) pow n) < e`
		  by FULL_SIMP_TAC real_ss [Q.SPECL [`(\n. (1/2) pow n)`,`0`] SEQ, REAL_SUB_RZERO]
		++ `!n. abs ((1 / 2) pow n):real = (1 / 2) pow n`
		  by FULL_SIMP_TAC real_ss [POW_POS,ABS_REFL]
		++ `!e:real. 0 < e ==> ?N. !n. n >= N ==> (1 / 2) pow n < e` by METIS_TAC []
		++ `?N. !n. n >= N ==> (1 / 2) pow n < r - r'` by METIS_TAC [REAL_SUB_LT]
		++ Q.EXISTS_TAC `N`
		++ `(1 / 2) pow N < r - r'` by FULL_SIMP_TAC real_ss []
		++ FULL_SIMP_TAC real_ss [GSYM REAL_LT_ADD_SUB, REAL_ADD_COMM, REAL_LT_IMP_LE])
	    ++ RW_TAC std_ss []
	    >> (`!n. - ((1 / 2) pow n) < 0:real`
	        by METIS_TAC [REAL_POW_LT, REAL_NEG_0, REAL_LT_NEG, EVAL ``0:real < 1/2``]
	        ++ `!n. r - (1 / 2) pow n < r` by METIS_TAC [REAL_LT_IADD, REAL_ADD_RID, real_sub]
                ++ Cases_on `f x = NegInf` >> METIS_TAC [lt_infty]
                ++ `f x <> PosInf` by METIS_TAC [le_infty, extreal_not_infty]
                ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
                ++ FULL_SIMP_TAC std_ss [extreal_lt_eq, extreal_le_def]
     		++ METIS_TAC [REAL_LET_TRANS])
	     ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss []
  ++ MATCH_MP_TAC SIGMA_ALGEBRA_ENUM
  ++ RW_TAC std_ss [IN_FUNSET]);

val IN_MEASURABLE_BOREL_ALT3 = store_thm
("IN_MEASURABLE_BOREL_ALT3", ``!f a. f IN measurable a Borel =
	sigma_algebra a /\ f IN (space a -> UNIV) /\
	 !c. ({x | c < f x } INTER space a) IN subsets a``,
 RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2,GSPECIFICATION]
 ++ EQ_TAC
 >> (RW_TAC std_ss []
     ++ `{x| c < f x} = PREIMAGE f {x | c < x}` by RW_TAC std_ss[PREIMAGE_def, GSPECIFICATION]
     ++ `!c. {x | f x <= c} = PREIMAGE f {x | x <= c}`
         by RW_TAC std_ss[PREIMAGE_def, GSPECIFICATION]
     ++ `!c. space a DIFF ((PREIMAGE f {x | x <= c}) INTER space a) IN subsets a`
     	 by METIS_TAC [sigma_algebra_def, algebra_def]
     ++ `!c. space a DIFF (PREIMAGE f {x | x <= c}) IN subsets a`
         by METIS_TAC [DIFF_INTER2]
     ++ `!c. (PREIMAGE f (COMPL {x | x <= c}) INTER space a) IN subsets a`
     	 by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
     ++ `COMPL {x | x <= c} = {x | c < x}`
     	 by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_COMPL, extreal_lt_def]
     ++ METIS_TAC [])
 ++ RW_TAC std_ss []
 ++ `{x | f x <= c} = PREIMAGE f {x | x <= c}` by RW_TAC std_ss[PREIMAGE_def, GSPECIFICATION]
 ++ `!c. { x | c < f x } = PREIMAGE f { x | c < x }`
     by RW_TAC std_ss[PREIMAGE_def, GSPECIFICATION]
 ++ `!c. space a DIFF ((PREIMAGE f {x | c < x}) INTER space a) IN subsets a`
     by METIS_TAC [sigma_algebra_def, algebra_def]
 ++ `!c. space a DIFF (PREIMAGE f {x | c < x}) IN subsets a` by METIS_TAC [DIFF_INTER2]
 ++ `!c. (PREIMAGE f (COMPL {x | c < x}) INTER space a) IN subsets a`
     by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
 ++ `COMPL {x | c < x} = {x | x <= c}`
     by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_COMPL, extreal_lt_def]
 ++ METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT4 = store_thm
("IN_MEASURABLE_BOREL_ALT4", ``!f a.  f IN measurable a Borel =
	           sigma_algebra a /\ f IN (space a -> UNIV) /\
		   !c d. ({x | c <= f x /\ f x < d} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  ++ EQ_TAC
  >> (STRIP_TAC
      ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL]
      ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL]
      ++ RW_TAC std_ss []
      ++ `(!d. {x | f x < d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL]
      ++ `(!c. {x | c <= f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
      ++ `{x | c <= f x /\ f x < d} INTER space a =
      	  ({x | c <= f x} INTER space a) INTER ({x | f x < d} INTER space a)`
          by (RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION] ++ METIS_TAC [])
      ++ METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, algebra_def, IN_MEASURABLE_BOREL])
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL]
  ++ `{x | f x < c} INTER space a = {x | NegInf <= f x /\ f x < c} INTER space a`
      by RW_TAC std_ss [le_infty]
  ++ METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT5 = store_thm
("IN_MEASURABLE_BOREL_ALT5", ``!f a.  f IN measurable a Borel =
	           sigma_algebra a /\ f IN (space a -> UNIV) /\
		   !c d. ({x | c < f x /\ f x <= d} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  ++ EQ_TAC
  >> (STRIP_TAC
      ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL]
      ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL]
      ++ RW_TAC std_ss []
      ++ `(!d. {x | f x <= d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
      ++ `(!c. {x | c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
      ++ `{x | c < f x /\ f x <= d} INTER space a =
      	  ({x | c < f x} INTER space a) INTER ({x | f x <= d} INTER space a)`
          by (RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION] ++ METIS_TAC [])
      ++ METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, algebra_def, IN_MEASURABLE_BOREL])
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT3]
  ++ `{x | c < f x} INTER space a = {x | c < f x /\ f x <= PosInf} INTER space a`
      by RW_TAC std_ss [le_infty]
  ++ METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT6 = store_thm
("IN_MEASURABLE_BOREL_ALT6", ``!f a.  f IN measurable a Borel =
	           sigma_algebra a /\ f IN (space a -> UNIV) /\
		   !c d. ({x | c <= f x /\ f x <= d} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  ++ EQ_TAC
  >> (STRIP_TAC
      ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL]
      ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL]
      ++ RW_TAC std_ss []
      ++ `(!d. {x | f x <= d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
      ++ `(!c. {x | c <= f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
      ++ `{x | c <= f x /\ f x <= d} INTER space a =
      	  ({x | c <= f x} INTER space a) INTER ({x | f x <= d} INTER space a)`
          by (RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION] ++ METIS_TAC [])
      ++ METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, algebra_def, IN_MEASURABLE_BOREL])
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2]
  ++ `{x | f x <= c} INTER space a = {x | NegInf <= f x /\ f x <= c} INTER space a`
      by RW_TAC std_ss [le_infty]
  ++ METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7 = store_thm
("IN_MEASURABLE_BOREL_ALT7", ``!f a.  f IN measurable a Borel ==>
	           sigma_algebra a /\ f IN (space a -> UNIV) /\
		   !c d. ({x | c < f x /\ f x < d} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  << [METIS_TAC [IN_MEASURABLE_BOREL],
      METIS_TAC [IN_MEASURABLE_BOREL],
      `(!d. {x | f x < d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL]
      ++ `(!c. {x | c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
      ++ `{x | c < f x /\ f x < d} INTER space a =
      	  ({x | c < f x} INTER space a) INTER ({x | f x < d} INTER space a)`
          by (RW_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION] ++ METIS_TAC [])
      ++ METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, algebra_def, IN_MEASURABLE_BOREL]]);

val IN_MEASURABLE_BOREL_ALT8 = store_thm
  ("IN_MEASURABLE_BOREL_ALT8", ``!f a. f IN measurable a Borel ==>
		 sigma_algebra a /\ f IN (space a -> UNIV) /\
			 (!c. ({x| f x = c} INTER space a) IN subsets a)``,
  RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT6]
  ++ `{x | f x = c} = {x | c <= f x /\ f x <= c}`
      by RW_TAC std_ss [EXTENSION, GSPECIFICATION, le_antisym, EQ_SYM_EQ]
  ++ METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT9 = store_thm
  ("IN_MEASURABLE_BOREL_ALT9", ``!f a. f IN measurable a Borel ==>
		 sigma_algebra a /\ f IN (space a -> UNIV) /\
			 (!c. ({x| f x <> c} INTER space a) IN subsets a)``,
  RW_TAC std_ss [IN_FUNSET,IN_UNIV]
  >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
  ++ `{x | f x <> c} INTER space a = space a DIFF ({x | f x = c} INTER space a)`
      by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, GSPECIFICATION, IN_SING] ++ METIS_TAC [])
  ++ METIS_TAC [IN_MEASURABLE_BOREL, IN_MEASURABLE_BOREL_ALT8, sigma_algebra_def, algebra_def]);

val IN_MEASURABLE_BOREL_ALL = store_thm
  ("IN_MEASURABLE_BOREL_ALL",``!f a. f IN measurable a Borel  ==>
	(!c. {x | f x < c} INTER space a IN subsets a) /\
	(!c. {x | c <= f x} INTER space a IN subsets a) /\
	(!c. {x | f x <= c} INTER space a IN subsets a) /\
	(!c. {x | c < f x} INTER space a IN subsets a) /\
	(!c d. {x | c < f x /\ f x < d} INTER space a IN subsets a) /\
	(!c d. {x | c <= f x /\ f x < d} INTER space a IN subsets a) /\
	(!c d. {x | c < f x /\ f x <= d} INTER space a IN subsets a) /\
	(!c d. {x | c <= f x /\ f x <= d} INTER space a IN subsets a) /\
	(!c. {x | f x <> c} INTER space a IN subsets a) /\
	(!c. {x | f x = c} INTER space a IN subsets a)``,
  RW_TAC std_ss []
  ++ METIS_TAC [IN_MEASURABLE_BOREL, IN_MEASURABLE_BOREL_ALT1, IN_MEASURABLE_BOREL_ALT2,
                IN_MEASURABLE_BOREL_ALT3, IN_MEASURABLE_BOREL_ALT4, IN_MEASURABLE_BOREL_ALT5,
                IN_MEASURABLE_BOREL_ALT6, IN_MEASURABLE_BOREL_ALT7, IN_MEASURABLE_BOREL_ALT8,
                IN_MEASURABLE_BOREL_ALT9]);

val IN_MEASURABLE_BOREL_ALL_MEASURE = store_thm
  ("IN_MEASURABLE_BOREL_ALL_MEASURE",``!f m. f IN measurable (m_space m,measurable_sets m) Borel
     ==>
	(!c. {x | f x <  c} INTER m_space m IN measurable_sets m) /\
	(!c. {x | c <= f x} INTER m_space m IN measurable_sets m) /\
	(!c. {x | f x <= c} INTER m_space m IN measurable_sets m) /\
	(!c. {x |  c < f x} INTER m_space m IN measurable_sets m) /\
	(!c d. {x |  c < f x /\ f x <  d} INTER m_space m IN measurable_sets m) /\
	(!c d. {x | c <= f x /\ f x <  d} INTER m_space m IN measurable_sets m) /\
	(!c d. {x |  c < f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
	(!c d. {x | c <= f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
	(!c. {x | f x = c} INTER m_space m IN measurable_sets m) /\
	(!c. {x | f x <> c} INTER m_space m IN measurable_sets m)``,
  METIS_TAC [IN_MEASURABLE_BOREL_ALL, m_space_def, space_def, measurable_sets_def, subsets_def]);

val IN_MEASURABLE_BOREL_LT = store_thm
  ("IN_MEASURABLE_BOREL_LT", ``!f g a. f IN measurable a Borel /\ g IN measurable a Borel
           ==>  ({x | f x < g x} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  ++ `{x | f x < g x} INTER space a =
      BIGUNION (IMAGE (\r. {x | f x < r /\ r < g x} INTER space a) Q_set)`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_INTER]
            ++ EQ_TAC
	    >> RW_TAC std_ss [Q_DENSE_IN_R]
	    ++ METIS_TAC [lt_trans])
  ++ POP_ORW
  ++ MATCH_MP_TAC BIGUNION_IMAGE_Q
  ++ CONJ_TAC
  >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
  ++ RW_TAC std_ss [IN_FUNSET]
  ++ `{x | f x < r /\ r < g x} INTER space a =
     ({x | f x < r} INTER space a) INTER ({x | r < g x} INTER space a)`
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] ++ METIS_TAC [])
  ++ POP_ORW
  ++ MATCH_MP_TAC ALGEBRA_INTER
  ++ CONJ_TAC
  >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL, sigma_algebra_def]
  ++ `?c. r = Normal c` by METIS_TAC [rat_not_infty, extreal_cases]
  ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL]);

val IN_MEASURABLE_BOREL_LE = store_thm
  ("IN_MEASURABLE_BOREL_LE", ``!f g a. f IN measurable a Borel /\ g IN measurable a Borel ==>
		 ({x | f x <= g x} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  ++ `{x | f x <= g x} INTER space a = space a DIFF ({x | g x < f x} INTER space a)`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF]
          ++ METIS_TAC [extreal_lt_def])
  ++ `{x | g x < f x} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_LT]
  ++ METIS_TAC [algebra_def, IN_MEASURABLE_BOREL, sigma_algebra_def]);

val SPACE_BOREL = store_thm
  ("SPACE_BOREL", ``space Borel= UNIV``,
       METIS_TAC [Borel_def, sigma_def, space_def]);

val BOREL_MEASURABLE_SETS1 = store_thm
  ("BOREL_MEASURABLE_SETS1",``!c. {x | x < c} IN subsets Borel``,
  RW_TAC std_ss [Borel_def]
  ++ MATCH_MP_TAC IN_SIGMA
  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  ++ METIS_TAC []);

val BOREL_MEASURABLE_SETS2 = store_thm
  ("BOREL_MEASURABLE_SETS2",``!c. {x | c <= x} IN subsets Borel``,
  RW_TAC std_ss []
  ++ `{x | c <= x} = UNIV DIFF {x | x < c}`
      by RW_TAC std_ss [extreal_lt_def, EXTENSION, GSPECIFICATION, DIFF_DEF, IN_UNIV, real_lte]
  ++ METIS_TAC [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, sigma_algebra_def, algebra_def,
                BOREL_MEASURABLE_SETS1]);

val BOREL_MEASURABLE_SETS3 = store_thm
  ("BOREL_MEASURABLE_SETS3",``!c. {x | x <= c} IN subsets Borel``,
  RW_TAC std_ss []
  ++ ASSUME_TAC SIGMA_ALGEBRA_BOREL
  ++ (MP_TAC o UNDISCH o Q.SPEC `Borel`) (INST_TYPE [alpha |-> ``:extreal``]
         SIGMA_ALGEBRA_FN_BIGINTER)
  ++ RW_TAC std_ss []
  ++ Cases_on `c`
  << [`{x | x = NegInf} = BIGINTER (IMAGE (\n. {x | x < -(&n)}) UNIV)`
       by (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, GSPECIFICATION]
           ++ EQ_TAC >> METIS_TAC [num_not_infty, lt_infty, extreal_ainv_def, extreal_of_num_def]
	   ++ RW_TAC std_ss []
	   ++ SPOSE_NOT_THEN ASSUME_TAC
     	   ++ METIS_TAC [SIMP_EXTREAL_ARCH, extreal_lt_def, extreal_ainv_def, neg_neg, lt_neg])
      ++ RW_TAC std_ss [le_infty]
      ++ Q.PAT_ASSUM `!f. P ==> BIGINTER s IN subsets Borel` MATCH_MP_TAC
      ++ RW_TAC std_ss [IN_FUNSET,BOREL_MEASURABLE_SETS1],
      RW_TAC std_ss [le_infty,GSPEC_T,INTER_UNIV]
      ++ METIS_TAC [ALGEBRA_SPACE,SPACE_BOREL,sigma_algebra_def],
      `!c. {x | x <= Normal c} =
           BIGINTER (IMAGE (\n:num. {x | x < Normal (c + (1/2) pow n)}) UNIV)`
   	 by (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, IN_INTER]
   	     ++ EQ_TAC
             >> (RW_TAC std_ss [GSPECIFICATION]
                 ++ `0:real < (1/2) pow n` by RW_TAC real_ss [REAL_POW_LT]
		 ++ Cases_on `x = NegInf` >> METIS_TAC [lt_infty]
                 ++ `x <> PosInf` by METIS_TAC [le_infty, extreal_not_infty]
		 ++ `0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq, extreal_of_num_def]
		 ++ RW_TAC std_ss [GSYM extreal_add_def]
		 ++ METIS_TAC [extreal_of_num_def, extreal_not_infty, let_add2, add_rzero])
       	     ++ RW_TAC std_ss [GSPECIFICATION]
       	     ++ `!n. x < Normal (c + (1 / 2) pow n)` by METIS_TAC []
       	     ++ `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n) `
                   by RW_TAC real_ss [FUN_EQ_THM]
       	     ++ `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST]
       	     ++ `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
       	     ++ `(\n. c + (1 / 2) pow n) --> c`
                   by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`]
                      SEQ_ADD,REAL_ADD_RID]
	     ++ Cases_on `x = NegInf` >> RW_TAC std_ss [le_infty]
	     ++ `x <> PosInf` by METIS_TAC [lt_infty]
	     ++ `?r. x = Normal r` by METIS_TAC [extreal_cases]
	     ++ FULL_SIMP_TAC std_ss [extreal_le_def, extreal_lt_eq]
       	     ++ METIS_TAC [REAL_LT_IMP_LE,Q.SPECL [`r`,`c`,`(\n. c + (1 / 2) pow n)`]
                    LE_SEQ_IMP_LE_LIM])
  ++ POP_ORW
  ++ POP_ASSUM MATCH_MP_TAC
  ++ RW_TAC std_ss [IN_FUNSET,BOREL_MEASURABLE_SETS1]]);

val BOREL_MEASURABLE_SETS4 = store_thm
  ("BOREL_MEASURABLE_SETS4",``!c. {x | c < x} IN subsets Borel``,
  	RW_TAC std_ss []
	++ `{x | c < x} = UNIV DIFF {x | x <= c}`
             by RW_TAC std_ss [extreal_lt_def, EXTENSION, GSPECIFICATION, DIFF_DEF,
	     	       	       IN_UNIV, real_lte]
        ++ METIS_TAC [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, sigma_algebra_def, algebra_def,
                      BOREL_MEASURABLE_SETS3]);

val BOREL_MEASURABLE_SETS5 = store_thm
  ("BOREL_MEASURABLE_SETS5", ``!c d. {x | c <= x /\ x < d} IN subsets Borel``,
  RW_TAC std_ss []
  ++ `!d. {x | x < d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS1]
  ++ `!c. {x | c <= x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS2]
  ++ `{x | c <= x /\ x < d} = {x | c <= x} INTER {x | x < d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
  ++ METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS6 = store_thm
  ("BOREL_MEASURABLE_SETS6", ``!c d. {x | c < x /\ x <= d} IN subsets Borel``,
  RW_TAC std_ss []
  ++ `!d. {x | x <= d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS3]
  ++ `!c. {x | c < x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS4]
  ++ `{x | c < x /\ x <= d} = {x | c < x} INTER {x | x <= d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
  ++ METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS7 = store_thm
  ("BOREL_MEASURABLE_SETS7", ``!c d. {x | c <= x /\ x <= d} IN subsets Borel``,
  RW_TAC std_ss []
  ++ `!d. {x | x <= d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS3]
  ++ `!c. {x | c <= x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS2]
  ++ `{x | c <= x /\ x <= d} = {x | c <= x} INTER {x | x <= d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
  ++ METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS8 = store_thm
  ("BOREL_MEASURABLE_SETS8", ``!c d. {x | c < x /\ x < d} IN subsets Borel``,
  RW_TAC std_ss []
  ++ `!d. {x | x < d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS1]
  ++ `!c. {x | c < x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS4]
  ++ `{x | c < x /\ x < d} = {x | c < x} INTER {x | x < d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
  ++ METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS9 = store_thm
  ("BOREL_MEASURABLE_SETS9", ``!c. {c} IN subsets Borel``,
  RW_TAC std_ss []
  ++ `{c} = {x | c <= x /\ x <= c}` by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING,
                                                      le_antisym, EQ_SYM_EQ]
  ++ RW_TAC std_ss [BOREL_MEASURABLE_SETS7]);

val BOREL_MEASURABLE_SETS10 = store_thm
  ("BOREL_MEASURABLE_SETS10", ``!c. {x | x <> c} IN subsets Borel``,
  RW_TAC std_ss []
  ++ `{x | x <> c} = (space Borel) DIFF ({c})`
      by RW_TAC std_ss [SPACE_BOREL, EXTENSION, IN_DIFF, IN_SING, GSPECIFICATION, IN_UNIV]
  ++ METIS_TAC [SIGMA_ALGEBRA_BOREL, BOREL_MEASURABLE_SETS9, sigma_algebra_def, algebra_def]);

val BOREL_MEASURABLE_SETS = store_thm
  ("BOREL_MEASURABLE_SETS",
      ``((!c. {x | x < c} IN subsets Borel)) /\
	(!c. {x | c <= x} IN subsets Borel) /\
	(!c. {x | c < x} IN subsets Borel) /\
	(!c. {x | x <= c} IN subsets Borel) /\
	(!c d. {x | c < x /\ x < d} IN subsets Borel) /\
	(!c d. {x | c <= x /\ x < d} IN subsets Borel) /\
	(!c d. {x | c < x /\ x <= d} IN subsets Borel) /\
	(!c d. {x | c <= x /\ x <= d} IN subsets Borel) /\
	(!c. {c} IN subsets Borel) /\
	(!c. {x | x <> c} IN subsets Borel)``,
  RW_TAC std_ss [BOREL_MEASURABLE_SETS1, BOREL_MEASURABLE_SETS4,
    BOREL_MEASURABLE_SETS3, BOREL_MEASURABLE_SETS2,
    BOREL_MEASURABLE_SETS5, BOREL_MEASURABLE_SETS6,
    BOREL_MEASURABLE_SETS7, BOREL_MEASURABLE_SETS8,
    BOREL_MEASURABLE_SETS9, BOREL_MEASURABLE_SETS10]);


(* ******************************************* *)
(*        Borel measurable functions           *)
(* ******************************************* *)

val IN_MEASURABLE_BOREL_CONST = store_thm
  ("IN_MEASURABLE_BOREL_CONST",``!a k f. sigma_algebra a /\ (!x. x IN space a ==> (f x = k))
		 ==> f IN measurable a Borel``,
  RW_TAC std_ss [IN_MEASURABLE_BOREL,IN_FUNSET, IN_UNIV]
  ++ Cases_on `c <= k`
  >> (`{x | f x < c} INTER space a = {}`
         by  (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_INTER]
              ++ METIS_TAC [extreal_lt_def])
      ++ METIS_TAC [sigma_algebra_def, algebra_def])
  ++ `{x | f x < c} INTER space a = space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
          ++ METIS_TAC [extreal_lt_def])
  ++ METIS_TAC [sigma_algebra_def, algebra_def, INTER_IDEMPOT, DIFF_EMPTY]);

val IN_MEASURABLE_BOREL_INDICATOR = store_thm
  ("IN_MEASURABLE_BOREL_INDICATOR",``!a A f. sigma_algebra a /\ A IN subsets a /\
		(!x. x IN space a ==> (f x = (indicator_fn A x)))
		 ==> f IN measurable a Borel``,
  RW_TAC std_ss [IN_MEASURABLE_BOREL]
  >> RW_TAC std_ss [IN_FUNSET, UNIV_DEF, indicator_fn_def, IN_DEF]
  ++ `!x. x IN space a ==> 0 <= f x /\ f x <= 1`
      by RW_TAC real_ss [indicator_fn_def, le_01, le_refl]
  ++ Cases_on `c <= 0`
  >> (`{x | f x < c} INTER space a = {}`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_INTER, extreal_lt_def]
	  ++ METIS_TAC [le_trans])
      ++ METIS_TAC [sigma_algebra_def, algebra_def, DIFF_EMPTY])
  ++ Cases_on `1 < c`
  >> (`{x | f x < c} INTER space a = space a`
	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_INTER]
	    ++ METIS_TAC [let_trans])
      ++ METIS_TAC [sigma_algebra_def, algebra_def, DIFF_EMPTY])
  ++ `{x | f x < c} INTER space a = (space a) DIFF A`
	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF]
	    ++ FULL_SIMP_TAC std_ss [extreal_lt_def, indicator_fn_def]
	    ++ METIS_TAC [extreal_lt_def])
  ++ METIS_TAC [sigma_algebra_def, algebra_def, DIFF_EMPTY]);

val IN_MEASURABLE_BOREL_CMUL = store_thm
  ("IN_MEASURABLE_BOREL_CMUL",``!a f g z. sigma_algebra a /\ f IN measurable a Borel /\
	    (!x. x IN space a ==> (g x = Normal (z) * f x))
	                 ==> g IN measurable a Borel``,
  RW_TAC std_ss []
  ++ Cases_on `Normal z = 0`
  >> METIS_TAC [IN_MEASURABLE_BOREL_CONST,mul_lzero]
  ++ Cases_on `0 < Normal z`
  >> (RW_TAC real_ss [IN_MEASURABLE_BOREL,IN_FUNSET,IN_UNIV]
      ++ `!c. {x | g x < c} INTER space a = {x | f x < c / Normal z} INTER space a`
           by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
	       ++ METIS_TAC [lt_rdiv, mul_comm, extreal_of_num_def, extreal_lt_eq])
      ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, extreal_div_eq, extreal_of_num_def, extreal_11])
  ++ `z < 0` by METIS_TAC [extreal_lt_def, extreal_le_def, extreal_of_num_def,
     	     		   REAL_LT_LE, GSYM real_lte]
  ++ RW_TAC real_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
  ++ `!c. {x | g x < c} INTER space a = {x | c / Normal z < f x} INTER space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
          ++ METIS_TAC [lt_rdiv_neg, mul_comm])
  ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL]);

val IN_MEASURABLE_BOREL_ABS = store_thm
  ("IN_MEASURABLE_BOREL_ABS",``!a f g. (sigma_algebra a) /\ f IN measurable a Borel /\
	(!x. x IN space a ==> (g x = abs (f x)))
	 ==> g IN measurable a Borel``,
  RW_TAC real_ss [IN_MEASURABLE_BOREL, IN_UNIV, IN_FUNSET]
  ++ Cases_on `c <= 0`
  >> (`{x | g x < c} INTER space a = {}`
	  by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, NOT_IN_EMPTY, GSYM real_lte]
	      ++ METIS_TAC [abs_pos,le_trans, extreal_le_def, extreal_of_num_def, extreal_lt_def])
      ++ METIS_TAC [sigma_algebra_def, algebra_def])
  ++ FULL_SIMP_TAC real_ss [GSYM real_lt]
  ++ Suff `{x | g x < c} INTER space a =
          ({x | f x < c} INTER space a) INTER ({x | -c < f x} INTER space a)`
  >> (RW_TAC std_ss []
      ++ MATCH_MP_TAC ALGEBRA_INTER
      ++ METIS_TAC [sigma_algebra_def, IN_MEASURABLE_BOREL_ALL, IN_MEASURABLE_BOREL, IN_FUNSET,
      	 	    IN_UNIV])
  ++ RW_TAC real_ss [EXTENSION, GSPECIFICATION, IN_INTER]
  ++ EQ_TAC
  >> METIS_TAC [abs_bounds_lt]
  ++ METIS_TAC [abs_bounds_lt]);

val IN_MEASURABLE_BOREL_SQR = store_thm
  ("IN_MEASURABLE_BOREL_SQR",``!a f g. sigma_algebra a /\ f IN measurable a Borel /\
	(!x. x IN space a ==> (g x = (f x) pow 2))
	==> g IN measurable a Borel``,
  RW_TAC real_ss []
  ++ `!c. {x | f x <= c} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
  ++ `!c. {x | c <= f x} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
  ++ RW_TAC real_ss [IN_UNIV, IN_FUNSET, IN_MEASURABLE_BOREL_ALT2]
  ++ Cases_on `c < 0`
  >> (`{x | g x <= c} INTER space a = {}`
  	by ( RW_TAC real_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_INTER, GSYM real_lt]
	     ++ METIS_TAC [le_pow2, lte_trans, extreal_lt_def])
      ++ METIS_TAC [sigma_algebra_def, algebra_def])
  ++ FULL_SIMP_TAC real_ss [extreal_lt_def]
  ++ `{x | g x <= c} INTER space a =
     ({x | f x <= sqrt (c)} INTER space a) INTER ({x | - (sqrt (c)) <= f x} INTER space a)`
	by (RW_TAC real_ss [EXTENSION, GSPECIFICATION, IN_INTER]
	    ++ EQ_TAC
	    >> (RW_TAC real_ss []
		>> (Cases_on `f x < 0` >> METIS_TAC [lte_trans, lt_imp_le, sqrt_pos_le]
     		    ++ METIS_TAC [pow2_sqrt, sqrt_mono_le, le_pow2, extreal_lt_def])
     		++ Cases_on `0 <= f x` >> METIS_TAC [le_trans, le_neg, sqrt_pos_le, neg_0]
		++ SPOSE_NOT_THEN ASSUME_TAC
		++ FULL_SIMP_TAC real_ss [GSYM extreal_lt_def]
		++ `sqrt c < - (f x)` by METIS_TAC [lt_neg, neg_neg]
		++ `(sqrt c) pow 2 < (- (f x)) pow 2` by RW_TAC real_ss [pow_lt2, sqrt_pos_le]
		++ `(sqrt c) pow 2 = c` by METIS_TAC [sqrt_pow2]
                ++ `(-1) pow 2 = 1` by METIS_TAC [pow_minus1, MULT_RIGHT_1]
		++ `(- (f x)) pow 2 = (f x) pow 2`
		    by RW_TAC std_ss [Once neg_minus1, pow_mul, mul_lone]
		++ METIS_TAC [extreal_lt_def])
	    ++ RW_TAC std_ss []
	    ++ Cases_on `0 <= f x` >> METIS_TAC [pow_le, sqrt_pow2]
	    ++ FULL_SIMP_TAC real_ss [GSYM extreal_lt_def]
	    ++ `- (f x) <= sqrt c` by METIS_TAC [le_neg, neg_neg]
	    ++ `(- (f x)) pow 2 <= (sqrt c) pow 2`
	        by METIS_TAC [pow_le, sqrt_pos_le, lt_neg, neg_neg, neg_0, lt_imp_le]
	    ++ `(sqrt c) pow 2 = c` by METIS_TAC [sqrt_pow2]
            ++ `(-1) pow 2 = 1` by METIS_TAC [pow_minus1,MULT_RIGHT_1]
	    ++ `(- (f x)) pow 2 = (f x) pow 2`
	        by RW_TAC std_ss [Once neg_minus1, pow_mul, mul_lone]
	    ++ METIS_TAC [])
  ++ METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, extreal_sqrt_def, extreal_ainv_def]);

val IN_MEASURABLE_BOREL_ADD = store_thm
  ("IN_MEASURABLE_BOREL_ADD",``!a f g h. sigma_algebra a /\ f IN measurable a Borel /\
	g IN measurable a Borel /\
        (!x. x IN space a ==> (h x = f x + g x)) ==> h IN measurable a Borel``,
  REPEAT STRIP_TAC
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL] >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
  ++ Cases_on `c = NegInf`
  >> (RW_TAC std_ss [lt_infty,GSPEC_F,INTER_EMPTY] ++ METIS_TAC [sigma_algebra_def, algebra_def])
  ++ Cases_on `c = PosInf`
  >> (RW_TAC std_ss [GSYM lt_infty]
      ++ `{x | h x <> PosInf} INTER space a =
          ({x | f x <> PosInf} INTER space a) INTER ({x | g x <> PosInf} INTER space a)`
          by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
	      ++ EQ_TAC >> METIS_TAC [add_infty]
  	      ++ RW_TAC std_ss []
	      ++ Cases_on `f x` ++ Cases_on `g x`
	      ++ METIS_TAC [extreal_add_def, extreal_not_infty])
      ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, ALGEBRA_INTER, sigma_algebra_def])
  ++ `?r1. c = Normal r1` by METIS_TAC [extreal_cases]
  ++ `{x | h x < Normal r1} INTER (space a) =
      BIGUNION (IMAGE (\r. {x | f x < r /\ r < Normal r1 - g x } INTER space a) Q_set)`
	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER]
	    ++ EQ_TAC
	    >> (RW_TAC std_ss []
	        ++ METIS_TAC [lt_sub_imp, Q_DENSE_IN_R])
	    ++ REVERSE (RW_TAC std_ss [])
	    >> METIS_TAC []
	    ++ METIS_TAC [lt_sub,lt_trans, extreal_not_infty])
  ++ FULL_SIMP_TAC std_ss []
  ++ MATCH_MP_TAC BIGUNION_IMAGE_Q
  ++ RW_TAC std_ss [IN_FUNSET]
  ++ `?y. r = Normal y` by METIS_TAC [Q_not_infty, extreal_cases]
  ++ `{x | f x < Normal y /\ Normal y < Normal r1 - g x} =
      {x | f x < Normal y} INTER {x | Normal y < Normal r1 - g x}`
       by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
  ++ `({x | f x < Normal y} INTER space a) IN subsets a`
      by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
  ++ `!x. x IN space a ==> ((Normal y < Normal r1 - g x) = (g x < Normal r1 - Normal y))`
        by METIS_TAC [lt_sub, extreal_not_infty, add_comm]
  ++ `{x | Normal y < Normal r1 - g x} INTER space a =
      {x | g x < Normal r1 - Normal y} INTER space a`
       by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION]
           ++ METIS_TAC [])
  ++ `({x | Normal y < Normal r1 - g x} INTER space a) IN subsets a`
      by METIS_TAC [IN_MEASURABLE_BOREL_ALL, extreal_sub_def]
  ++ `(({x | f x < Normal y} INTER space a) INTER
      ({x | Normal y < Normal r1 - g x} INTER space a)) =
      ({x | f x < Normal y} INTER {x | Normal y < Normal r1 - g x} INTER space a)`
	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
	    ++ EQ_TAC >> RW_TAC std_ss []
	    ++ RW_TAC std_ss [])
  ++ METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val IN_MEASURABLE_BOREL_SUB = store_thm
  ("IN_MEASURABLE_BOREL_SUB",``!a f g h. sigma_algebra a /\ f IN measurable a Borel /\
	g IN measurable a Borel  /\
        (!x. x IN space a ==> (h x = f x - g x)) ==> h IN measurable a Borel``,
  RW_TAC std_ss []
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
  ++ Q.EXISTS_TAC `f`
  ++ Q.EXISTS_TAC `(\x. - g x)`
  ++ RW_TAC std_ss [extreal_sub_add]
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
  ++ Q.EXISTS_TAC `g`
  ++ Q.EXISTS_TAC `-1`
  ++ RW_TAC std_ss [GSYM extreal_ainv_def, GSYM extreal_of_num_def, GSYM neg_minus1]);

val IN_MEASURABLE_BOREL_MUL = store_thm
  ("IN_MEASURABLE_BOREL_MUL",``!a f g h. sigma_algebra a /\ f IN measurable a Borel  /\
                (!x. x IN space a ==> f x <> NegInf /\ f x <> PosInf /\
		       	  	      g x <> NegInf /\ g x <> PosInf) /\
		g IN measurable a Borel /\ (!x. x IN space a ==> (h x = f x * g x))
		==> h IN measurable a Borel``,
  RW_TAC std_ss []
  ++ `!x. x IN space a ==> (f x * g x = 1 / 2 * ((f x + g x) pow 2 - f x pow 2 - g x pow 2))`
	by (RW_TAC std_ss []
	    ++ (MP_TAC o Q.SPECL [`f x`, `g x`]) add_pow2
	    ++ RW_TAC std_ss []
	    ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
	    ++ `?r. g x = Normal r` by METIS_TAC [extreal_cases]
	    ++ FULL_SIMP_TAC real_ss [extreal_11, extreal_pow_def, extreal_add_def,
	       		     	      extreal_sub_def, extreal_of_num_def, extreal_mul_def,
				      extreal_div_eq]
	    ++ `r pow 2 + r' pow 2 + 2 * r * r' - r pow 2 - r' pow 2 = 2 * r * r'`
	        by REAL_ARITH_TAC
	    ++ RW_TAC real_ss [REAL_MUL_ASSOC])
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
  ++ Q.EXISTS_TAC `(\x. (f x + g x) pow 2 - f x pow 2 - g x pow 2)`
  ++ Q.EXISTS_TAC `1 / 2`
  ++ RW_TAC real_ss [extreal_of_num_def, extreal_div_eq]
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
  ++ Q.EXISTS_TAC `(\x. (f x + g x) pow 2 - f x pow 2)`
  ++ Q.EXISTS_TAC `(\x. g x pow 2)`
  ++ RW_TAC std_ss []
     >>(MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
        ++ Q.EXISTS_TAC `(\x. (f x + g x) pow 2)`
        ++ Q.EXISTS_TAC `(\x. f x pow 2)`
        ++ RW_TAC std_ss []
        >> (MATCH_MP_TAC IN_MEASURABLE_BOREL_SQR
	    ++ Q.EXISTS_TAC `(\x. (f x + g x))`
	    ++ RW_TAC std_ss []
	    ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
	    ++ Q.EXISTS_TAC `f`
	    ++ Q.EXISTS_TAC `g`
	    ++ RW_TAC std_ss [])
	++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SQR
	++ METIS_TAC [])
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SQR
  ++ METIS_TAC []);

val IN_MEASURABLE_BOREL_SUM = store_thm
  ("IN_MEASURABLE_BOREL_SUM",``!a f g s. FINITE s /\ sigma_algebra a /\
				(!i. i IN s ==> (f i) IN measurable a Borel) /\
				(!x. x IN space a ==> (g x = SIGMA (\i. (f i) x) s))
				 ==> g IN measurable a Borel``,
	Suff `!s:'b -> bool. FINITE s ==> (\s:'b -> bool. !a f g. FINITE s /\ sigma_algebra a /\
		(!i. i IN s ==> f i IN measurable a Borel) /\
		(!x. x IN space a ==> (g x = SIGMA (\i. f i x) s)) ==>
	           g IN measurable a Borel) s`
	>> METIS_TAC []
	++ MATCH_MP_TAC FINITE_INDUCT
	++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, NOT_IN_EMPTY]
	>> METIS_TAC [IN_MEASURABLE_BOREL_CONST]
  ++ FULL_SIMP_TAC std_ss []
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
  ++ Q.EXISTS_TAC `f e`
  ++ Q.EXISTS_TAC `(\x. SIGMA (\i. f i x) s)`
  ++ FULL_SIMP_TAC std_ss [IN_INSERT, DELETE_NON_ELEMENT]
  ++ Q.PAT_ASSUM `!a f g. P ==> g IN measurable a Borel` MATCH_MP_TAC
  ++ Q.EXISTS_TAC `f`
  ++ RW_TAC std_ss []);

val IN_MEASURABLE_BOREL_CMUL_INDICATOR = store_thm
  ("IN_MEASURABLE_BOREL_CMUL_INDICATOR",``!a z s. sigma_algebra a /\ s IN subsets a
      ==> (\x. Normal z * indicator_fn s x) IN measurable a Borel``,
  RW_TAC std_ss []
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
  ++ Q.EXISTS_TAC `indicator_fn s`
  ++ Q.EXISTS_TAC `z`
  ++ RW_TAC std_ss []
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
  ++ METIS_TAC []);

val IN_MEASURABLE_BOREL_MUL_INDICATOR = store_thm
  ("IN_MEASURABLE_BOREL_MUL_INDICATOR",``!a f s. sigma_algebra a /\ f IN measurable a Borel /\
	s IN subsets a ==> (\x. f x * indicator_fn s x) IN measurable a Borel``,
  RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2, IN_FUNSET, IN_UNIV]
  ++ Cases_on `0 <= c`
  >> (`{x | f x * indicator_fn s x <= c} INTER space a =
     (({x | f x <= c} INTER space a) INTER s) UNION (space a DIFF s)`
         by (RW_TAC std_ss [indicator_fn_def, EXTENSION, GSPECIFICATION, IN_INTER,
	    	    	    IN_UNION, IN_DIFF]
	     ++ Cases_on `x IN s` >> RW_TAC std_ss [mul_rone, mul_rzero]
	     ++ RW_TAC std_ss [mul_rone, mul_rzero])
      ++ POP_ORW
      ++ MATCH_MP_TAC ALGEBRA_UNION
      ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [sigma_algebra_def]
      ++ REVERSE CONJ_TAC >> FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def]
      ++ MATCH_MP_TAC ALGEBRA_INTER
      ++ FULL_SIMP_TAC std_ss [sigma_algebra_def])
  ++ `{x | f x * indicator_fn s x <= c} INTER space a = (({x | f x <= c} INTER space a) INTER s)`
         by (RW_TAC std_ss [indicator_fn_def, EXTENSION, GSPECIFICATION, IN_INTER]
	     ++ Cases_on `x IN s` >> RW_TAC std_ss [mul_rone, mul_rzero]
	     ++ RW_TAC std_ss [mul_rone, mul_rzero])
  ++ POP_ORW
  ++ MATCH_MP_TAC ALGEBRA_INTER
  ++ FULL_SIMP_TAC std_ss [sigma_algebra_def]);

val IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ = store_thm
  ("IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ",``!a f. sigma_algebra a ==>
         (f IN measurable a Borel = (\x. f x * indicator_fn (space a) x) IN measurable a Borel)``,
  RW_TAC std_ss []
  ++ EQ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, ALGEBRA_SPACE, sigma_algebra_def]
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_UNIV, IN_FUNSET]
  ++ `{x | f x < c} INTER space a = {x | f x * indicator_fn (space a) x < c} INTER space a`
       by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION, indicator_fn_def,
       	  	  	  mul_rzero, mul_rone]
           ++ METIS_TAC [mul_rzero, mul_rone])
  ++ RW_TAC std_ss []);


val IN_MEASURABLE_BOREL_POS_SIMPLE_FN = store_thm
  ("IN_MEASURABLE_BOREL_POS_SIMPLE_FN",``!m f. measure_space m /\
  					       (?s a x. pos_simple_fn m f s a x)
				 ==> f IN measurable (m_space m,measurable_sets m) Borel``,
  RW_TAC std_ss [pos_simple_fn_def]
  ++ `!i. i IN s ==> indicator_fn (a i) IN measurable (m_space m,measurable_sets m) Borel`
	by METIS_TAC [IN_MEASURABLE_BOREL_INDICATOR, measurable_sets_def, subsets_def,
	   	      m_space_def, measure_space_def]
  ++ `!i x. i IN s ==> (\t. Normal (x i) * indicator_fn (a i) t)
     	 IN measurable (m_space m, measurable_sets m) Borel`
	by (RW_TAC std_ss []
	    ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
	    ++ Q.EXISTS_TAC `indicator_fn (a i)`
	    ++ Q.EXISTS_TAC `x' i`
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [measure_space_def])
  ++ MATCH_MP_TAC (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM)
  ++ Q.EXISTS_TAC `(\i. (\t. Normal (x i) * indicator_fn (a i) t))`
  ++ Q.EXISTS_TAC `s`
  ++ RW_TAC std_ss [space_def]
  >> METIS_TAC [measure_space_def]
  ++ RW_TAC real_ss [indicator_fn_def,mul_rzero,mul_rone]
  ++ RW_TAC std_ss [extreal_of_num_def]);

val IN_MEASURABLE_BOREL_POW = store_thm
  ("IN_MEASURABLE_BOREL_POW",``!n a f. sigma_algebra a /\
    f IN measurable a Borel /\ (!x. x IN space a ==> f x <> NegInf /\ f x <> PosInf)
     ==> (\x. (f x) pow n) IN measurable a Borel``,
  Induct >> (RW_TAC std_ss [pow_0]
	     ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST
	     ++ METIS_TAC [])
  ++ RW_TAC std_ss []
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL
  ++ Q.EXISTS_TAC `f`
  ++ Q.EXISTS_TAC `(\x. f x pow n)`
  ++ RW_TAC std_ss [pow_not_infty]
  ++ METIS_TAC [pow_add,ADD1,pow_1,mul_comm]);

val IN_MEASURABLE_BOREL_MAX = store_thm
  ("IN_MEASURABLE_BOREL_MAX",``!a f g. sigma_algebra a /\
  				       f IN measurable a Borel /\ g IN measurable a Borel
                    ==> (\x. max (f x) (g x)) IN measurable a Borel``,
  RW_TAC std_ss [IN_MEASURABLE_BOREL,extreal_max_def,IN_FUNSET, IN_UNIV]
  ++ `!c. {x | (if f x <= g x then g x else f x) < c} = {x | f x < c} INTER {x | g x < c}`
	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
	    ++ EQ_TAC
            >> (RW_TAC std_ss []
                >> METIS_TAC [let_trans]
                ++ METIS_TAC [extreal_lt_def, lt_trans])
	     ++ METIS_TAC [extreal_lt_def, lt_trans])
  ++ `!c. {x | (if f x <= g x then g x else f x) < c} INTER space a =
          ({x | f x < c} INTER space a) INTER ({x | g x < c} INTER space a)`
	  by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
  ++ METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val IN_MEASURABLE_BOREL_MONO_SUP = store_thm
  ("IN_MEASURABLE_BOREL_MONO_SUP",``!fn f a. (sigma_algebra a /\
  					      (!n:num. fn n IN measurable a Borel) /\
					      (!n x. x IN space a ==> fn n x <= fn (SUC n) x) /\
					      (!x. x IN space a ==>
					      	   (f x = sup (IMAGE (\n. fn n x) UNIV))))
			==> f IN measurable a Borel``,
   RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2,IN_FUNSET,IN_UNIV]
   ++ `{x | sup (IMAGE (\n. fn n x) UNIV) <= c} INTER space a =
       BIGINTER (IMAGE (\n. {x | fn n x <= c} INTER space a) UNIV)`
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGINTER_IMAGE, IN_UNIV, IN_INTER, sup_le]
		++ EQ_TAC
                >> (RW_TAC std_ss []
	            ++ Q.PAT_ASSUM `!y. P y ==> y <= c` MATCH_MP_TAC
		    ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
		    ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
		    ++ METIS_TAC [])
		++ RW_TAC std_ss []
		++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
		++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
		++ METIS_TAC [])
    ++ `{x | f x <= c} INTER space a = {x | sup (IMAGE (\n. fn n x) UNIV) <= c} INTER space a`
         by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] ++ METIS_TAC [])
    ++ `!c. BIGINTER (IMAGE (\n. {x | fn n x <= c} INTER (space a)) UNIV) IN subsets a`
        by (RW_TAC std_ss []
	    ++ (MP_TAC o Q.SPEC `(space a,subsets a)`) SIGMA_ALGEBRA_FN_BIGINTER
	    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, space_def, subsets_def, SPACE])
    ++ METIS_TAC []);

val fn_plus_def = Define `fn_plus f = (\x. if 0 < f x then f x else 0)`;

val fn_minus_def = Define `fn_minus f = (\x. if f x < 0 then ~ f x else 0)`;

val fn_abs_def = Define `fn_abs f = (\x. abs (f x))`;

val FN_PLUS_POS = store_thm
  ("FN_PLUS_POS",``!g x. 0 <= (fn_plus g) x``,
  RW_TAC real_ss [fn_plus_def, FUN_EQ_THM, lt_imp_le, le_refl]);

val FN_MINUS_POS = store_thm
  ("FN_MINUS_POS",``!g x. 0 <= (fn_minus g) x``,
  RW_TAC real_ss [fn_minus_def, FUN_EQ_THM, le_refl]
  ++ METIS_TAC [le_neg, lt_imp_le, neg_0]);

val FN_PLUS_POS_ID = store_thm
  ("FN_PLUS_POS_ID",``(!x. 0 <= g x) ==> ((fn_plus g) = g)``,
  RW_TAC real_ss [fn_plus_def,FUN_EQ_THM]
  ++ Cases_on `g x = 0` >> METIS_TAC []
  ++ METIS_TAC [le_lt]);

val FN_MINUS_POS_ZERO = store_thm
  ("FN_MINUS_POS_ZERO",``(!x. 0 <= g x) ==> ((fn_minus g) = (\x. 0))``,
  RW_TAC real_ss [fn_minus_def,FUN_EQ_THM]
  ++ Cases_on `g x = 0` >> METIS_TAC [neg_0]
  ++ `0 < g x` by METIS_TAC [lt_le]
  ++ METIS_TAC [extreal_lt_def]);

val FN_PLUS_CMUL = store_thm
  ("FN_PLUS_CMUL",``!f c. (0 <= c ==> (fn_plus (\x. Normal c * f x) =
  		       	     	      (\x. Normal c * fn_plus f x))) /\
                          (c <= 0 ==> (fn_plus (\x. Normal c * f x) =
			     	      (\x. -Normal c * fn_minus f x)))``,

  RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
  >> (Cases_on `0 < f x`
      >> METIS_TAC [let_mul, extreal_of_num_def, extreal_le_def, extreal_lt_def, le_antisym]
      ++ RW_TAC std_ss [mul_rzero]
      ++ METIS_TAC [mul_le, extreal_lt_def, extreal_le_def, extreal_of_num_def, lt_imp_le,
      	 	    le_antisym])
  ++ RW_TAC std_ss [mul_rzero, neg_mul2]
  >> METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
     	        le_antisym, mul_comm]
  ++ METIS_TAC [le_mul_neg, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
     	        le_antisym]);

val FN_MINUS_CMUL = store_thm
  ("FN_MINUS_CMUL",``!f c. (0 <= c ==> (fn_minus (\x. Normal c * f x) =
  			      	       (\x. Normal c * fn_minus f x))) /\
                         (c <= 0 ==> (fn_minus (\x. Normal c * f x) =
			       	     (\x. -Normal c * fn_plus f x)))``,
  RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
  >> (RW_TAC std_ss [mul_rzero, mul_rneg, neg_eq0]
      >> METIS_TAC [le_mul, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
      	 	    le_antisym]
      ++ METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
      	 	    le_antisym, neg_eq0])
  ++ RW_TAC std_ss [mul_rzero, neg_eq0, mul_lneg, neg_0]
  >> METIS_TAC [le_mul_neg, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
     	        le_antisym]
  ++ METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
     	        le_antisym, neg_eq0, mul_comm]);

val FN_PLUS_ADD_LE = store_thm
("FN_PLUS_ADD_LE", ``!f g x. fn_plus (\x. f x + g x) x <= (fn_plus f x) + (fn_plus g x)``,
    RW_TAC real_ss[fn_plus_def, add_rzero, add_lzero, le_refl, le_add2]
    ++ METIS_TAC [le_refl, extreal_lt_def, le_add2, add_lzero, add_rzero, lt_imp_le]);

val FN_MINUS_ADD_LE = store_thm
  ("FN_MINUS_ADD_LE", ``!f g x. fn_minus (\x. f x + g x) x <= (fn_minus f x) + (fn_minus g x)``,
    RW_TAC real_ss[fn_minus_def, add_rzero, add_lzero, le_refl, le_add2]
    << [Cases_on `f x` ++ Cases_on `g x`
        ++ RW_TAC std_ss [extreal_add_def, extreal_sub_def, extreal_ainv_def, lt_infty,
	   	  	  num_not_infty, lte_trans, le_refl, le_infty, extreal_le_def]
	++ REAL_ARITH_TAC,
	(Cases_on `f x` ++ Cases_on `g x`
        ++ RW_TAC std_ss [extreal_add_def, extreal_sub_def, extreal_ainv_def, lt_infty,
	   	  	  num_not_infty, lte_trans, le_refl, le_infty, extreal_le_def])
	>> METIS_TAC [lt_infty]
	++ FULL_SIMP_TAC std_ss [extreal_of_num_def, extreal_lt_eq, extreal_le_def,
	   		 	 extreal_add_def, REAL_LE_NEG, GSYM real_lte]
	++ METIS_TAC [REAL_LE_REFL, REAL_LE_ADD2, REAL_ADD_RID],
	(Cases_on `f x` ++ Cases_on `g x`
        ++ RW_TAC std_ss [extreal_add_def, extreal_sub_def, extreal_ainv_def, lt_infty,
	   	  	  num_not_infty, lte_trans, le_refl, le_infty, extreal_le_def])
	>> METIS_TAC [lt_infty]
	++ FULL_SIMP_TAC std_ss [extreal_of_num_def, extreal_lt_eq, extreal_le_def,
	   		 	 extreal_add_def, REAL_LE_NEG, GSYM real_lte]
	++ METIS_TAC [REAL_LE_REFL, REAL_LE_ADD2, REAL_ADD_LID],
	METIS_TAC [extreal_lt_def, le_add2, add_rzero],
	METIS_TAC [lt_neg,le_add2, add_rzero, neg_0, lt_imp_le],
	METIS_TAC [lt_neg, neg_0, lt_imp_le],
	METIS_TAC [lt_neg, neg_0, lt_imp_le]]);

val IN_MEASURABLE_BOREL_FN_PLUS = store_thm
  ("IN_MEASURABLE_BOREL_FN_PLUS",``!a f. f IN measurable a Borel
                ==> fn_plus f IN measurable a Borel``,
  RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV, fn_plus_def]
  ++ Cases_on `c <= 0`
  >> (`{x | (if 0 < f x then f x else 0) < c} = {}`
    	by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]
	    ++ `!x. 0 <= (if 0 < f x then f x else 0)` by RW_TAC real_ss [lt_imp_le, le_refl]
	    ++ METIS_TAC [le_trans, extreal_lt_def, extreal_of_num_def, extreal_le_def])
      ++ METIS_TAC [sigma_algebra_def, algebra_def, INTER_EMPTY])
  ++ `{x | (if 0 < f x then f x else 0) < c} = {x | f x < c}`
	by (RW_TAC real_ss [EXTENSION, GSPECIFICATION]
   	    ++ EQ_TAC
            >> (RW_TAC real_ss []
                ++ METIS_TAC [extreal_lt_def, let_trans])
	    ++ RW_TAC real_ss []
	    ++ METIS_TAC [extreal_lt_def])
  ++ METIS_TAC []);

val IN_MEASURABLE_BOREL_FN_MINUS = store_thm
  ("IN_MEASURABLE_BOREL_FN_MINUS",``!a f. f IN measurable a Borel
            ==> fn_minus f IN measurable a Borel``,
  RW_TAC std_ss [fn_minus_def]
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV, fn_minus_def]
  >> METIS_TAC [IN_MEASURABLE_BOREL]
  ++ Cases_on `c <= 0`
	>> (`{x | (if f x < 0 then -f x else 0) < c} = {}`
		by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]
		    ++ `!x. 0 <= (if f x < 0 then -f x else 0)`
			by (RW_TAC real_ss [le_refl]
                            ++ METIS_TAC [lt_neg, neg_0, lt_imp_le])
		    ++ METIS_TAC [extreal_of_num_def, extreal_le_def, le_trans, extreal_lt_def])
	    ++ METIS_TAC [sigma_algebra_def, algebra_def, INTER_EMPTY, IN_MEASURABLE_BOREL])
  ++ `{x | (if f x < 0 then -f x else 0) < c} = {x | -c < f x}`
	by (RW_TAC real_ss [EXTENSION, GSPECIFICATION]
   	    ++ EQ_TAC
            >> (RW_TAC std_ss []
		>> METIS_TAC [lt_neg, neg_neg]
		++ METIS_TAC [lt_neg, neg_neg, neg_0, extreal_lt_def, lte_trans,
		   	      lt_imp_le, extreal_ainv_def])
	    ++ RW_TAC std_ss []
	    >> METIS_TAC [lt_neg, neg_neg]
	    ++ METIS_TAC [lt_neg, neg_neg,neg_0, extreal_lt_def, lte_trans, lt_imp_le,
	       		  extreal_ainv_def])
  ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL]);

val IN_MEASURABLE_BOREL_PLUS_MINUS = store_thm
  ("IN_MEASURABLE_BOREL_PLUS_MINUS",``!a f. f IN measurable a Borel =
                         (fn_plus f IN measurable a Borel /\ fn_minus f IN measurable a Borel)``,
  RW_TAC std_ss []
  ++ EQ_TAC >> RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, IN_MEASURABLE_BOREL_FN_MINUS]
  ++ RW_TAC std_ss []
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
  ++ Q.EXISTS_TAC `fn_plus f`
  ++ Q.EXISTS_TAC `fn_minus f`
  ++ RW_TAC std_ss [fn_plus_def, fn_minus_def, sub_rzero,lt_antisym, sub_rzero, add_lzero]
  ++ METIS_TAC [IN_MEASURABLE_BOREL, lt_antisym, sub_rneg, add_lzero,extreal_lt_def, le_antisym]);

val INDICATOR_FN_MUL_INTER = store_thm
  ("INDICATOR_FN_MUL_INTER",``!A B. (\t. (indicator_fn A t) * (indicator_fn B t)) =
  				    (\t. indicator_fn (A INTER B) t)``,
  RW_TAC std_ss [FUN_EQ_THM]
  ++ `(indicator_fn (A INTER B) t= (if t IN (A INTER B) then 1 else 0))`
      by METIS_TAC [indicator_fn_def]
  ++ RW_TAC std_ss [indicator_fn_def, mul_lone, IN_INTER, mul_lzero]
  ++ FULL_SIMP_TAC real_ss []);

val indicator_fn_split = store_thm
  ("indicator_fn_split", ``!(r:num->bool) s (b:num->('a->bool)). FINITE r /\
	(BIGUNION (IMAGE b r) = s) /\
        (!i j. i IN r /\ j IN r /\ (~(i=j)) ==> DISJOINT (b i) (b j)) ==>
     !a. a SUBSET s ==> ((indicator_fn a) =
     	   	    	 (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))``,
   Suff `!r. FINITE r ==>
		(\r. !s (b:num->('a->bool)).
	FINITE r /\
	(BIGUNION (IMAGE b r) = s) /\
	     (!i j. i IN r /\ j IN r /\ (~(i=j)) ==> DISJOINT (b i) (b j)) ==>
	     !a. a SUBSET s ==>
		 ((indicator_fn a) =
		  (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))) r`
   >> METIS_TAC []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, IMAGE_EMPTY, BIGUNION_EMPTY,
                     SUBSET_EMPTY, indicator_fn_def, NOT_IN_EMPTY,
                     FINITE_INSERT, IMAGE_INSERT, DELETE_NON_ELEMENT,
                     IN_INSERT, BIGUNION_INSERT]
   ++ Q.PAT_ASSUM `!b. P ==> !a. Q ==> (x = y)`
	(MP_TAC o Q.ISPEC `(b :num -> 'a -> bool)`)
   ++ RW_TAC std_ss [SUBSET_DEF]
   ++ POP_ASSUM (MP_TAC o Q.ISPEC `a DIFF ((b :num -> 'a -> bool) e)`)
   ++ Know `(!x. x IN a DIFF b e ==> x IN BIGUNION (IMAGE b s))`
   >> METIS_TAC [SUBSET_DEF, IN_UNION, IN_DIFF]
   ++ RW_TAC std_ss [FUN_EQ_THM]
   ++ Know `SIGMA (\i. (if x IN a INTER b i then 1 else 0)) s =
	    SIGMA (\i. (if x IN (a DIFF b e) INTER b i then 1 else 0)) s`
   >> (RW_TAC std_ss [Once EXTREAL_SUM_IMAGE_IN_IF]
       ++ RW_TAC std_ss [(Once o Q.SPEC `(\i. if x IN (a DIFF b e) INTER b i then 1 else 0)` o
       	  	 	 UNDISCH o Q.ISPEC `(s :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF]
       ++ MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``)
       ++ RW_TAC std_ss [FUN_EQ_THM, IN_INTER, IN_DIFF]
       ++ FULL_SIMP_TAC real_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF,	IN_INTER, NOT_IN_EMPTY,
       	  			 EXTENSION, GSPECIFICATION]
       ++ METIS_TAC [])
   ++ STRIP_TAC
   ++ `SIGMA (\i. if x IN a INTER b i then 1 else 0) s = (if x IN a DIFF b e then 1 else 0)`
       by METIS_TAC []
   ++ POP_ORW
   ++ RW_TAC real_ss [IN_INTER, IN_DIFF, EXTREAL_SUM_IMAGE_ZERO, add_rzero, add_lzero]
   ++ FULL_SIMP_TAC std_ss []
   ++ `x IN BIGUNION (IMAGE b s)` by METIS_TAC [SUBSET_DEF, IN_UNION]
   ++ FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE]
   ++ `s = {x'} UNION (s DIFF {x'})` by METIS_TAC [UNION_DIFF, SUBSET_DEF, IN_SING]
   ++ POP_ORW
   ++ `FINITE {x'} /\ FINITE (s DIFF {x'})` by METIS_TAC [FINITE_SING, FINITE_DIFF]
   ++ `DISJOINT {x'} (s DIFF {x'})` by METIS_TAC [EXTENSION, IN_DISJOINT, IN_DIFF, IN_SING]
   ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_DISJOINT_UNION]
   ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING]
   ++ Suff `SIGMA (\i. if x IN b i then 1 else 0) (s DIFF {x'}) = 0`
   >> METIS_TAC [add_rzero]
   ++ RW_TAC std_ss [Once EXTREAL_SUM_IMAGE_IN_IF]
   ++ Suff `(\i. if i IN s DIFF {x'} then if x IN b i then 1 else 0 else 0) = (\x. 0)`
   >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
   ++ RW_TAC std_ss [FUN_EQ_THM, IN_DIFF, IN_SING]
   ++ METIS_TAC [IN_SING, IN_DIFF, IN_DISJOINT]);

val indicator_fn_suminf = store_thm
 ("indicator_fn_suminf",
  ``!a x. (!m n. m <> n ==> DISJOINT (a m) (a n)) ==>
          (suminf (\i. indicator_fn (a i) x) =
             indicator_fn (BIGUNION (IMAGE a univ(:num))) x)``,
  RW_TAC std_ss [ext_suminf_def,sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ Cases_on `~(x IN BIGUNION (IMAGE a univ(:num)))`
      >> (FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV]
          ++ RW_TAC std_ss [indicator_fn_def, EXTREAL_SUM_IMAGE_ZERO, FINITE_COUNT,le_refl,le_01])
      ++ FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, indicator_fn_def]
      ++ REVERSE (RW_TAC std_ss [])
      >> METIS_TAC []
      ++ `!n. n <> x' ==> ~(x IN a n)`
           by METIS_TAC [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
      ++ Cases_on `~(x' IN count n)`
      >> (`SIGMA (\i. if x IN a i then 1 else 0) (count n) = 0`
            by (MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
                ++ RW_TAC real_ss [FINITE_COUNT]
		++ METIS_TAC [])
          ++ RW_TAC std_ss [le_01])
      ++ `count n = ((count n) DELETE x') UNION {x'}`
          by (RW_TAC std_ss [EXTENSION, IN_DELETE, IN_UNION, IN_SING, IN_COUNT]
	      ++ METIS_TAC [])
      ++ POP_ORW
      ++ `DISJOINT ((count n) DELETE x') ({x'})`
          by RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_SING, IN_DELETE]
      ++ `!n. (\i. if x IN a i then 1 else 0) n <> NegInf`
          by RW_TAC std_ss [num_not_infty]
      ++ FULL_SIMP_TAC std_ss [FINITE_COUNT, FINITE_DELETE, FINITE_SING,
      	 	       	       EXTREAL_SUM_IMAGE_DISJOINT_UNION, EXTREAL_SUM_IMAGE_SING]
      ++ Suff `SIGMA (\i. if x IN a i then 1 else 0) (count n DELETE x') = 0`
      >> RW_TAC std_ss [add_lzero, le_refl]
      ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
      ++ RW_TAC std_ss [FINITE_COUNT, FINITE_DELETE]
      ++ METIS_TAC [IN_DELETE])
  ++ `!n. SIGMA (\i. indicator_fn (a i) x) (count n) <= y`
       by (RW_TAC std_ss []
           ++ POP_ASSUM MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
	   ++ METIS_TAC [])
  ++ ASM_SIMP_TAC std_ss [indicator_fn_def, IN_BIGUNION_IMAGE, IN_UNIV]
  ++ (REVERSE (Cases_on `?x'. x IN a x'`) ++ ASM_SIMP_TAC std_ss [])
  >> (`0 <= SIGMA (\i. indicator_fn (a i) x) (count 0)`
       by RW_TAC std_ss [COUNT_ZERO, EXTREAL_SUM_IMAGE_THM, le_refl]
      ++ METIS_TAC [le_trans])
  ++ POP_ASSUM (Q.X_CHOOSE_THEN `x'` ASSUME_TAC)
  ++ Suff `SIGMA (\i. indicator_fn (a i) x) (count (SUC x')) = 1`
  >> METIS_TAC []
  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_COUNT, COUNT_SUC]
  ++ Suff `SIGMA (\i. indicator_fn (a i) x) (count x' DELETE x') = 0`
  >> RW_TAC std_ss [indicator_fn_def,add_rzero]
  ++ `!n. n <> x' ==> ~(x IN a n)` by METIS_TAC [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
  ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
  ++ FULL_SIMP_TAC std_ss [FINITE_COUNT, FINITE_DELETE, IN_COUNT, IN_DELETE, indicator_fn_def]);

val measure_split = store_thm
  ("measure_split", ``!(r:num->bool) (b:num->('a->bool)) m.
	measure_space m /\ FINITE r /\
	(BIGUNION (IMAGE b r) = m_space m) /\
	(!i j. i IN r /\ j IN r /\ (~(i = j)) ==> DISJOINT (b i) (b j)) /\
	(!i. i IN r ==> b i IN measurable_sets m) ==>
	     !a. a IN measurable_sets m ==>
		 ((measure m) a = SIGMA (\i. (measure m) (a INTER (b i))) r)``,
   Suff `!r. FINITE r ==>
		(\r. !(b:num->('a->bool)) m.
	measure_space m /\
	(BIGUNION (IMAGE b r) = m_space m) /\
	(!i j. i IN r /\ j IN r /\ (~(i=j)) ==> DISJOINT (b i) (b j)) /\
	(!i. i IN r ==> b i IN measurable_sets m) ==>
	     !a. a IN measurable_sets m ==>
		 ((measure m) a =
		  SIGMA (\i. (measure m) (a INTER (b i))) r)) r`
   >> RW_TAC std_ss []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, IMAGE_EMPTY, BIGUNION_EMPTY,
		     DELETE_NON_ELEMENT, IN_INSERT, NOT_IN_EMPTY]
   >> METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE, SUBSET_EMPTY ,MEASURE_EMPTY]
   ++ Cases_on `s = {}`
   >> (FULL_SIMP_TAC real_ss [REAL_SUM_IMAGE_THM, IMAGE_DEF, IN_SING, BIGUNION,
			     GSPECIFICATION, GSPEC_ID, SUBSET_DEF,REAL_SUM_IMAGE_SING]
       ++ METIS_TAC [SUBSET_INTER1,MEASURE_SPACE_SUBSET_MSPACE])
   ++ `?x s'. (s = x INSERT s') /\ ~(x IN s')` by METIS_TAC [SET_CASES]
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, IN_INSERT]
   ++ Q.PAT_ASSUM `!b' m'. P ==> !a'. Q ==> (f = g)`
	(MP_TAC o Q.ISPECL [`(\i:num. if i = x then b x UNION b e else b i)`,
	`(m :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`])
   ++ `IMAGE (\i. (if i = x then b x UNION b e else b i)) s' = IMAGE b s'`
        by (RW_TAC std_ss [Once EXTENSION, IN_IMAGE]
            ++ EQ_TAC
            >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `i` ++ METIS_TAC [])
            ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `x''` ++ METIS_TAC [])
   ++ FULL_SIMP_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT, UNION_ASSOC]
   ++ POP_ASSUM (K ALL_TAC)
   ++ `(b x UNION (b e UNION BIGUNION (IMAGE b s')) = m_space m)`
       by METIS_TAC [UNION_COMM,UNION_ASSOC]
   ++ ASM_REWRITE_TAC []
   ++ `(!i j. ((i = x) \/ i IN s') /\ ((j = x) \/ j IN s') /\ ~(i = j) ==>
            DISJOINT (if i = x then b x UNION b e else b i)
             (if j = x then b x UNION b e else b j))`
          by (FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, GSPECIFICATION, IN_INSERT,
	     		    	    IN_INTER, NOT_IN_EMPTY]
       ++ METIS_TAC [IN_UNION])
   ++ ASM_REWRITE_TAC [GSYM UNION_ASSOC] ++ POP_ASSUM (K ALL_TAC)
   ++ `(!i. (i = x) \/ i IN s' ==> (if i = x then b x UNION b e else b i) IN measurable_sets m)`
	by METIS_TAC [ALGEBRA_UNION, sigma_algebra_def, measure_space_def, subsets_def]
   ++ ASM_REWRITE_TAC [] ++ POP_ASSUM (K ALL_TAC)
   ++ STRIP_TAC
   ++ FULL_SIMP_TAC std_ss [UNION_ASSOC]
   ++ POP_ASSUM ((fn thm => ONCE_REWRITE_TAC [thm]) o UNDISCH o Q.SPEC `a`)
   ++ `(x INSERT s') DELETE e = x INSERT s'` by METIS_TAC [EXTENSION, IN_DELETE, IN_INSERT]
   ++ FULL_SIMP_TAC real_ss [FINITE_INSERT, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT,
			     REAL_ADD_ASSOC]
   ++ Suff `(measure m (a INTER (b x UNION b e)) =
	     measure m (a INTER b e) + measure m (a INTER b x)) /\
	    (SIGMA (\i. measure m (a INTER
				   (if i = x then b x UNION b e else b i))) s' =
	     SIGMA (\i. measure m (a INTER b i)) s')`
   >> RW_TAC std_ss []
   ++ CONJ_TAC
   >> (`a INTER (b x UNION b e) = (a INTER b e) UNION (a INTER b x)`
	by (FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, GSPECIFICATION,
				     NOT_IN_EMPTY, IN_INTER, IN_UNION]
	    ++ METIS_TAC [])
       ++ POP_ORW
       ++ (MATCH_MP_TAC o REWRITE_RULE [additive_def] o UNDISCH o Q.SPEC `m`)
		MEASURE_SPACE_ADDITIVE
       ++ CONJ_TAC
       >> METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, measure_space_def, subsets_def]
       ++ CONJ_TAC
       >> METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, measure_space_def, subsets_def]
       ++ FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER]
       ++ METIS_TAC [])
   ++ ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s' :num -> bool)`) REAL_SUM_IMAGE_IN_IF]
   ++ MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``)
   ++ RW_TAC std_ss [FUN_EQ_THM]
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]);

val _ = export_theory ();
