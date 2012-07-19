(* ------------------------------------------------------------------------- *)
(* Lebesgue Theory defined on the extended real-valued functions             *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble, Cambridge University                    *)
(* ------------------------------------------------------------------------- *)

(*
app load ["bossLib", "metisLib", "arithmeticTheory", "pred_setTheory", "prim_recTheory", "listTheory",
   	  "state_transformerTheory", "HurdUseful", "combinTheory", "pairTheory",
	  "realTheory", "realLib", "extra_boolTheory", "jrhUtils",
	  "extra_pred_setTheory", "realSimps", "extra_realTheory",
	  "numTheory", "simpLib", "seqTheory", "subtypeTheory",
	  "transcTheory", "limTheory", "stringTheory", "rich_listTheory",
	  "stringSimps", "listSimps", "extrealTheory", "measureTheory"];

quietdec := true;
*)
open HolKernel Parse boolLib bossLib metisLib arithmeticTheory pred_setTheory prim_recTheory
     listTheory state_transformerTheory HurdUseful extra_numTheory
     combinTheory pairTheory realTheory realLib extra_boolTheory jrhUtils
     extra_pred_setTheory realSimps extra_realTheory  numTheory
     simpLib seqTheory subtypeTheory transcTheory limTheory stringTheory
     rich_listTheory stringSimps listSimps extrealTheory measureTheory;

val _ = new_theory "lebesgue";

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val REVERSE = Tactical.REVERSE;

val Simplify = RW_TAC arith_ss;
val Suff = PARSE_TAC SUFF_TAC;
val Know = PARSE_TAC KNOW_TAC;
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val Cond =
  DISCH_THEN
  (fn mp_th =>
   let
     val cond = fst (dest_imp (concl mp_th))
   in
     KNOW_TAC cond << [ALL_TAC, DISCH_THEN (MP_TAC o MP mp_th)]
   end);

val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

val safe_list_ss = (simpLib.++ (bool_ss, LIST_ss));

val safe_string_ss = (simpLib.++ (bool_ss, STRING_ss));

val arith_string_ss = (simpLib.++ (arith_ss, STRING_ss));

val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

(*
quietdec := false;
*)

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

val pos_simple_fn_integral_def = Define
   `pos_simple_fn_integral m s a x =
	(SIGMA (\i:num. (x i) * ((measure m) (a i))) s)`;

val psfs_def = Define
   `psfs m f = {(s,a,x) | pos_simple_fn m f s a x}`;

val psfis_def = Define
   `psfis m f = IMAGE (\(s,a,x). pos_simple_fn_integral m s a x) (psfs m f)`;

val pos_fn_integral_def = Define
   `pos_fn_integral m f = sup {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f x}`;

val integral_def = Define
   `integral m f = (pos_fn_integral m (fn_plus f)) - (pos_fn_integral m (fn_minus f))`;

val integrable_def = Define
   `integrable m f =
     f IN measurable (m_space m,measurable_sets m) Borel /\
     (?z. (!r. r IN {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= fn_plus f x} ==> (r <= z))) /\
     (?z. (!r. r IN {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= fn_minus f x} ==> (r <= z)))`;

val finite_space_integral_def = Define
   `finite_space_integral m f =
        SIGMA (\r. real (r) * measure m (PREIMAGE f {r} INTER m_space m)) (IMAGE f (m_space m))`;

val prod_measure_def = Define
   `prod_measure m0 m1 =
	(\a. integral m0 (\s0. Normal ((measure m1) (PREIMAGE (\s1. (s0,s1)) a))))`;

val prod_measure_space_def = Define
   `prod_measure_space m0 m1 =
	((m_space m0) CROSS (m_space m1),
	 subsets (sigma ((m_space m0) CROSS (m_space m1))
	       		(prod_sets (measurable_sets m0) (measurable_sets m1))),
	 prod_measure m0 m1)`;

val prod_sets3_def = Define
   `prod_sets3 a b c = {s CROSS (t CROSS u) | s IN a /\ t IN b /\ u IN c}`;

val prod_measure3_def = Define
   `prod_measure3 m0 m1 m2 = prod_measure m0 (prod_measure_space m1 m2)`;

val prod_measure_space3_def = Define
   `prod_measure_space3 m0 m1 m2 =
    (m_space m0 CROSS (m_space m1 CROSS m_space m2),
     subsets (sigma (m_space m0 CROSS (m_space m1 CROSS m_space m2))
              (prod_sets3 (measurable_sets m0) (measurable_sets m1) (measurable_sets m2))),
     prod_measure3 m0 m1 m2)`;

(*****************************************************************************)

val pos_simple_fn_integral_present = store_thm
  ("pos_simple_fn_integral_present",
   ``!m f (s:num->bool) a x g (s':num->bool) b y.
	measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
	(?z z' c (k:num->bool).
		(!t. t IN m_space m ==> (f t = SIGMA (\i. Normal (z i) * (indicator_fn (c i) t)) k)) /\
		(!t. t IN m_space m ==> (g t = SIGMA (\i. Normal (z' i) * (indicator_fn (c i) t)) k)) /\
		(pos_simple_fn_integral m s a x = pos_simple_fn_integral m k c z) /\
		(pos_simple_fn_integral m s' b y = pos_simple_fn_integral m k c z') /\
		FINITE k /\ (!i. i IN k ==> 0 <= z i) /\ (!i. i IN k ==> 0 <= z' i) /\
		(!i j. i IN k /\ j IN k /\ (~(i=j)) ==> DISJOINT (c i) (c j)) /\
		(!i. i IN k ==> c i IN measurable_sets m) /\
		(BIGUNION (IMAGE c k) = m_space m))``,
   RW_TAC std_ss []
   ++ `?p n. BIJ p (count n) (s CROSS s')`
	by FULL_SIMP_TAC std_ss [GSYM FINITE_BIJ_COUNT, pos_simple_fn_def, FINITE_CROSS]
   ++ `?p'. BIJ p' (s CROSS s') (count n) /\
	    (!x. x IN (count n) ==> ((p' o p) x = x)) /\
	    (!x. x IN (s CROSS s') ==> ((p o p') x = x))`
	by (MATCH_MP_TAC BIJ_INV ++ RW_TAC std_ss [])
   ++ Q.EXISTS_TAC `x o FST o p`
   ++ Q.EXISTS_TAC `y o SND o p`
   ++ Q.EXISTS_TAC `(\(i,j). a i INTER b j) o p`
   ++ Q.EXISTS_TAC `IMAGE p' (s CROSS s')`
   ++ Q.ABBREV_TAC `G = IMAGE (\i j. p' (i,j)) s'`
   ++ Q.ABBREV_TAC `H = IMAGE (\j i. p' (i,j)) s`
   ++ CONJ_TAC
   >> (RW_TAC std_ss [FUN_EQ_THM]
       ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       ++ FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF]
       ++ `(\x'. (if x' IN s then (\i. Normal (x i) * indicator_fn (a i) t) x' else 0)) =
	   (\x'. (if x' IN s then (\i. Normal (x i) *
		SIGMA (\j. indicator_fn (a i INTER b j) t) s') x' else 0))`
	by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	    ++ (MP_TAC o Q.ISPEC `(a :num -> 'a -> bool) (x' :num)` o
		UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
		Q.ISPECL
		[`(s' :num -> bool)`,
		 `m_space (m:('a -> bool) #
          	  (('a -> bool) -> bool) # (('a -> bool) -> real))`,
		 `(b :num -> 'a -> bool)`]) indicator_fn_split
	    ++ Q.PAT_ASSUM `!i. i IN s ==> (a:num->'a->bool) i IN measurable_sets m`
		(ASSUME_TAC o UNDISCH o Q.SPEC `x'`)
	    ++ `!a m. measure_space m /\
	      a IN measurable_sets m ==> a SUBSET m_space m`
		by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
 			   	  subset_class_def, subsets_def, space_def]
	    ++ POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
			  Q.ISPECL [`(a :num -> 'a -> bool) (x' :num)`,
				    `(m : ('a -> bool) #
				     (('a -> bool) -> bool) # (('a -> bool) -> real))`])
	    ++ ASM_SIMP_TAC std_ss [])
       ++ FULL_SIMP_TAC std_ss []
       ++ `!(x':num) (i:num). Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) t) s' =
		    SIGMA (\j. Normal (x i) * indicator_fn (a i INTER b j) t) s'`
	   by (RW_TAC std_ss []
               ++ (MP_TAC o Q.SPEC `(\j. indicator_fn (a (i:num) INTER b j) t)` o UNDISCH o Q.SPEC `s'` o GSYM o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	       ++ Suff `(!x. x IN s' ==> 0 <= (\j. indicator_fn (a i INTER b j) t) x)`
	       >> RW_TAC std_ss []
	       ++ RW_TAC std_ss [indicator_fn_def,le_refl,le_01])
       ++ POP_ORW
       ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       ++ `INJ p' (s CROSS s')
	   (IMAGE p' (s CROSS s'))`
	   by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       ++ (MP_TAC o Q.SPEC `(\i:num. Normal (x (FST (p i))) * indicator_fn ((\(i:num,j:num). a i INTER b j) (p i)) t)` o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss []
       ++ (MP_TAC o Q.SPEC `((\i. Normal (x (FST ((p :num -> num # num) i))) * indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p')` o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
       ++ RW_TAC std_ss []
       ++ `(\x'.if x' IN s CROSS s' then
                Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t
               else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x'
		 else 0))` by METIS_TAC []
       ++ POP_ORW
       ++ RW_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_IN_IF, EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE]
       ++ Suff `(\i. Normal (x (FST i)) * indicator_fn (a (FST i) INTER b (SND i)) t) =
                (\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'`
       ++ RW_TAC std_ss [FST,SND])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [FUN_EQ_THM] ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       ++ FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF]
       ++ `(\x. if x IN s' then Normal (y x) * indicator_fn (b x) t else 0) =
           (\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) t) x else 0))`
             by RW_TAC std_ss []
       ++ POP_ORW
       ++ `(\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) t) x else 0)) =
	   (\x. (if x IN s' then (\i. Normal (y i) *
		SIGMA (\j. indicator_fn (a j INTER b i) t) s) x else 0))`
	by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	    ++ (MP_TAC o REWRITE_RULE [Once INTER_COMM] o
		Q.ISPEC `(b :num -> 'a -> bool) (x' :num)` o
		UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
		Q.ISPECL
		[`(s :num -> bool)`,
		 `m_space (m:('a -> bool) #
          	  (('a -> bool) -> bool) # (('a -> bool) -> real))`,
		 `(a :num -> 'a -> bool)`]) indicator_fn_split
	    ++ Q.PAT_ASSUM `!i. i IN s' ==> (b:num->'a->bool) i IN measurable_sets m`
		(ASSUME_TAC o UNDISCH o Q.SPEC `x'`)
	    ++ RW_TAC std_ss [MEASURE_SPACE_SUBSET_MSPACE])
       ++ POP_ORW
      ++ `!(i:num). Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) t) s =
		    SIGMA (\j. Normal (y i) * indicator_fn (a j INTER b i) t) s`
	   by (RW_TAC std_ss []
               ++ (MP_TAC o Q.SPEC `(\j. indicator_fn (a j INTER b (i:num)) t)` o UNDISCH o Q.SPEC `s` o GSYM o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	       ++ Suff `(!x. x IN s ==> 0 <= (\j. indicator_fn (a j INTER b i) t) x)`
	       >> RW_TAC std_ss []
	       ++ RW_TAC std_ss [indicator_fn_def,le_refl,le_01])
       ++ POP_ORW
       ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       ++ `INJ p' (s CROSS s')
	   (IMAGE p' (s CROSS s'))`
	     by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       ++ (MP_TAC o Q.SPEC `(\i:num. Normal (y (SND (p i))) * indicator_fn ((\(i:num,j:num). a i INTER b j) (p i)) t)` o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF]
       ++ `(\x'.if x' IN s CROSS s' then
                Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x'
		 else 0))` by METIS_TAC []
       ++ POP_ORW
       ++ RW_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_IN_IF,EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE]
       ++  `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
	by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
	    ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [FST,SND]
	    ++ EQ_TAC
            >> (STRIP_TAC ++ Q.EXISTS_TAC `(r,q)` ++ RW_TAC std_ss [FST,SND])
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [])
       ++ POP_ORW
       ++ `INJ (\x. (SND x,FST x)) (s CROSS s')
		(IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
	by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
	    >> METIS_TAC []
	    ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
	    ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [FST,SND])
       ++ (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) t)` o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o
	   Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
		INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss [o_DEF]
       ++ Suff `(\x. Normal (y (SND x)) * indicator_fn (a (FST x) INTER b (SND x)) t) =
		(\x. Normal (y (SND x)) * indicator_fn ((\(i,j). a i INTER b j) x) t)`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'`
       ++ RW_TAC std_ss [FST,SND])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [pos_simple_fn_integral_def] ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       ++ RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
       ++ `(\x'. if x' IN s then (x x') * measure m (a x') else 0) =
           (\x'. (if x' IN s then (\i. (x i) * measure m (a i)) x' else 0))`
            by METIS_TAC []
       ++ POP_ORW
       ++ `(\x'. (if x' IN s then (\i. (x i) * measure m (a i)) x' else 0)) =
	   (\x'. (if x' IN s then (\i. (x i) *
		SIGMA (\j. measure m (a i INTER b j)) s') x' else 0))`
	by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	    ++ (MP_TAC o Q.SPEC `a (x' :num)` o
		UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
		Q.SPECL
		[`s'`, `b`, `m`]) measure_split
	   ++ RW_TAC std_ss [])
       ++ POP_ORW
       ++ RW_TAC std_ss []
       ++ `!(x':num). x' IN s ==> ((x x') * SIGMA (\j. measure m (a x' INTER b j)) s' =
		    SIGMA (\j. (x x') * measure m (a x' INTER b j)) s')`
	   by (RW_TAC std_ss []
	       ++ FULL_SIMP_TAC std_ss [REAL_SUM_IMAGE_CMUL])
       ++ RW_TAC std_ss []
       ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       ++ `INJ p' (s CROSS s')
	   (IMAGE p' (s CROSS s'))`
   	    by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       ++ (MP_TAC o Q.SPEC `(\i:num. (x (FST (p i))) * measure m ((\(i:num,j:num). a i INTER b j) (p i)))` o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) REAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s:num -> bool)CROSS(s':num -> bool)`) REAL_SUM_IMAGE_IN_IF]
       ++ `(\x'. if x' IN s CROSS s' then
                (x (FST x')) * measure m ((\(i,j). a i INTER b j) x') else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. (x (FST x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))` by METIS_TAC []
       ++ POP_ORW
       ++ RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF,REAL_SUM_IMAGE_REAL_SUM_IMAGE]
       ++ Suff `(\i. (x (FST i)) * measure m (a (FST i) INTER b (SND i))) =
                (\x'. (x (FST x')) * measure m ((\(i,j). a i INTER b j) x'))`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'`
       ++ RW_TAC std_ss [FST,SND])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [pos_simple_fn_integral_def] ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       ++ RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
       ++ `(\x'. if x' IN s' then (y x') * measure m (b x') else 0) =
           (\x'. (if x' IN s' then (\i. (y i) * measure m (b i)) x' else 0))`
            by METIS_TAC []
       ++ POP_ORW
       ++ `(\x'. (if x' IN s' then (\i. (y i) * measure m (b i)) x' else 0)) =
	   (\x'. (if x' IN s' then (\i. (y i) *
		SIGMA (\j. measure m (b i INTER a j)) s) x' else 0))`
	by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	    ++ (MP_TAC o Q.SPEC `b (x' :num)` o
		UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
		Q.SPECL
		[`s`, `a`, `m`]) measure_split
	   ++ RW_TAC std_ss [])
       ++ POP_ORW
       ++ `!i. i IN s' ==> ((y i) * SIGMA (\j. measure m (b i INTER a j)) s =
			   SIGMA (\j. (y i) * measure m (b i INTER a j)) s)`
   	   by (RW_TAC std_ss []
	       ++ FULL_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_CMUL])
       ++ FULL_SIMP_TAC std_ss []
       ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       ++ `INJ p' (s CROSS s')
	   (IMAGE p' (s CROSS s'))`
   	    by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       ++ (MP_TAC o Q.SPEC `(\i:num. (y (SND (p i))) * measure m ((\(i:num,j:num). a i INTER b j) (p i)))` o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) REAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s:num -> bool)CROSS(s':num -> bool)`) REAL_SUM_IMAGE_IN_IF]
       ++ `(\x'. if x' IN s CROSS s' then
                (y (SND x')) * measure m ((\(i,j). a i INTER b j) x') else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. (y (SND x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))` by METIS_TAC []
       ++ POP_ORW
       ++ RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF,REAL_SUM_IMAGE_REAL_SUM_IMAGE]
       ++  `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
	by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
	    ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [FST,SND]
	    ++ EQ_TAC
            >> (STRIP_TAC ++ Q.EXISTS_TAC `(r,q)` ++ RW_TAC std_ss [FST,SND])
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [])
       ++ POP_ORW
       ++ `INJ (\x. (SND x,FST x)) (s CROSS s')
		(IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
	by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
	    >> METIS_TAC []
	    ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
	    ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
	    ++ RW_TAC std_ss []
	    ++ FULL_SIMP_TAC std_ss [FST,SND])
       ++ (MP_TAC o Q.SPEC `(\x. (y (FST x)) * measure m (a (SND x) INTER b (FST x)))` o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o
	   Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
		INST_TYPE [``:'b``|->``:num#num``]) REAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss [o_DEF,INTER_COMM]
       ++ Suff `(\x. (y (SND x)) * measure m (a (FST x) INTER b (SND x))) =
		(\x. (y (SND x)) * measure m ((\(i,j). a i INTER b j) x))`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'`
       ++ RW_TAC std_ss [FST,SND])
   ++ CONJ_TAC
   >> FULL_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_CROSS, pos_simple_fn_def]
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_IMAGE]
       ++ FULL_SIMP_TAC std_ss [o_DEF]
       ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
       ++ RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ METIS_TAC [IN_CROSS,pos_simple_fn_def,FST])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_IMAGE]
       ++ FULL_SIMP_TAC std_ss [o_DEF]
       ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
       ++ RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ METIS_TAC [IN_CROSS,pos_simple_fn_def,SND])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_DISJOINT, IN_IMAGE,EXTENSION, NOT_IN_EMPTY, IN_INTER]
       ++ FULL_SIMP_TAC std_ss [o_DEF]
       ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
       ++ RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
       ++ FULL_SIMP_TAC std_ss [IN_INTER, IN_CROSS, FST, SND, pos_simple_fn_def,
				DISJOINT_DEF]
       ++ METIS_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER])
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_IMAGE]
       ++ FULL_SIMP_TAC std_ss [o_DEF]
       ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       ++ RW_TAC std_ss []
       ++ FULL_SIMP_TAC std_ss [IN_CROSS, FST, SND, pos_simple_fn_def]
       ++ METIS_TAC [ALGEBRA_INTER, subsets_def, space_def,
		     sigma_algebra_def, measure_space_def])
   ++ RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_IMAGE, IN_CROSS]
   ++ `!s'' x. (?x'. ((x = p' x') /\ FST x' IN s /\ SND x' IN s')) =
	   (?x1 x2. ((x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s'))`
	by METIS_TAC [PAIR, FST, SND]
   ++ POP_ORW
   ++ `!s''. (?x. (s'' = (\(i,j). a i INTER b j) (p x)) /\
		  ?x1 x2. (x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s') =
		 (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\
			  x1 IN s /\ x2 IN s')`
	by METIS_TAC []
   ++ POP_ORW
   ++ FULL_SIMP_TAC std_ss [o_DEF, IN_CROSS]
   ++ `!s''. (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\
		  x1 IN s /\ x2 IN s') =
		 (?x1 x2. (s'' = (\(i,j). a i INTER b j) (x1,x2)) /\
		  x1 IN s /\ x2 IN s')`
	by METIS_TAC [FST,SND]
   ++ POP_ORW
   ++ RW_TAC std_ss []
   ++ Suff `(?x1 x2. x' IN a x1 INTER b x2 /\ x1 IN s /\ x2 IN s') =
		x' IN m_space m`
   >> METIS_TAC []
   ++ RW_TAC std_ss [IN_INTER]
   ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
   ++ `m_space m = (BIGUNION (IMAGE a s)) INTER (BIGUNION (IMAGE b s'))`
		by METIS_TAC [INTER_IDEMPOT]
   ++ POP_ORW
   ++ Q.PAT_ASSUM `BIGUNION (IMAGE b s') = m_space m` (K ALL_TAC)
   ++ Q.PAT_ASSUM `BIGUNION (IMAGE a s) = m_space m` (K ALL_TAC)
   ++ RW_TAC std_ss [IN_INTER, IN_BIGUNION, IN_IMAGE]
   ++ METIS_TAC []);

val psfis_present = store_thm
  ("psfis_present",
   ``!m f g a b.
	measure_space m /\
	a IN psfis m f /\ b IN psfis m g ==>
	(?z z' c (k:num->bool).
		(!t. t IN m_space m ==> (f t = SIGMA (\i. Normal (z i) * (indicator_fn (c i) t)) k)) /\
		(!t. t IN m_space m ==> (g t = SIGMA (\i. Normal (z' i) * (indicator_fn (c i) t)) k)) /\
		(a = pos_simple_fn_integral m k c z) /\
		(b = pos_simple_fn_integral m k c z') /\
		FINITE k /\ (!i. i IN k ==> 0 <= z i) /\ (!i. i IN k ==> 0 <= z' i) /\
		(!i j. i IN k /\ j IN k /\ (~(i=j)) ==> DISJOINT (c i) (c j)) /\
		(!i. i IN k ==> c i IN measurable_sets m) /\
		(BIGUNION (IMAGE c k) = m_space m))``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Cases_on `x'` ++ Cases_on `x` ++ Cases_on `x''` ++ Cases_on `x'''`
   ++ Cases_on `r'` ++ Cases_on `r` ++ Cases_on `r''` ++ Cases_on `r'''`
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
   ++  MATCH_MP_TAC pos_simple_fn_integral_present
   ++ METIS_TAC []);

(* ------------------------------------------------------ *)
(*        Properties of POSTIVE SIMPLE FUNCTIONS          *)
(* ------------------------------------------------------ *)

val pos_simple_fn_thm1 = store_thm
 ("pos_simple_fn_thm1",``!m f s a x i y. measure_space m /\ pos_simple_fn m f s a x /\
			i IN s /\ y IN a i ==> (f y = Normal (x i))``,
  RW_TAC std_ss [pos_simple_fn_def]
  ++ `y IN m_space m` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF]
  ++ `FINITE (s DELETE i)` by RW_TAC std_ss [FINITE_DELETE]
  ++ (MP_TAC o UNDISCH o Q.SPECL [`i`,`s DELETE i`] o CONJUNCT2 o Q.ISPEC `(\i:num. Normal (x i) * indicator_fn (a i) y)`) EXTREAL_SUM_IMAGE_THM
  ++ RW_TAC std_ss [INSERT_DELETE,DELETE_DELETE]
  ++ `!j. j IN (s DELETE i) ==> ~(y IN a j)`
	    by (RW_TAC std_ss [IN_DELETE]
		++ `DISJOINT (a i) (a j)` by METIS_TAC []
		++ FULL_SIMP_TAC std_ss [DISJOINT_DEF,INTER_DEF,EXTENSION,GSPECIFICATION,NOT_IN_EMPTY]
		++ METIS_TAC [])
  ++ RW_TAC std_ss [Once EXTREAL_SUM_IMAGE_IN_IF]
  ++ `!j. j IN s DELETE i ==> (indicator_fn (a j) y = 0)` by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ RW_TAC std_ss [mul_rzero,EXTREAL_SUM_IMAGE_ZERO,add_rzero,indicator_fn_def,mul_rone]);

val pos_simple_fn_le = store_thm
  ("pos_simple_fn_le",``!m f g s a x x' i. measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s a x' /\
                        (!x. x IN m_space m ==> g x <= f x) /\
 			(i IN s) /\ ~(a i = {}) ==> (Normal (x' i) <= Normal (x i))``,
  RW_TAC std_ss []
  ++ `!t. t IN a i ==> (f t = Normal (x i))` by METIS_TAC [pos_simple_fn_thm1]
  ++ `!t. t IN a i ==> (g t = Normal (x' i))` by METIS_TAC [pos_simple_fn_thm1]
  ++ METIS_TAC [CHOICE_DEF,pos_simple_fn_def,MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF]);

val pos_simple_fn_cmul = store_thm
 ("pos_simple_fn_cmul", ``!m f z. measure_space m /\ pos_simple_fn m f s a x /\ 0 <= z ==> (?s' a' x'. pos_simple_fn m (\t. Normal z * f t) s' a' x')``,
  RW_TAC std_ss [pos_simple_fn_def]
  ++ Q.EXISTS_TAC `s` ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `(\i. z * (x i))`
  ++ RW_TAC std_ss [REAL_LE_MUL,GSYM extreal_mul_def]
  >> METIS_TAC [extreal_le_def,extreal_of_num_def,le_mul]
  ++ (MP_TAC o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) t)`,`z`] o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
  ++ FULL_SIMP_TAC std_ss [mul_assoc]);

val pos_simple_fn_cmul_alt = store_thm
("pos_simple_fn_cmul_alt", ``!m f s a x z. measure_space m /\ 0 <= z /\ pos_simple_fn m f s a x ==> pos_simple_fn m (\t. Normal z * f t) s a (\i. z * x i)``,
  RW_TAC std_ss [pos_simple_fn_def,REAL_LE_MUL,GSYM extreal_mul_def]
  >> METIS_TAC [extreal_le_def,extreal_of_num_def,le_mul]
  ++ (MP_TAC o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) t)`,`z`] o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
  ++ `!x'. (\i. Normal (x i) * indicator_fn (a i) t) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero] ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ FULL_SIMP_TAC std_ss [mul_assoc]);

val pos_simple_fn_add = store_thm
 ("pos_simple_fn_add",``!m f g. measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' a' x' ==> (?s'' a'' x''. pos_simple_fn m (\t. f t + g t) s'' a'' x'') ``,
  REPEAT STRIP_TAC
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`a'`,`x'`]) pos_simple_fn_integral_present
  ++ RW_TAC std_ss []
  ++ Q.EXISTS_TAC `k`
  ++ Q.EXISTS_TAC `c` ++ Q.EXISTS_TAC `(\i. z i + z' i)`
  ++ RW_TAC std_ss [pos_simple_fn_def,REAL_LE_ADD,GSYM extreal_add_def]
  >> METIS_TAC [le_add,pos_simple_fn_def]
  ++ RW_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_ADD]
  ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_EQ
  ++ METIS_TAC [extreal_of_num_def,extreal_le_def,add_rdistrib]);

val pos_simple_fn_add_alt = store_thm
 ("pos_simple_fn_add_alt",``!m f g s a x y. measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s a y ==> pos_simple_fn m (\t. f t + g t) s a (\i. x i + y i)``,
  RW_TAC std_ss [pos_simple_fn_def,REAL_LE_ADD,GSYM extreal_add_def,le_add,GSYM EXTREAL_SUM_IMAGE_ADD]
  ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_EQ
  ++  METIS_TAC [extreal_of_num_def,extreal_le_def,add_rdistrib]);

val pos_simple_fn_indicator = store_thm
("pos_simple_fn_indicator",``!m A. measure_space m /\ A IN measurable_sets m ==> ?s a x. pos_simple_fn m (indicator_fn A) s a x``,
 RW_TAC real_ss []
 ++ `FINITE {0:num;1:num}` by METIS_TAC [FINITE_INSERT,FINITE_SING]
 ++ Q.EXISTS_TAC `{0:num;1:num}`  ++ Q.EXISTS_TAC `(\i. if i = 0 then (m_space m DIFF A) else A)` ++ Q.EXISTS_TAC `(\i. if i = 0 then 0 else 1)`
 ++ RW_TAC real_ss [pos_simple_fn_def,indicator_fn_def,FINITE_SING,IN_SING,MEASURE_SPACE_MSPACE_MEASURABLE]
 << [METIS_TAC [le_01,le_refl],
     `{1:num} DELETE 0 = {1}` by (RW_TAC real_ss [DELETE_DEF,DIFF_DEF,IN_SING] ++ RW_TAC real_ss [EXTENSION,IN_SING] ++ RW_TAC real_ss [GSPECIFICATION] ++ EQ_TAC >> RW_TAC real_ss [] ++ RW_TAC real_ss [])
     ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM,FINITE_SING,GSYM extreal_of_num_def,mul_lzero,add_lzero,EXTREAL_SUM_IMAGE_SING,mul_rzero,mul_rone],
     METIS_TAC [MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE],
     RW_TAC real_ss [],
     FULL_SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,GSPECIFICATION,IN_INTER,IN_DIFF,NOT_IN_EMPTY,IN_INSERT,IN_SING]
     ++ METIS_TAC [],
     RW_TAC std_ss [IMAGE_DEF]
     ++ `{if i:num = 0 then m_space m DIFF A else A | i IN {0; 1}} = {m_space m DIFF A ; A}`
  	     by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INSERT,IN_SING]
  		 ++ EQ_TAC >> METIS_TAC []
                 ++ RW_TAC std_ss [] >> METIS_TAC []
		 ++ Q.EXISTS_TAC `1:num`
                 ++ RW_TAC real_ss [])
     ++ RW_TAC std_ss [BIGUNION_INSERT,BIGUNION_SING]
     ++ METIS_TAC [UNION_DIFF,MEASURE_SPACE_SUBSET_MSPACE]]);

val pos_simple_fn_indicator_alt = store_thm
("pos_simple_fn_indicator_alt",``!m s. measure_space m /\ s IN measurable_sets m ==>
   pos_simple_fn m (indicator_fn s) {0:num;1:num} (\i:num. if i = 0 then (m_space m DIFF s) else s) (\i. if i = 0 then 0 else 1)``,
  RW_TAC std_ss []
  ++ `FINITE {0:num;1:num}` by METIS_TAC [FINITE_INSERT,FINITE_SING]
  ++ `{1:num} DELETE 0 = {1}` by (RW_TAC real_ss [DELETE_DEF,DIFF_DEF,IN_SING] ++ RW_TAC real_ss [EXTENSION,IN_SING] ++ RW_TAC real_ss [GSPECIFICATION] ++ EQ_TAC >> RW_TAC real_ss [] ++ RW_TAC real_ss [])
  ++ RW_TAC real_ss [pos_simple_fn_def,indicator_fn_def,FINITE_SING,IN_SING,MEASURE_SPACE_MSPACE_MEASURABLE,EXTREAL_SUM_IMAGE_THM,mul_rone,mul_lone,mul_rzero,mul_lzero,EXTREAL_SUM_IMAGE_SING,GSYM extreal_of_num_def,add_rzero,add_lzero]

  << [METIS_TAC [le_01,le_refl],
     METIS_TAC [MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE],
     RW_TAC real_ss [],
     FULL_SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,GSPECIFICATION,IN_INTER,IN_DIFF,NOT_IN_EMPTY,IN_INSERT,IN_SING]
     ++ METIS_TAC [],
     RW_TAC std_ss [IMAGE_DEF]
     ++ `{if i:num = 0 then m_space m DIFF s else s | i IN {0; 1}} = {m_space m DIFF s ; s}`
  	     by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INSERT,IN_SING]
  		 ++ EQ_TAC >> METIS_TAC []
                 ++ RW_TAC std_ss [] >> METIS_TAC []
		 ++ Q.EXISTS_TAC `1:num`
                 ++ RW_TAC real_ss [])
     ++ RW_TAC std_ss [BIGUNION_INSERT,BIGUNION_SING]
     ++ METIS_TAC [UNION_DIFF,MEASURE_SPACE_SUBSET_MSPACE]]);

val pos_simple_fn_max = store_thm
("pos_simple_fn_max",``!m f s a x g s'b y.
	measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
	?s'' a'' x''. pos_simple_fn m (\x. max (f x) (g x)) s'' a'' x''``,
  RW_TAC std_ss []
  ++ `?p n. BIJ p (count n) (s CROSS s')`	by FULL_SIMP_TAC std_ss [GSYM FINITE_BIJ_COUNT, pos_simple_fn_def, FINITE_CROSS]
  ++ `?p'. BIJ p' (s CROSS s') (count n) /\ (!x. x IN (count n) ==> ((p' o p) x = x)) /\ (!x. x IN (s CROSS s') ==> ((p o p') x = x))` by (MATCH_MP_TAC BIJ_INV ++ RW_TAC std_ss [])
  ++ Q.EXISTS_TAC `IMAGE p' (s CROSS s')`
  ++ Q.EXISTS_TAC `(\(i,j). a i INTER b j) o p`
  ++ Q.EXISTS_TAC `(\n. max ((x o FST o p) n) ((y o SND o p)n))`
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def,extreal_max_def]
  ++ `!i j. i IN IMAGE p' (s CROSS s') /\ j IN IMAGE p' (s CROSS s') /\ i <> j ==> DISJOINT (((\(i,j). a i INTER b j) o p) i) (((\(i,j). a i INTER b j) o p) j)`
    by (RW_TAC std_ss [DISJOINT_DEF, IN_IMAGE]
	++ RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_INTER]
	++ FULL_SIMP_TAC std_ss [o_DEF]
        ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
        ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
        ++ RW_TAC std_ss []
        ++ RW_TAC std_ss []
        ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
	++ FULL_SIMP_TAC std_ss [IN_INTER, IN_CROSS, FST, SND, pos_simple_fn_def,DISJOINT_DEF]
        ++ METIS_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER])
  ++ `!i. i IN IMAGE p' (s CROSS s') ==>  ((\(i,j). a i INTER b j) o p) i IN measurable_sets m`
    by (RW_TAC std_ss [IN_IMAGE]
        ++ FULL_SIMP_TAC std_ss [o_DEF]
        ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       	++ RW_TAC std_ss []
	++ FULL_SIMP_TAC std_ss [IN_CROSS, FST, SND, pos_simple_fn_def]
        ++ METIS_TAC [ALGEBRA_INTER, subsets_def, space_def,sigma_algebra_def, measure_space_def])
  ++ `BIGUNION (IMAGE ((\(i,j). a i INTER b j) o p) (IMAGE p' (s CROSS s'))) =  m_space m`
     by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_IMAGE, IN_CROSS]
	++ `!s'' x. (?x'. ((x = p' x') /\ FST x' IN s /\ SND x' IN s')) = (?x1 x2. ((x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s'))`
            by METIS_TAC [PAIR, FST, SND]
	++ POP_ORW
        ++ `!s''. (?x. (s'' = (\(i,j). a i INTER b j) (p x)) /\ ?x1 x2. (x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s') =
                  (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\  x1 IN s /\ x2 IN s')`
            by METIS_TAC []
        ++ POP_ORW
        ++ FULL_SIMP_TAC std_ss [o_DEF, IN_CROSS]
        ++ `!s''. (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\  x1 IN s /\ x2 IN s') = (?x1 x2. (s'' = (\(i,j). a i INTER b j) (x1,x2)) /\ x1 IN s /\ x2 IN s')` by METIS_TAC [FST,SND]
        ++ POP_ORW
       	++ RW_TAC std_ss []
        ++ Suff `(?x1 x2. x' IN a x1 INTER b x2 /\ x1 IN s /\ x2 IN s') = x' IN m_space m`
        >> METIS_TAC []
       	++ RW_TAC std_ss [IN_INTER]
        ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       	++ `m_space m = (BIGUNION (IMAGE a s)) INTER (BIGUNION (IMAGE b s'))` by METIS_TAC [INTER_IDEMPOT]
        ++ POP_ORW
       	++ Q.PAT_ASSUM `BIGUNION (IMAGE b s') = m_space m` (K ALL_TAC)
 	++ Q.PAT_ASSUM `BIGUNION (IMAGE a s) = m_space m` (K ALL_TAC)
	++ RW_TAC std_ss [IN_INTER, IN_BIGUNION, IN_IMAGE]
	++ METIS_TAC [])
  ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
  ++ `INJ p' (s CROSS s')(IMAGE p' (s CROSS s'))` by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
  ++ `FINITE (IMAGE p' (s CROSS s'))` by RW_TAC std_ss [IMAGE_FINITE]
  ++ FULL_SIMP_TAC std_ss []
  ++ CONJ_TAC >> METIS_TAC []
  ++ REVERSE CONJ_TAC
  >> (RW_TAC std_ss [max_def] ++ FULL_SIMP_TAC std_ss [IN_IMAGE,IN_CROSS])
  ++ RW_TAC std_ss []
  >> (RW_TAC std_ss [Once EXTREAL_SUM_IMAGE_IN_IF]
      ++ `(\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) x') x else 0)) = (\x. (if x IN s' then (\i. Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) x') s) x else 0))`
	  by (RW_TAC std_ss [FUN_EQ_THM]
		++ RW_TAC std_ss []
		++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
		++ (MP_TAC o REWRITE_RULE [Once INTER_COMM] o Q.ISPEC `(b :num -> 'a -> bool) (x'' :num)` o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.ISPECL [`(s :num -> bool)`, `m_space (m:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`, `(a :num -> 'a -> bool)`]) indicator_fn_split
		++ Q.PAT_ASSUM `!i. i IN s' ==> (b:num->'a->bool) i IN measurable_sets m` (ASSUME_TAC o UNDISCH o Q.SPEC `x''`)
		++ `!a m. measure_space m /\ a IN measurable_sets m ==> a SUBSET m_space m` by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,subset_class_def, subsets_def, space_def]
		++ POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.ISPECL [`(b :num -> 'a -> bool) (x'' :num)`,`(m : ('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`])
		++ ASM_SIMP_TAC std_ss [])
      ++ `(\x. if x IN s' then Normal (y x) * indicator_fn (b x) x' else 0) =
        (\x. if x IN s' then (\i. Normal (y i) * indicator_fn (b i) x') x else 0)`
          by METIS_TAC []
      ++ POP_ORW ++ POP_ORW
      ++ `!i. i IN s' ==> (Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) x') s = SIGMA (\j. Normal (y i) * indicator_fn (a j INTER b i) x') s)`
           by (RW_TAC std_ss []
               ++ (MP_TAC o Q.SPECL [`(\j. indicator_fn (a j INTER (b:num->'a->bool) i) x')`,`y (i:num)`] o UNDISCH o Q.ISPEC `s:num->bool` o GSYM o INST_TYPE [alpha |-> ``:num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	       ++ FULL_SIMP_TAC std_ss [])
      ++ RW_TAC std_ss []
      ++ (MP_TAC o Q.ISPEC `(\n':num. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
                           indicator_fn ((\(i:num,j:num). a i INTER b j) (p n')) x')` o
                   UNDISCH o Q.SPEC `p'` o UNDISCH o
                   Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
                   INST_TYPE [``:'b``|->``:num``]) EXTREAL_SUM_IMAGE_IMAGE
      ++ RW_TAC std_ss [o_DEF]
      ++ POP_ASSUM (K ALL_TAC)
      ++ RW_TAC std_ss [Once ((UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF)]
      ++ `!x. (\j. Normal (y x) * indicator_fn (a j INTER b x) x') = (\x j. Normal (y x) * indicator_fn (a j INTER b x) x') x` by METIS_TAC []
      ++ POP_ORW
      ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_IF_ELIM,EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE]
      ++ `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
		by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
		    ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
		    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [FST,SND]
		    ++ EQ_TAC
        	    >> (STRIP_TAC ++ Q.EXISTS_TAC `(r,q)` ++ RW_TAC std_ss [FST,SND])
		    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [])
      ++ POP_ORW
      ++ `INJ (\x. (SND x,FST x)) (s CROSS s') (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
		by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
		    >> METIS_TAC []
		    ++ (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
		    ++ (MP_TAC o Q.ISPEC `x''':num#num`) pair_CASES
		    ++ RW_TAC std_ss []
		    ++ FULL_SIMP_TAC std_ss [FST,SND])
      ++ (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) x')` o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o  Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss [o_DEF]
       ++ Suff `!x'''. x''' IN (s CROSS s') ==> ((\x. Normal (y (SND x)) * indicator_fn (a (FST x) INTER b (SND x)) x') x''' = (\x''. if x'' IN s CROSS s' then Normal (max (x (FST x'')) (y (SND x''))) * indicator_fn ((\(i,j). a i INTER b j) x'') x' else 0) x''')`
       >> (RW_TAC std_ss []
           ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(s:num->bool) CROSS (s':num->bool)`) EXTREAL_SUM_IMAGE_EQ
	   ++ RW_TAC std_ss []
	   ++ DISJ1_TAC
	   ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero])
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'''`
       ++ RW_TAC real_ss [indicator_fn_def,mul_rone,mul_rzero]
       ++ `q IN s` by METIS_TAC [IN_CROSS,FST,SND]
       ++ `x' IN (a q)` by METIS_TAC [IN_INTER]
       ++ `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s = Normal (x q)`
           by (`pos_simple_fn m f s a x` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
	       ++ METIS_TAC [pos_simple_fn_thm1,pos_simple_fn_def])
       ++ `r IN s'` by METIS_TAC [IN_CROSS,FST,SND]
       ++ `x' IN (b r)` by METIS_TAC [IN_INTER]
       ++ `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' = Normal (y r)`
          by (`pos_simple_fn m g s' b y` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
	      ++ METIS_TAC [pos_simple_fn_thm1])
       ++ FULL_SIMP_TAC std_ss [extreal_le_def,max_def])
  ++ RW_TAC std_ss [Once EXTREAL_SUM_IMAGE_IN_IF]
  ++ `(\x''. if x'' IN s then Normal (x x'') * indicator_fn (a x'') x' else 0) =
      (\x''. if x'' IN s then (\i. Normal (x i) * indicator_fn (a i) x') x'' else 0)`
          by METIS_TAC []
  ++ POP_ORW
  ++ `(\x''. (if x'' IN s then (\i. Normal (x i) * indicator_fn (a i) x') x'' else 0)) = (\x''. (if x'' IN s then (\i. Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) x') s') x'' else 0))`
	 by (RW_TAC std_ss [FUN_EQ_THM]
	     ++ RW_TAC std_ss []
	     ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	     ++ (MP_TAC o Q.ISPEC `(a:num -> 'a -> bool) (x'':num)` o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.ISPECL [`(s':num -> bool)`, `m_space (m:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`, `(b :num -> 'a -> bool)`]) indicator_fn_split
	     ++ `a x'' SUBSET m_space m` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE]
	     ++ RW_TAC std_ss [])
  ++ POP_ORW
  ++ `!(i:num). i IN s ==> (Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) x') s' = SIGMA (\j. Normal (x i) * indicator_fn (a i INTER b j) x') s')`
         by (RW_TAC std_ss []
             ++ (MP_TAC o Q.SPECL [`(\j. indicator_fn ((a:num->'a->bool) i INTER b j) x')`,`x (i:num)`] o UNDISCH o Q.ISPEC `s':num->bool` o GSYM o INST_TYPE [alpha |-> ``:num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	     ++ RW_TAC std_ss [])
  ++ RW_TAC std_ss []
  ++ (MP_TAC o Q.ISPEC `(\n':num. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
                         indicator_fn ((\(i:num,j:num). a i INTER b j) (p n')) x')` o
               UNDISCH o Q.SPEC `p'` o UNDISCH o
               Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
               INST_TYPE [``:'b``|->``:num``]) EXTREAL_SUM_IMAGE_IMAGE
  ++ RW_TAC std_ss [o_DEF]
  ++ POP_ASSUM (K ALL_TAC)
  ++ RW_TAC std_ss [Once (Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)` EXTREAL_SUM_IMAGE_IN_IF)]
  ++ `!x''. (\j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') = (\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') x''` by METIS_TAC []
  ++ POP_ORW
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_IF_ELIM,EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE]
  ++ Suff `!x'''. x''' IN (s CROSS s') ==> ( (\x''. Normal (x (FST x'')) * indicator_fn (a (FST x'') INTER b (SND x'')) x') x''' = (\x''. if x'' IN s CROSS s' then Normal (max (x (FST x'')) (y (SND x''))) * indicator_fn ((\(i,j). a i INTER b j) x'') x' else 0) x''')`
  >> (RW_TAC std_ss []
      ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(s:num->bool) CROSS (s':num->bool)`) EXTREAL_SUM_IMAGE_EQ
      ++ RW_TAC std_ss []
      ++ DISJ1_TAC
      ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero])
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ Cases_on `x'''`
  ++ RW_TAC real_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ `q IN s` by METIS_TAC [IN_CROSS,FST,SND]
  ++ `x' IN (a q)` by METIS_TAC [IN_INTER]
  ++ `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s = Normal (x q)`
        by (`pos_simple_fn m f s a x` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
            ++ METIS_TAC [pos_simple_fn_thm1])
  ++ `r IN s'` by METIS_TAC [IN_CROSS,FST,SND]
  ++ `x' IN (b r)` by METIS_TAC [IN_INTER]
  ++ `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' = Normal (y r)`
        by (`pos_simple_fn m g s' b y` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
            ++ METIS_TAC [pos_simple_fn_thm1])
  ++ FULL_SIMP_TAC std_ss [extreal_le_def,max_def]);

val pos_simple_fn_not_infty = store_thm
("pos_simple_fn_not_infty",``!m f s a x. pos_simple_fn m f s a x ==> (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf)``,
  RW_TAC std_ss [pos_simple_fn_def]
  ++ `(!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) x') i <> NegInf)`
       by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
           ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ `(!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) x') i <> PosInf)`
       by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
           ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]);

(* ************************************************************************* *)
(* Properties of Integrals of Positive Simple Functions                      *)
(* ************************************************************************* *)

val pos_simple_fn_integral_add = store_thm
  ("pos_simple_fn_integral_add",
   ``!m f (s:num->bool) a x
        g (s':num->bool) b y.
	measure_space m /\
	pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
	?s'' c z. pos_simple_fn m (\x. f x + g x) s'' c z /\
		(pos_simple_fn_integral m s a x +
		 pos_simple_fn_integral m s' b y =
		 pos_simple_fn_integral m s'' c z)``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
   ++ RW_TAC std_ss [] ++ ASM_SIMP_TAC std_ss []
   ++ Q.EXISTS_TAC `k` ++ Q.EXISTS_TAC `c` ++ Q.EXISTS_TAC `(\i. z i + z' i)`
   ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def]
   ++ REVERSE CONJ_TAC
   >> (RW_TAC std_ss [GSYM REAL_SUM_IMAGE_ADD] ++ REAL_ARITH_TAC)
   ++ RW_TAC std_ss [REAL_LE_ADD,le_add,GSYM extreal_add_def]
   ++ (MP_TAC o Q.SPECL [`\i. Normal (z i) * indicator_fn ((c:num->'a->bool) i) (x':'a)`,`\i. Normal (z' i) * indicator_fn ((c:num->'a->bool) i) (x':'a)`] o GSYM o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_ADD
   ++ RW_TAC std_ss []
   ++ `SIGMA (\i. (Normal (z i) + Normal (z' i)) * indicator_fn (c i) x') k = SIGMA (\x. Normal (z x) * indicator_fn (c x) x' + Normal (z' x) * indicator_fn (c x) x') k`
         by (MATCH_MP_TAC ((UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_EQ)
       ++ RW_TAC std_ss [GSYM extreal_add_def]
       ++ METIS_TAC [add_rdistrib,extreal_le_def,extreal_of_num_def])
  ++ RW_TAC std_ss []);

val pos_simple_fn_integral_add_alt = store_thm
  ("pos_simple_fn_integral_add_alt", ``!m f s a x g y.	measure_space m /\
        pos_simple_fn m f s a x /\ pos_simple_fn m g s a y ==>
  	  (pos_simple_fn_integral m s a x +
           pos_simple_fn_integral m s a y =
 	   pos_simple_fn_integral m s a (\i. x i + y i))``,
  RW_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def,GSYM REAL_SUM_IMAGE_ADD]
  ++ REAL_ARITH_TAC);

val psfis_add = store_thm
  ("psfis_add",
   ``!m f g a b.
	measure_space m /\
	a IN psfis m f /\ b IN psfis m g ==>
	a + b IN psfis m (\x. f x + g x)``,
 RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 ++ Cases_on `x'` ++ Cases_on `x` ++ Cases_on `x''` ++ Cases_on `x'''`
 ++ Cases_on `r'` ++ Cases_on `r` ++ Cases_on `r''` ++ Cases_on `r'''`
 ++ RW_TAC std_ss []
 ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
 ++ Suff `?s a x. (pos_simple_fn_integral m q q''''' r' +
 	           pos_simple_fn_integral m q''' q''''''' r'' =
		   pos_simple_fn_integral m s a x) /\
	    pos_simple_fn m (\x. f x + g x) s a x`
 >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
     ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
     ++ RW_TAC std_ss [PAIR_EQ])
 ++ ONCE_REWRITE_TAC [CONJ_COMM]
 ++ MATCH_MP_TAC pos_simple_fn_integral_add ++ RW_TAC std_ss []);

val pos_simple_fn_integral_mono = store_thm
("pos_simple_fn_integral_mono",
   ``!m f (s:num->bool) a x
        g (s':num->bool) b y.
	measure_space m /\
	pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y /\
	(!x. x IN m_space m ==> f x <= g x) ==>
	pos_simple_fn_integral m s a x <= pos_simple_fn_integral m s' b y``,
  REPEAT STRIP_TAC
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
  ++ RW_TAC std_ss [] ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss [pos_simple_fn_integral_def]
  ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `k:num->bool`) REAL_SUM_IMAGE_MONO
  ++ RW_TAC std_ss []
  ++ Cases_on `c x' = {}`
  >> RW_TAC real_ss [MEASURE_EMPTY]
  ++ `pos_simple_fn m f k c z` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
  ++ `pos_simple_fn m g k c z'` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
  ++ `?t. t IN c x'` by METIS_TAC [CHOICE_DEF]
  ++ `f t = Normal (z x')` by METIS_TAC [pos_simple_fn_thm1]
  ++ `g t = Normal (z' x')` by METIS_TAC [pos_simple_fn_thm1]
  ++ `z x' <= z' x'` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF,extreal_le_def]
  ++ Cases_on `measure m (c x') = 0` >> RW_TAC real_ss []
  ++ MATCH_MP_TAC REAL_LE_RMUL_IMP
  ++ RW_TAC std_ss []
  ++ METIS_TAC [MEASURE_SPACE_POSITIVE,positive_def,REAL_LT_IMP_LE]);

val psfis_mono = store_thm
("psfis_mono", ``!m f g a b. measure_space m /\ a IN psfis m f /\ b IN psfis m g /\
	(!x. x IN m_space m ==> f x <= g x) ==>	a <= b``,
  RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
  ++ Cases_on `x'` ++ Cases_on `x` ++ Cases_on `x''` ++ Cases_on `x'''`
  ++ Cases_on `r'` ++ Cases_on `r` ++ Cases_on `r''` ++ Cases_on `r'''`
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
  ++ MATCH_MP_TAC pos_simple_fn_integral_mono
  ++ METIS_TAC []);

val pos_simple_fn_integral_unique = store_thm
 ("pos_simple_fn_integral_unique", ``!m f (s:num->bool) a x (s':num->bool) b y.
	measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m f s' b y ==>
	(pos_simple_fn_integral m s a x = pos_simple_fn_integral m s' b y)``,
   METIS_TAC [REAL_LE_ANTISYM,REAL_LE_REFL,le_antisym,le_refl, pos_simple_fn_integral_mono]);

val psfis_unique = store_thm
 ("psfis_unique", ``!m f a b.
	measure_space m /\ a IN psfis m f /\ b IN psfis m f ==>	(a = b)``,
   METIS_TAC [REAL_LE_ANTISYM,REAL_LE_REFL,le_antisym,le_refl, psfis_mono]);

val pos_simple_fn_integral_indicator = store_thm
 ("pos_simple_fn_integral_indicator", ``!m A. measure_space m /\ A IN measurable_sets m ==>
	(?s a x. pos_simple_fn m (indicator_fn A) s a x /\
		 (pos_simple_fn_integral m s a x = measure m A))``,
  RW_TAC std_ss []
  ++ Q.EXISTS_TAC `{0;1}`
  ++ Q.EXISTS_TAC `\i. if i = 0 then m_space m DIFF A else A`
  ++ Q.EXISTS_TAC `\i. if i = 0 then 0 else 1`
  ++ `{1:num} DELETE 0 = {1}` by RW_TAC real_ss [Once EXTENSION, IN_SING, IN_DELETE]
  ++ RW_TAC real_ss [pos_simple_fn_indicator_alt,pos_simple_fn_integral_def,REAL_SUM_IMAGE_THM,REAL_SUM_IMAGE_SING,FINITE_SING]);

val psfis_indicator = store_thm
  ("psfis_indicator",
   ``!m A. measure_space m /\ A IN measurable_sets m ==>
		measure m A IN psfis m (indicator_fn A)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Suff `?s a x. pos_simple_fn m (indicator_fn A) s a x /\
		    (pos_simple_fn_integral m s a x = measure m A)`
   >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [PAIR_EQ])
   ++ MATCH_MP_TAC pos_simple_fn_integral_indicator
   ++ ASM_REWRITE_TAC []);

val pos_simple_fn_integral_cmul = store_thm
 ("pos_simple_fn_integral_cmul", ``!m f s a x z. measure_space m /\ pos_simple_fn m f s a x /\ 0 <= z ==>
	    (pos_simple_fn m (\x. Normal z * f x) s a (\i. z * x i) /\
	    (pos_simple_fn_integral m s a (\i. z * x i) = z * pos_simple_fn_integral m s a x))``,
  RW_TAC std_ss [pos_simple_fn_integral_def, pos_simple_fn_def,REAL_LE_MUL,GSYM extreal_mul_def]
  << [METIS_TAC [extreal_le_def,le_mul,extreal_of_num_def],
      RW_TAC std_ss [(UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_CMUL,mul_assoc],
      RW_TAC std_ss [(UNDISCH o Q.ISPEC `s:num->bool` o GSYM) REAL_SUM_IMAGE_CMUL,REAL_MUL_ASSOC]]);

val psfis_cmul = store_thm
 ("psfis_cmul", ``!m f a z. measure_space m /\ a IN psfis m f /\ 0 <= z ==>
	z * a IN psfis m (\x. Normal z * f x)``,
  RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
  ++ Cases_on `x'`
  ++ Cases_on `r`
  ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
  ++ Q.EXISTS_TAC `(q,q',(\i. z * r' i))`
  ++ RW_TAC std_ss []
  >> METIS_TAC [pos_simple_fn_integral_cmul]
  ++ Q.EXISTS_TAC `(q,q',(\i. z * r' i))`
  ++ RW_TAC std_ss []
  ++ METIS_TAC [pos_simple_fn_integral_cmul]);

val pos_simple_fn_integral_cmul_alt = store_thm
("pos_simple_fn_integral_cmul_alt",``!m f s a x z. measure_space m /\ 0 <= z /\ pos_simple_fn m f s a x ==> (?s' a' x'. (pos_simple_fn m (\t. Normal z * f t) s' a' x') /\ (pos_simple_fn_integral m s' a' x' = z * pos_simple_fn_integral m s a x))``,
  RW_TAC real_ss []
  ++ Q.EXISTS_TAC `s` ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `(\i. z * x i)`
  ++ RW_TAC std_ss [pos_simple_fn_cmul_alt]
  ++ FULL_SIMP_TAC real_ss [pos_simple_fn_integral_def,pos_simple_fn_def,mul_assoc,GSYM extreal_mul_def,(UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_CMUL,(UNDISCH o Q.ISPEC `s:num->bool` o GSYM) REAL_SUM_IMAGE_CMUL,REAL_MUL_ASSOC]);

val IN_psfis = store_thm
  ("IN_psfis",
   ``!m r f. r IN psfis m f ==>	?s a x. pos_simple_fn m f s a x /\ (r = pos_simple_fn_integral m s a x)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Cases_on `x'`++ Cases_on `x` ++ Cases_on `r` ++ Cases_on `r'`
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
   ++ METIS_TAC []);

val IN_psfis_eq = store_thm
  ("IN_psfis_eq",
   ``!m r f. r IN psfis m f = ?s a x. pos_simple_fn m f s a x /\ (r = pos_simple_fn_integral m s a x)``,
   RW_TAC std_ss []
   ++ EQ_TAC
   >> RW_TAC std_ss [IN_psfis]
   ++ RW_TAC std_ss [psfis_def,psfs_def,IN_IMAGE,GSPECIFICATION]
   ++ Q.EXISTS_TAC `(s,a,x)`
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `(s,a,x)`
   ++ RW_TAC std_ss []);

val psfis_pos = store_thm
 ("psfis_pos",
   ``!m f a. measure_space m /\ a IN psfis m f ==> (!x. x IN m_space m ==> 0 <= f x)``,
  RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
  ++ Cases_on `x'`
  ++ Cases_on `r`
  ++ FULL_SIMP_TAC std_ss [PAIR_EQ,pos_simple_fn_def,REAL_SUM_IMAGE_POS]);

val pos_psfis = store_thm
  ("pos_psfis", ``!r m f. measure_space m /\ r IN psfis m f ==> 0 <= r``,
    REPEAT STRIP_TAC
    ++ `?s a x. pos_simple_fn m f s a x /\
			(r = pos_simple_fn_integral m s a x)`
	by METIS_TAC [IN_psfis]
    ++ RW_TAC std_ss [pos_simple_fn_integral_def] ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
    ++ METIS_TAC [pos_simple_fn_def, MEASURE_SPACE_POSITIVE,positive_def, REAL_LE_MUL]);

val pos_simple_fn_integral_zero = store_thm
("pos_simple_fn_integral_zero",``!m s a x. measure_space m /\ pos_simple_fn m (\t. 0) s a x ==> (pos_simple_fn_integral m s a x = 0)``,
  RW_TAC std_ss []
  ++ `pos_simple_fn m (\t. 0) {1:num} (\i:num. if i=1 then (m_space m) else {}) (\i:num. 0) /\
     (pos_simple_fn_integral m  {1:num} (\i:num. if i=1 then (m_space m) else {}) (\i:num. 0) = 0)`
      by  RW_TAC real_ss [pos_simple_fn_integral_def,
      pos_simple_fn_def,FINITE_SING, REAL_SUM_IMAGE_SING, EXTREAL_SUM_IMAGE_SING, IMAGE_SING,BIGUNION_SING,IN_SING,MEASURE_SPACE_MSPACE_MEASURABLE,GSYM extreal_of_num_def,mul_lzero,le_refl]
  ++ METIS_TAC [pos_simple_fn_integral_unique]);

val pos_simple_fn_integral_zero_alt = store_thm
("pos_simple_fn_integral_zero_alt",``!m s a x. measure_space m /\ pos_simple_fn m g s a x /\ (!x. x IN m_space m ==> (g x = 0))
                                      ==> (pos_simple_fn_integral m s a x = 0)``,
  RW_TAC std_ss [pos_simple_fn_integral_def]
  ++ `FINITE s` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
  ++ RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
  ++ Suff `(\i. if i IN s then x i * measure m (a i) else 0) = \x. 0`
  >> RW_TAC std_ss [REAL_SUM_IMAGE_0]
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ RW_TAC std_ss []
  ++ Cases_on `a x' = {}` >> FULL_SIMP_TAC real_ss [MEASURE_EMPTY]
  ++ Suff `x x' = 0` >> FULL_SIMP_TAC real_ss []
  ++ `?y. y IN a x'` by METIS_TAC [CHOICE_DEF]
  ++ `Normal (x x') = g y` by METIS_TAC [pos_simple_fn_thm1]
  ++ METIS_TAC [pos_simple_fn_thm1,MEASURE_SPACE_SUBSET_MSPACE,pos_simple_fn_def,SUBSET_DEF,extreal_of_num_def,extreal_11]);

val psfis_zero = store_thm
 ("psfis_zero", ``!m a. measure_space m ==> ((a IN psfis m (\x. 0)) = (a = 0))``,
  RW_TAC std_ss []
  ++ EQ_TAC  >> METIS_TAC [IN_psfis_eq,pos_simple_fn_integral_zero]
  ++ RW_TAC std_ss [IN_psfis_eq]
  ++ Q.EXISTS_TAC `{1}` ++ Q.EXISTS_TAC `(\i. m_space m)` ++ Q.EXISTS_TAC `(\i. 0)`
  ++ RW_TAC real_ss [pos_simple_fn_integral_def, pos_simple_fn_def,FINITE_SING,
 		     EXTREAL_SUM_IMAGE_SING, REAL_SUM_IMAGE_SING,IMAGE_SING,BIGUNION_SING,IN_SING,MEASURE_SPACE_MSPACE_MEASURABLE,mul_lzero,GSYM extreal_of_num_def,le_refl]);

val pos_simple_fn_integral_sum = store_thm
  ("pos_simple_fn_integral_sum",
   ``!m f s a x P. measure_space m /\
	(!i. i IN P ==> pos_simple_fn m (f i) s a (x i)) /\ FINITE P /\ P <> {} ==>
	(pos_simple_fn m (\t. SIGMA (\i. f i t) P) s a (\i. SIGMA (\j. x j i) P) /\
		    (pos_simple_fn_integral m s a (\j. SIGMA (\i. x i j) P) =
		     SIGMA (\i. pos_simple_fn_integral m s a (x i)) P))``,
  Suff `!P:'b->bool. FINITE P ==>
        (\P:'b->bool. !m f s a x. measure_space m /\
	(!i. i IN P ==> pos_simple_fn m (f i) s a (x i)) /\ P <> {} ==>
	(pos_simple_fn m (\t. SIGMA (\i. f i t) P) s a (\i. SIGMA (\j. x j i) P) /\
		    (pos_simple_fn_integral m s a (\j. SIGMA (\i. x i j) P) =
		     SIGMA (\i. pos_simple_fn_integral m s a (x i)) P))) P`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM,EXTREAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT,NOT_IN_EMPTY]
  >> (`(\t. f e t + SIGMA (\i. f i t) s) = (\t. (\t. f e t) t + (\t. SIGMA (\i. f i t) s) t)` by RW_TAC std_ss []
      ++ POP_ORW
      ++ `(\i. x e i + SIGMA (\j. x j i) s) = (\i. (\i. x e i) i + (\i. SIGMA (\j. x j i) s) i)` by RW_TAC std_ss []
      ++ POP_ORW
      ++ MATCH_MP_TAC pos_simple_fn_add_alt
      ++ RW_TAC std_ss [] >> METIS_TAC [IN_INSERT]
      ++ Cases_on `s <> {}` >> METIS_TAC [IN_INSERT]
      ++ FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_THM,REAL_SUM_IMAGE_THM,pos_simple_fn_def,IN_SING,le_refl,GSYM extreal_of_num_def,mul_lzero,EXTREAL_SUM_IMAGE_0])
  ++ Cases_on `s = {}` >> (RW_TAC real_ss [REAL_SUM_IMAGE_THM,REAL_SUM_IMAGE_THM] ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ `SIGMA (\i. pos_simple_fn_integral m s' a (x i)) s = pos_simple_fn_integral m s' a (\j. SIGMA (\i. x i j) s)`
      by METIS_TAC []
  ++ POP_ORW
  ++ `(\j. x e j + SIGMA (\i. x i j) s) =
      (\j. x e j + (\j. SIGMA (\i. x i j) s) j)` by METIS_TAC []
  ++ POP_ORW
  ++(MATCH_MP_TAC o GSYM) pos_simple_fn_integral_add_alt
  ++ METIS_TAC []);

val pos_simple_fn_integral_sum_alt = store_thm
  ("pos_simple_fn_integral_sum_alt",
   ``!m f s a x P. measure_space m /\
	(!i. i IN P ==> pos_simple_fn m (f i) (s i) (a i) (x i)) /\ FINITE P /\ P <> {} ==>
        ?c k z. (pos_simple_fn m (\t. SIGMA (\i. f i t) P) k c z /\
		(pos_simple_fn_integral m k c z =
		 SIGMA (\i. pos_simple_fn_integral m (s i) (a i) (x i)) P))``,

  Suff `!P:'b->bool. FINITE P ==>
        (\P:'b->bool. !m f s a x. measure_space m /\ (!i. i IN P ==> pos_simple_fn m (f i) (s i) (a i) (x i)) /\ P <> {} ==>
        ?c k z. (pos_simple_fn m (\t. SIGMA (\i. f i t) P) k c z /\
		(pos_simple_fn_integral m k c z =
		 SIGMA (\i. pos_simple_fn_integral m (s i) (a i) (x i)) P))) P`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM,EXTREAL_SUM_IMAGE_THM]
  ++ Cases_on `s = {}`
  >> (RW_TAC real_ss [REAL_SUM_IMAGE_SING,EMPTY_DELETE,REAL_SUM_IMAGE_THM,EXTREAL_SUM_IMAGE_THM,add_rzero]
     ++ METIS_TAC [IN_SING])
  ++ `?c k z. pos_simple_fn m (\t. SIGMA (\i. f i t) s) k c z /\
        (pos_simple_fn_integral m k c z =
         SIGMA (\i. pos_simple_fn_integral m (s' i) (a i) (x i)) s)`
        by METIS_TAC [IN_INSERT]
  ++ (MP_TAC o Q.SPECL [`m`,`f (e:'b)`,`s' (e:'b)`,`a (e:'b)`,`x (e:'b)`,`(\t. SIGMA (\i:'b. f i t) s)`,`k`,`c`,`z`]) pos_simple_fn_integral_present
  ++ FULL_SIMP_TAC std_ss [IN_INSERT,DELETE_NON_ELEMENT]
  ++ RW_TAC std_ss []
  ++ METIS_TAC [pos_simple_fn_integral_add]);

val psfis_sum = store_thm
  ("psfis_sum",
   ``!m f a P.	measure_space m /\ (!i. i IN P ==> a i IN psfis m (f i)) /\ FINITE P ==>
	(SIGMA a P) IN psfis m (\t. SIGMA (\i. f i t) P)``,
  Suff `!P:'b->bool. FINITE P ==>
        (\P:'b->bool. !m f a. measure_space m /\ (!i. i IN P ==> a i IN psfis m (f i)) ==>
	(SIGMA a P) IN psfis m (\t. SIGMA (\i. f i t) P)) P`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,REAL_SUM_IMAGE_THM,psfis_zero,DELETE_NON_ELEMENT, IN_INSERT]
  ++ `!t. (\i. f i t) = (\i. (\i. f i t) i)` by METIS_TAC []
  ++ POP_ORW
  ++ `(\t. f e t + SIGMA (\i. f i t) s) = (\t. f e t + (\t. SIGMA (\i. f i t) s) t)`
       by METIS_TAC []
  ++ POP_ORW
  ++ METIS_TAC [psfis_add]);

val psfis_intro = store_thm
 ("psfis_intro",
   ``!m a x P. measure_space m /\ (!i. i IN P ==> a i IN measurable_sets m) /\ (!i. i IN P ==> 0 <= x i) /\
	FINITE P ==> (SIGMA (\i. (x i) * measure m (a i)) P) IN psfis m (\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) P)``,
  RW_TAC std_ss []
  ++ `!t. (\i. Normal (x i) * indicator_fn (a i) t) =
	   (\i. (\i t. Normal (x i) * indicator_fn (a i) t) i t)`
	by METIS_TAC []
  ++ POP_ORW
  ++ MATCH_MP_TAC psfis_sum
  ++ RW_TAC std_ss []
  ++ METIS_TAC [psfis_cmul, psfis_indicator]);

val pos_simple_fn_integral_sub = store_thm
  ("pos_simple_fn_integral_sub",
   ``!m f s a x g s' b y.
	measure_space m /\ (!x. g x <= f x) /\
	pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
	?s'' c z. pos_simple_fn m (\x. f x - g x) s'' c z /\
		(pos_simple_fn_integral m s a x -
		 pos_simple_fn_integral m s' b y =
		 pos_simple_fn_integral m s'' c z)``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
   ++ RW_TAC std_ss [] ++ ASM_SIMP_TAC std_ss []
   ++ Q.EXISTS_TAC `k`
   ++ Q.EXISTS_TAC `c`
   ++ Q.EXISTS_TAC `(\i. if (i IN k /\ ~(c i = {})) then (z i - z' i) else 0)`
   ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def]
   ++ `pos_simple_fn m f k c z` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
   ++ `pos_simple_fn m g k c z'` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
   ++ `!x. k x = x IN k` by METIS_TAC [SPECIFICATION]
   ++ REVERSE CONJ_TAC
   >> (`!i. ((if (i IN k /\ ~(c i = {})) then z i - z' i else 0) * measure m (c i)) =
	(if i IN k then (z i - z' i) * measure m (c i) else 0)`
		by (RW_TAC std_ss [] ++ FULL_SIMP_TAC real_ss [MEASURE_EMPTY])
	++ POP_ORW
        ++ RW_TAC std_ss [Once real_sub,Once REAL_NEG_MINUS1,GSYM REAL_SUM_IMAGE_CMUL,GSYM REAL_SUM_IMAGE_IN_IF,GSYM REAL_SUM_IMAGE_ADD] ++ REAL_ARITH_TAC)
  ++ CONJ_TAC
  >> METIS_TAC [sub_zero_le]
  ++ REVERSE (RW_TAC real_ss [])
  >> (`?q. q IN c i` by METIS_TAC [CHOICE_DEF]
      ++ METIS_TAC [pos_simple_fn_thm1,REAL_SUB_LE,extreal_le_def])
  ++ `!i. (Normal (if (i IN k /\ ~(c i = {})) then z i - z' i else 0) * indicator_fn (c i) x') =
	(if i IN k then Normal (z i - z' i) * indicator_fn (c i) x' else 0)`
	by (RW_TAC std_ss [] ++ FULL_SIMP_TAC real_ss [indicator_fn_def,mul_rzero,mul_rone,NOT_IN_EMPTY] ++ METIS_TAC [mul_lzero,extreal_of_num_def])
  ++ POP_ORW
  ++ RW_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_IN_IF]
  ++ RW_TAC std_ss [GSYM extreal_sub_def]
  ++ (MP_TAC o Q.SPEC `(\i. (Normal (z i) - Normal (z' i)) * indicator_fn (c i) x')` o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x. x IN k ==> (\i. (Normal (z i) - Normal (z' i)) * indicator_fn (c i) x') x <> NegInf`
        by (RW_TAC std_ss [extreal_sub_def,indicator_fn_def,mul_rzero,mul_rone]
            ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ `!x. x IN k ==> ((Normal (z x) - Normal (z' x)) * indicator_fn (c x) x' =
         Normal (z x) *  indicator_fn (c x) x' - Normal (z' x) *   indicator_fn (c x) x')`
            by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,sub_rzero]
  ++ RW_TAC std_ss []
  ++ NTAC 3 (POP_ASSUM (K ALL_TAC))

  ++ (MP_TAC o Q.SPEC `(\x:num. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x')` o UNDISCH o Q.SPEC `k` o GSYM o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x. NegInf <> (\x. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x') x`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,sub_rzero,extreal_sub_def]
            ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss []
  ++ `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s =
      SIGMA (\i. Normal (z i) * indicator_fn (c i) x') k` by METIS_TAC []
  ++ `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' =
      SIGMA (\i. Normal (z' i) * indicator_fn (c i) x') k` by METIS_TAC []
  ++ POP_ORW
  ++ POP_ORW
  ++ `(\x. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x') =
      (\x. (\x. Normal (z x) * indicator_fn (c x) x') x - (\x. Normal (z' x) * indicator_fn (c x) x') x)` by METIS_TAC []
  ++ POP_ORW
  ++ (MATCH_MP_TAC o UNDISCH o Q.SPEC `k` o GSYM o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_SUB
  ++ DISJ1_TAC
  ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty]);

val psfis_sub = store_thm
  ("psfis_sub",
   ``!m f g a b.
	measure_space m /\ (!x. g x <= f x) /\
	a IN psfis m f /\ b IN psfis m g ==>
	a - b IN psfis m (\x. f x - g x)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Cases_on `x'` ++ Cases_on `x` ++ Cases_on `x''` ++ Cases_on `x'''`
   ++ RW_TAC std_ss []
   ++ Cases_on `r'` ++ Cases_on `r` ++ Cases_on `r''` ++ Cases_on `r'''`
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
   ++ Suff `?s a x. (pos_simple_fn_integral m q q''''' r' -
		      pos_simple_fn_integral m q''' q''''''' r'' =
		      pos_simple_fn_integral m s a x) /\
	    pos_simple_fn m (\x. f x - g x) s a x`
   >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [PAIR_EQ])
   ++ ONCE_REWRITE_TAC [CONJ_COMM]
   ++ MATCH_MP_TAC pos_simple_fn_integral_sub ++ RW_TAC std_ss []);



(* ------------------------------------------------------------ *)
(*    Properties of Integrals of Positive Functions  - Part 1   *)
(* ------------------------------------------------------------ *)

val pos_fn_integral_pos_simple_fn = store_thm
("pos_fn_integral_pos_simple_fn",``!m f s a x. measure_space m /\ pos_simple_fn m f s a x ==> (pos_fn_integral m f = pos_simple_fn_integral m s a x)``,
  RW_TAC std_ss [pos_fn_integral_def]
  ++ MATCH_MP_TAC REAL_SUP_MAX
  ++ RW_TAC std_ss []
  >> (ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ METIS_TAC [IN_psfis_eq,le_refl])
  ++ POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)])
  ++ RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
  ++ METIS_TAC [pos_simple_fn_integral_mono]);

val pos_fn_integral_mspace = store_thm
  ("pos_fn_integral_mspace",``!m f. measure_space m  /\ (!x. x IN m_space m ==> 0 <= f x)
	 ==> (pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn (m_space m) x))``,
  RW_TAC std_ss [pos_fn_integral_def,indicator_fn_def,mul_rzero,mul_rone]);

val pos_fn_integral_zero = store_thm
("pos_fn_integral_zero",``!m. measure_space m ==> (pos_fn_integral m (\x. 0) = 0)``,
  RW_TAC std_ss [pos_fn_integral_def]
  ++ MATCH_MP_TAC REAL_SUP_MAX
  ++ RW_TAC std_ss []
  >> (ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
      ++ Q.EXISTS_TAC `\x. 0`
      ++ METIS_TAC [psfis_zero,le_refl,IN_psfis_eq])
  ++ POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)])
  ++ RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
  ++ `!x. x IN m_space m ==> (g x = 0)` by METIS_TAC  [le_antisym,pos_simple_fn_def]
  ++ METIS_TAC [REAL_LE_REFL,pos_simple_fn_integral_zero_alt]);


(* ---------------------------------------------------- *)
(*             Properties of Integrability              *)
(* ---------------------------------------------------- *)

val fn_plus_integrable = store_thm
  ("fn_plus_integrable",
   ``!m f. measure_space m /\ integrable m f ==> integrable m (fn_plus f)``,
 	RW_TAC std_ss [integrable_def]
	<< [METIS_TAC [IN_MEASURABLE_BOREL_FN_PLUS],
	    `fn_plus (fn_plus f) = fn_plus f` by METIS_TAC [FN_PLUS_POS_ID,FN_PLUS_POS]
	    ++ METIS_TAC [],
	    `fn_minus (fn_plus f) = (\x. 0)` by METIS_TAC [FN_MINUS_POS_ZERO,FN_PLUS_POS]
	    ++ POP_ORW
	    ++ Q.EXISTS_TAC `0`
	    ++ RW_TAC std_ss [GSPECIFICATION]
	    ++ `!x. x IN m_space m ==> (g x = 0)` by METIS_TAC [pos_simple_fn_def,le_antisym,IN_psfis_eq]
	    ++ METIS_TAC [REAL_LE_REFL,pos_simple_fn_integral_zero_alt,IN_psfis_eq]]);

val fn_minus_integrable = store_thm
  ("fn_minus_integrable",
   ``!m f. measure_space m /\ integrable m f ==> integrable m (fn_minus f)``,
 	RW_TAC std_ss [integrable_def]
	<< [METIS_TAC [IN_MEASURABLE_BOREL_FN_MINUS],
	    `fn_plus (fn_minus f) = fn_minus f` by METIS_TAC [FN_MINUS_POS,FN_PLUS_POS_ID]
	    ++ METIS_TAC [],
 	    `fn_minus (fn_minus f) = (\x. 0)` by METIS_TAC [FN_MINUS_POS,FN_MINUS_POS_ZERO]
	    ++ POP_ORW
	    ++ Q.EXISTS_TAC `0`
	    ++ RW_TAC std_ss [GSPECIFICATION]
	    ++ `!x. x IN m_space m ==> (g x = 0)` by METIS_TAC [pos_simple_fn_def,le_antisym,IN_psfis_eq]
	    ++ METIS_TAC [REAL_LE_REFL,pos_simple_fn_integral_zero_alt,IN_psfis_eq]]);

val integrable_mspace = store_thm
  ("integrable_mspace",``!m f. measure_space m  ==>
                      (integrable m f = integrable m (\x. f x * indicator_fn (m_space m) x))``,
  RW_TAC std_ss [integrable_def]
  ++ `f IN measurable (m_space m,measurable_sets m) Borel =
      (\x. f x * indicator_fn (m_space m) x) IN measurable (m_space m,measurable_sets m) Borel`
       by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ,measure_space_def,m_space_def,
       	  	     measurable_sets_def,space_def,subsets_def]
  ++ `!g. (!x. x IN m_space m ==> g x <= fn_plus (\x. f x * indicator_fn (m_space m) x) x) =
          (!x. x IN m_space m ==> g x <= fn_plus f x)`
           by (RW_TAC std_ss [indicator_fn_def]
	       ++ EQ_TAC
	       >> (RW_TAC std_ss []
      	       	   ++ `fn_plus (\x'. f x' * if x' IN m_space m then 1 else 0) x = fn_plus f x`
          	       by RW_TAC std_ss [mul_rone,fn_plus_def]
      		   ++ METIS_TAC [])
               ++ RW_TAC std_ss [fn_plus_def,mul_rone])
  ++ `!g. (!x. x IN m_space m ==> g x <= fn_minus (\x. f x * indicator_fn (m_space m) x) x) =
          (!x. x IN m_space m ==> g x <= fn_minus f x)`
           by (RW_TAC std_ss [indicator_fn_def]
	       ++ EQ_TAC
	       >> (RW_TAC std_ss []
      	       	   ++ `fn_minus (\x'. f x' * if x' IN m_space m then 1 else 0) x = fn_minus f x`
          	       by RW_TAC std_ss [mul_rone,fn_minus_def]
      		   ++ METIS_TAC [])
               ++ RW_TAC std_ss [fn_minus_def,mul_rone])
  ++ RW_TAC std_ss []);

val integrable_pos = store_thm
  ("integrable_pos",``!m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) ==>
                     (integrable m f = f IN measurable (m_space m, measurable_sets m) Borel /\
		     (?z.!r. r IN {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f x} ==> r <= z))``,
  RW_TAC std_ss [Once integrable_mspace,integrable_def]
  ++ `!x. 0 <= (\x. f x * indicator_fn (m_space m) x) x` by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
  ++ FULL_SIMP_TAC std_ss [FN_PLUS_POS_ID,FN_MINUS_POS_ZERO]
  ++ `f IN measurable (m_space m,measurable_sets m) Borel =
      (\x. f x * indicator_fn (m_space m) x) IN measurable (m_space m,measurable_sets m) Borel`
       by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ,measure_space_def,m_space_def,
       	  	     measurable_sets_def,space_def,subsets_def]
  ++ EQ_TAC
  >> RW_TAC std_ss [GSPECIFICATION,indicator_fn_def,mul_rzero,mul_rone]
  ++ RW_TAC std_ss [GSPECIFICATION,indicator_fn_def,mul_rzero,mul_rone]
  ++ Q.EXISTS_TAC `0`
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ `!x. x IN m_space m ==> (g x = 0)` by METIS_TAC [pos_simple_fn_def,le_antisym,IN_psfis_eq]
  ++ METIS_TAC [REAL_LE_REFL,pos_simple_fn_integral_zero_alt,IN_psfis_eq]);

val pos_fn_integral_mono = store_thm
  ("pos_fn_integral_mono",
   ``!m f1 f2. measure_space m /\ integrable m f1 /\ integrable m f2 /\
		(!x. x IN m_space m ==> f1 x <= f2 x) /\
		(!x. x IN m_space m ==> 0 <= f1 x)
		 ==> (pos_fn_integral m f1 <= pos_fn_integral m f2)``,
  RW_TAC std_ss [pos_fn_integral_def]
  ++ `!x. x IN m_space m ==> 0 <= f2 x` by METIS_TAC [le_trans]
  ++ MATCH_MP_TAC REAL_IMP_SUP_LE
  ++ RW_TAC std_ss []
  >> (Q.EXISTS_TAC `0`
	++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	++ RW_TAC std_ss [GSPECIFICATION]
	++ Q.EXISTS_TAC `(\x. 0)`
	++ METIS_TAC [psfis_zero,SPECIFICATION])
  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ `?g1. r IN psfis m g1 /\ (!t. t IN m_space m ==> g1 t <= f2 t)` by METIS_TAC [le_trans]
  ++ `r IN {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f2 x}`
      by (RW_TAC std_ss [GSPECIFICATION] ++ METIS_TAC [])
  ++ Suff `?z. !r. r IN {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f2 x} ==> r <= z  `
  >> PROVE_TAC [REAL_SUP_UBOUND_LE,SPECIFICATION]
  ++ METIS_TAC [integrable_pos]);

val integrable_bounded = store_thm
  ("integrable_bounded", ``!m f g. measure_space m /\ integrable m f /\
                           (!x. x IN m_space m ==> abs(g x) <= f x) /\
	                   g IN measurable (m_space m,measurable_sets m) Borel
	                      ==> integrable m g``,
  RW_TAC std_ss [integrable_def,GSPECIFICATION,abs_bounds]
  >> (Q.EXISTS_TAC `z`
      ++ RW_TAC std_ss []
      ++ `!x. x IN m_space m ==> fn_plus g x <= fn_plus f x` by (RW_TAC std_ss [fn_plus_def,lt_imp_le,le_refl] ++ METIS_TAC [lte_trans])
      ++ `!x. x IN m_space m ==> g' x <= fn_plus f x` by METIS_TAC [le_trans]
      ++ METIS_TAC [])
  ++ Q.EXISTS_TAC `z`
  ++ RW_TAC std_ss []
  ++  `!x. x IN m_space m ==> fn_minus g x <= fn_plus f x`
	by (RW_TAC real_ss [fn_minus_def,fn_plus_def,lt_imp_le,le_refl]
	    >> METIS_TAC [le_neg,neg_neg]
	    ++ METIS_TAC [extreal_lt_def,le_neg,neg_0,lte_trans])
  ++  `!x. x IN m_space m ==> g' x <= fn_plus f x` by METIS_TAC [le_trans]
  ++ METIS_TAC []);

val integrable_plus_minus = store_thm
  ("integrable_plus_minus", ``!m f. measure_space m ==> (integrable m f =
		(f IN measurable (m_space m,measurable_sets m) Borel /\
                 integrable m (fn_plus f) /\ integrable m (fn_minus f)))``,
  RW_TAC std_ss [integrable_def,FN_PLUS_POS_ID,FN_PLUS_POS,FN_MINUS_POS_ZERO,FN_MINUS_POS]
  ++ EQ_TAC
  >> (RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS]
      ++ Q.EXISTS_TAC `0`
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ `!x. x IN m_space m ==> (g x = 0)` by METIS_TAC [pos_simple_fn_def,le_antisym,IN_psfis_eq]
      ++ METIS_TAC [REAL_LE_REFL,pos_simple_fn_integral_zero_alt,IN_psfis_eq])
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS]);

val pos_simple_fn_integrable = store_thm
  ("pos_simple_fn_integrable",
   ``!m f s a x. (measure_space m) /\ (pos_simple_fn m f s a x) ==> integrable m f``,

  RW_TAC std_ss []
  ++ `f IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [IN_MEASURABLE_BOREL_POS_SIMPLE_FN]
  ++ `!x. x IN m_space m ==> 0 <= f x` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
  ++ RW_TAC std_ss [integrable_pos]
  ++ Q.EXISTS_TAC `pos_simple_fn_integral m s a x`
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ FULL_SIMP_TAC real_ss [IN_psfis_eq]
  ++ METIS_TAC [pos_simple_fn_integral_mono]);

val indicator_fn_integrable = store_thm
  ("indicator_fn_integrable",
     ``!m A. (measure_space m) /\ (A IN measurable_sets m) ==> integrable m (indicator_fn A)``,
  RW_TAC real_ss []
  ++ `?s a x. pos_simple_fn m (indicator_fn A) s a x` by METIS_TAC [pos_simple_fn_indicator]
  ++ METIS_TAC [pos_simple_fn_integrable]);


val integrable_cmul = store_thm
    ("integrable_cmul",``!m c f. measure_space m /\ integrable m f
			==> (integrable m (\x. Normal c * f x))``,
  RW_TAC std_ss []
  ++ `(\x. Normal c * f x) IN measurable (m_space m, measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL ++ METIS_TAC [integrable_def,measure_space_def,space_def])
  ++ FULL_SIMP_TAC std_ss [integrable_def, GSPECIFICATION]
  ++ RW_TAC std_ss []
  >> ( Cases_on `c = 0`
       >> (RW_TAC std_ss [GSYM extreal_of_num_def,mul_lzero]
            ++ `fn_plus (\x. 0) = (\x. 0)` by RW_TAC std_ss [fn_plus_def]
	    ++ Q.EXISTS_TAC `0`
	    ++ RW_TAC std_ss []
	    ++ `!x. x IN m_space m ==> (g x = 0)` by METIS_TAC [pos_simple_fn_def,le_antisym,IN_psfis_eq]
	    ++ METIS_TAC [pos_simple_fn_integral_zero_alt,IN_psfis_eq,REAL_LE_REFL])
	++ Cases_on `0 <= c`
	>> (`0 < c` by METIS_TAC [REAL_LE_LT]
	    ++ Q.EXISTS_TAC `c*z`
	    ++ RW_TAC std_ss []
	    ++ `(inv (c) * r) IN psfis m (\x. Normal (inv c) * g x)` by METIS_TAC [psfis_cmul,REAL_LE_INV]
	    ++ `fn_plus (\x. Normal c * f x) = (\x. Normal c * fn_plus f x)` by FULL_SIMP_TAC std_ss [FN_PLUS_CMUL]
	    ++ FULL_SIMP_TAC std_ss []
	    ++ `!x. x IN m_space m ==> (\x. Normal (inv c) * g x) x <= fn_plus f x`
		   by RW_TAC std_ss [mul_comm,GSYM extreal_div_def,GSYM extreal_inv_def,GSYM le_ldiv]
	    ++ ONCE_REWRITE_TAC [REAL_MUL_COMM]
	    ++ Q.PAT_ASSUM `!r. (?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= fn_plus f x) ==> r <= z`
		 (MP_TAC o Q.SPEC `inv c * r`)
	    ++ RW_TAC std_ss []
	    ++ `inv c * r <= z` by (POP_ASSUM MATCH_MP_TAC
                                    ++ Q.EXISTS_TAC `(\x. Normal (inv c) * g x)`
                                    ++ RW_TAC std_ss [])
	    ++ METIS_TAC [REAL_LE_LDIV_EQ,real_div,REAL_MUL_COMM])
	++ FULL_SIMP_TAC std_ss [GSYM real_lt]
	++ `fn_plus (\x. Normal c * f x) = (\x. Normal (-c) * fn_minus f x)`
            by METIS_TAC [REAL_LT_IMP_LE,extreal_ainv_def,FN_PLUS_CMUL]
	++ Q.EXISTS_TAC `-c * z'`
	++ RW_TAC std_ss []
	++ `0 < (-c)` by METIS_TAC [REAL_LT_NEG,REAL_NEG_0]
	++ `0 <= inv (-c)` by METIS_TAC [REAL_LE_INV,REAL_LT_IMP_LE]
	++ `(inv (-c) * r) IN psfis m (\x. Normal (inv (-c)) * g x)` by METIS_TAC [psfis_cmul]
	++ `!x. x IN m_space m ==> (\x. Normal (inv (-c)) * g x) x <= fn_minus f x`
		   by RW_TAC std_ss [mul_comm,GSYM extreal_div_def,GSYM extreal_inv_def,GSYM le_ldiv]
	++ ONCE_REWRITE_TAC [REAL_NEG_LMUL]
	++ ONCE_REWRITE_TAC [REAL_MUL_COMM]
	++ Q.PAT_ASSUM `!r. (?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= fn_minus f x) ==> r <= z'`
		 (MP_TAC o Q.SPEC `inv (-c) * r`)
	++ RW_TAC std_ss []
	++ `inv (-c) * r <= z'` by (POP_ASSUM MATCH_MP_TAC
                                    ++ Q.EXISTS_TAC `(\x. Normal (inv (-c)) * g x)`
				    ++ RW_TAC std_ss [])
	++ METIS_TAC [REAL_LE_LDIV_EQ,real_div,REAL_MUL_COMM])
  ++ Cases_on `c = 0`
  >> (RW_TAC std_ss [GSYM extreal_of_num_def,mul_lzero]
      ++ `fn_minus (\x. 0) = (\x. 0)` by RW_TAC std_ss [fn_minus_def,neg_0]
      ++ Q.EXISTS_TAC `0`
      ++ RW_TAC std_ss []
      ++ `!x. x IN m_space m ==> (g x = 0)` by METIS_TAC [pos_simple_fn_def,le_antisym,IN_psfis_eq]
      ++ METIS_TAC [pos_simple_fn_integral_zero_alt,IN_psfis_eq,REAL_LE_REFL])
  ++ Cases_on `0 <= c`
  >> (`0 < c` by METIS_TAC [REAL_LE_LT]
     ++ Q.EXISTS_TAC `c*z'`
     ++ RW_TAC std_ss []
     ++ `(inv (c) * r) IN psfis m (\x. Normal (inv c) * g x)` by METIS_TAC [psfis_cmul,REAL_LE_INV]
     ++ `fn_minus (\x. Normal c * f x) = (\x. Normal c * fn_minus f x)` by FULL_SIMP_TAC std_ss [FN_MINUS_CMUL]
     ++ FULL_SIMP_TAC std_ss []
     ++ `!x. x IN m_space m ==> (\x. Normal (inv c) * g x) x <= fn_minus f x`
	   by RW_TAC std_ss [mul_comm,GSYM extreal_div_def,GSYM extreal_inv_def,GSYM le_ldiv]
     ++ ONCE_REWRITE_TAC [REAL_MUL_COMM]
     ++ Q.PAT_ASSUM `!r. (?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= fn_minus f x) ==> r <= z'`
	    (MP_TAC o Q.SPEC `inv c * r`)
     ++ RW_TAC std_ss []
     ++ `inv c * r <= z'` by (POP_ASSUM MATCH_MP_TAC
                              ++ Q.EXISTS_TAC `(\x. Normal (inv c) * g x)`
                              ++ RW_TAC std_ss [])
     ++ METIS_TAC [REAL_LE_LDIV_EQ,real_div,REAL_MUL_COMM])
  ++ FULL_SIMP_TAC std_ss [GSYM real_lt]
  ++ `fn_minus (\x. Normal c * f x) = (\x. Normal (-c) * fn_plus f x)`
            by METIS_TAC [REAL_LT_IMP_LE,extreal_ainv_def,FN_MINUS_CMUL]
  ++ Q.EXISTS_TAC `-c * z`
  ++ RW_TAC std_ss []
  ++ `0 < (-c)` by METIS_TAC [REAL_LT_NEG,REAL_NEG_0]
  ++ `0 <= inv (-c)` by METIS_TAC [REAL_LE_INV,REAL_LT_IMP_LE]
  ++ `(inv (-c) * r) IN psfis m (\x. Normal (inv (-c)) * g x)` by METIS_TAC [psfis_cmul]
  ++ `!x. x IN m_space m ==> (\x. Normal (inv (-c)) * g x) x <= fn_plus f x`
	   by RW_TAC std_ss [mul_comm,GSYM extreal_div_def,GSYM extreal_inv_def,GSYM le_ldiv]
  ++ ONCE_REWRITE_TAC [REAL_NEG_LMUL]
  ++ ONCE_REWRITE_TAC [REAL_MUL_COMM]
  ++ Q.PAT_ASSUM `!r. (?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= fn_plus f x) ==> r <= z`
	 (MP_TAC o Q.SPEC `inv (-c) * r`)
  ++ RW_TAC std_ss []
  ++ `inv (-c) * r <= z` by (POP_ASSUM MATCH_MP_TAC
                             ++ Q.EXISTS_TAC `(\x. Normal (inv (-c)) * g x)`
		 	     ++ RW_TAC std_ss [])
  ++ METIS_TAC [REAL_LE_LDIV_EQ,real_div,REAL_MUL_COMM]);

val integrable_const = store_thm
  ("integrable_const", ``!m k. measure_space m ==> integrable m (\x. Normal k)``,
  RW_TAC std_ss []
  ++ Cases_on `0 <= k`
  >> (`pos_simple_fn m (\x. Normal k) {1:num} (\i. m_space m) (\i. k)`
	 by RW_TAC real_ss [pos_simple_fn_def,FINITE_SING,IN_SING,BIGUNION_SING,IMAGE_SING,MEASURE_SPACE_MSPACE_MEASURABLE,extreal_le_def,extreal_of_num_def,EXTREAL_SUM_IMAGE_SING,indicator_fn_def,mul_rone,extreal_mul_def]
      ++ METIS_TAC [pos_simple_fn_integrable])
  ++ FULL_SIMP_TAC std_ss [GSYM real_lt]
  ++ `pos_simple_fn m (\x. Normal (-k)) {1:num} (\i. m_space m) (\i. -k)`
	by (RW_TAC real_ss [pos_simple_fn_def,FINITE_SING,IN_SING,BIGUNION_SING,IMAGE_SING,MEASURE_SPACE_MSPACE_MEASURABLE,extreal_le_def,extreal_of_num_def,EXTREAL_SUM_IMAGE_SING,indicator_fn_def,mul_rone,extreal_mul_def]
	    ++ METIS_TAC [REAL_LT_NEG,REAL_NEG_0,REAL_LT_IMP_LE])
  ++ `integrable m (\x. Normal (-k))` by METIS_TAC [pos_simple_fn_integrable]
  ++ `(\x. Normal k) = (\x. Normal (-1) * (\k. Normal (-k)) k)`
         by RW_TAC real_ss [FUN_EQ_THM,extreal_mul_def]
  ++ RW_TAC std_ss [integrable_cmul]);

val pos_fn_integral_pos = store_thm
("pos_fn_integral_pos",``!m f. measure_space m /\ integrable m f /\ (!x. x IN m_space m ==> 0 <= f x)
                          ==> 0 <= pos_fn_integral m f``,
  RW_TAC std_ss [pos_fn_integral_mspace]
  ++ `0 = pos_fn_integral m (\x. 0)` by METIS_TAC [pos_fn_integral_zero]
  ++ POP_ORW
  ++ MATCH_MP_TAC pos_fn_integral_mono
  ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [measure_space_def]
  ++ CONJ_TAC >> RW_TAC std_ss [integrable_const,extreal_of_num_def]
  ++ CONJ_TAC >> METIS_TAC [integrable_mspace]
  ++ RW_TAC std_ss [le_refl,indicator_fn_def,mul_rzero,mul_rone]);

val pos_fn_integral_indicator = store_thm
  ("pos_fn_integral_indicator",
   ``!m s. measure_space m /\ s IN measurable_sets m ==>
	   (pos_fn_integral m (indicator_fn s) = measure m s)``,
  METIS_TAC [pos_fn_integral_pos_simple_fn,pos_simple_fn_integral_indicator]);



(***************************************************************************)
(*                       Sequences - Convergence                           *)
(***************************************************************************)

val psfis_mono_conv_mono_borel = store_thm
  ("psfis_mono_conv_mono_borel",
   ``!m f fi ri r g r'.
	measure_space m /\
	(f IN measurable (m_space m,measurable_sets m) Borel) /\
	(!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
	(!i. (ri i) IN psfis m (fi i)) /\
	(ri --> r) /\
	(r' IN psfis m g) /\
	(!x. x IN m_space m ==> g x <= f x) ==>
	r' <= r``,
   REPEAT STRIP_TAC
   ++ `?s a x. pos_simple_fn m g s a x`
	by METIS_TAC [IN_psfis]
   ++ `mono_increasing ri`
	by (FULL_SIMP_TAC std_ss [mono_increasing_def,ext_mono_increasing_def]
	    ++ REPEAT STRIP_TAC ++ MATCH_MP_TAC psfis_mono
	    ++ METIS_TAC [])
   ++ `!i. ri i <= r`
	by METIS_TAC [mono_increasing_def, SEQ_MONO_LE, DECIDE ``!n:num. n <= n + 1``]
   ++ `!i. ?s a x. pos_simple_fn m (fi i) s a x /\
		   ((ri i) = pos_simple_fn_integral m s a x)`
	by METIS_TAC [IN_psfis]
   ++ MATCH_MP_TAC REAL_LE_MUL_EPSILON
   ++ RW_TAC std_ss []
   ++ Q.ABBREV_TAC `b = \n. {t | Normal z * g t <= (fi n) t}`
   ++ `!i. 0 <= ri i`
	by METIS_TAC [pos_psfis,MEASURE_SPACE_POSITIVE]
   ++ `!i x. x IN m_space m ==> 0 <= fi i x` by METIS_TAC [psfis_pos]
   ++ `!i. (fi i) IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [IN_psfis_eq,IN_MEASURABLE_BOREL_POS_SIMPLE_FN]
   ++ `g IN measurable (m_space m,measurable_sets m) Borel`
	by METIS_TAC [IN_MEASURABLE_BOREL_POS_SIMPLE_FN,IN_psfis]
   ++ `(\t. Normal z * g t) IN measurable (m_space m, measurable_sets m) Borel`
	by ( MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
	     ++ Q.EXISTS_TAC `g` ++ Q.EXISTS_TAC `z`
	     ++ RW_TAC real_ss []
	     ++ METIS_TAC [measure_space_def] )
   ++ `!n:num. {t | Normal z * g t <= fi n t} INTER m_space m = {t | Normal z * (g t) - (fi n t) <= 0} INTER m_space m`
	by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
	    ++ METIS_TAC [sub_le_zero,pos_simple_fn_not_infty])
   ++ `!n. (\t. Normal z * g t - fi n t) IN measurable (m_space m, measurable_sets m) Borel`
	by ( RW_TAC std_ss []
      	     ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
	     ++ Q.EXISTS_TAC `(\t. Normal z * g t)`
	     ++ Q.EXISTS_TAC `fi n`
	     ++ RW_TAC std_ss []
	     ++ METIS_TAC [measure_space_def])
   ++ `!n. {t | Normal z * g t <= fi n t} INTER m_space m IN measurable_sets m`
	by METIS_TAC [IN_MEASURABLE_BOREL_ALL,m_space_def,space_def,
			subsets_def,measurable_sets_def,measure_space_def]
   ++ `!n. b n INTER m_space m IN measurable_sets m` by ( Q.UNABBREV_TAC `b` ++ METIS_TAC [])
    ++ `!n. z * (SIGMA (\i. x i * measure m (a i INTER (b n INTER m_space m))) s) <= ri n`
	by (STRIP_TAC
	    ++ `?s a x x'.
		((ri n) = pos_simple_fn_integral m s a x) /\
		pos_simple_fn m (fi n) s a x /\
		(pos_simple_fn_integral m s a x' = r') /\
		pos_simple_fn m g s a x'`
		by (`?s a x. pos_simple_fn m g s a x /\
		   (r' = pos_simple_fn_integral m s a x)`
		by METIS_TAC [IN_psfis]
	    	++ `?s a x. pos_simple_fn m (fi n) s a x /\
		   ((ri n) = pos_simple_fn_integral m s a x)`
		by METIS_TAC [IN_psfis]
	    	++ (MP_TAC o Q.ISPECL [`(m :
               ('a -> bool) #
               (('a -> bool) -> bool) # (('a -> bool) -> real))`,
				   `((fi :num -> 'a -> extreal) (n :num))`,
		`(s'' :num -> bool)`, `(a'' :num -> 'a -> bool)`,
		`(x'' :num -> real)`,
		`(g :'a -> extreal)`, `(s' :num -> bool)`, `(a' :num -> 'a -> bool)`,
             `(x' :num -> real)`]) pos_simple_fn_integral_present
	    	++ RW_TAC std_ss []
	    	++ Q.EXISTS_TAC `k` ++ Q.EXISTS_TAC `c` ++ Q.EXISTS_TAC `z'` ++ Q.EXISTS_TAC `z''`
	    	++ ASM_SIMP_TAC std_ss [pos_simple_fn_def] ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def])
   	    ++ RW_TAC std_ss []
	    ++ MATCH_MP_TAC REAL_LE_TRANS
	    ++ Q.EXISTS_TAC `z * (SIGMA (\i. x'' i * measure m (a' i INTER (b n INTER m_space m))) s')`
	    ++ CONJ_TAC
	    >> (MATCH_MP_TAC psfis_mono
		++ Q.EXISTS_TAC `m` ++ Q.EXISTS_TAC `(\t. Normal z * SIGMA (\i. Normal (x i) * indicator_fn (a i INTER (b n INTER m_space m)) t) s)`
		++ Q.EXISTS_TAC `(\t. Normal z * SIGMA (\i. Normal (x'' i) * indicator_fn (a' i INTER (b n INTER m_space m)) t) s')`
		++ ASM_REWRITE_TAC [] ++ CONJ_TAC
		>> (`z * SIGMA (\i. x i * measure m (a i INTER (b n INTER m_space m))) s =
		     SIGMA (\i. (\i. z * x i) i * measure m ((\i.(a i INTER (b n INTER m_space m))) i)) s`
			by FULL_SIMP_TAC std_ss [pos_simple_fn_def, GSYM REAL_SUM_IMAGE_CMUL, REAL_MUL_ASSOC]
		    ++ POP_ORW
		    ++ `!t. Normal z * SIGMA (\i. Normal (x i) * indicator_fn (a i INTER (b n INTER m_space m)) t) s =
			SIGMA (\i. Normal ((\i. (z * x i)) i) * indicator_fn ((\i.(a i INTER (b n INTER m_space m))) i) t) s`
			by (RW_TAC std_ss []
			    ++ `!i. (\i. Normal (x i) * indicator_fn (a i INTER (b n INTER m_space m)) t) i <> NegInf`
			          by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,num_not_infty]
			    ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def, GSYM EXTREAL_SUM_IMAGE_CMUL2, mul_assoc,GSYM extreal_mul_def])
		    ++ POP_ORW
		    ++ MATCH_MP_TAC psfis_intro
		    ++ FULL_SIMP_TAC real_ss [pos_simple_fn_def, REAL_LE_MUL, REAL_LT_IMP_LE]
		    ++ METIS_TAC [measure_space_def, sigma_algebra_def, subsets_def, space_def, ALGEBRA_INTER, pos_simple_fn_def])
		++ CONJ_TAC
	        >> (`z * SIGMA (\i. x'' i * measure m (a' i INTER (b n INTER m_space m))) s' =
		         SIGMA (\i. (\i. z * x'' i) i * measure m ((\i.(a' i INTER (b n INTER m_space m))) i)) s'`
			by FULL_SIMP_TAC std_ss [pos_simple_fn_def, GSYM REAL_SUM_IMAGE_CMUL, REAL_MUL_ASSOC]
		    ++ POP_ORW
		    ++ `!t. Normal z * SIGMA (\i. Normal (x'' i) * indicator_fn (a' i INTER (b n INTER m_space m)) t) s' =
			SIGMA (\i. Normal ((\i. z * x'' i) i) * indicator_fn ((\i.(a' i INTER (b n INTER m_space m))) i) t) s'`
			by (RW_TAC std_ss []
			   ++ `!i. (\i. Normal (x'' i) * indicator_fn (a' i INTER (b n INTER m_space m)) t) i <> NegInf`
			          by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,num_not_infty]
			   ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def, GSYM EXTREAL_SUM_IMAGE_CMUL2, mul_assoc,GSYM extreal_mul_def])
		    ++ POP_ORW
		    ++ MATCH_MP_TAC psfis_intro
		    ++ FULL_SIMP_TAC real_ss [pos_simple_fn_def, REAL_LE_MUL, REAL_LT_IMP_LE]
		    ++ METIS_TAC [measure_space_def, sigma_algebra_def, subsets_def, space_def, ALGEBRA_INTER, pos_simple_fn_def])
	        ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
	        ++ RW_TAC std_ss []
	        ++ `!i. Normal (x i) * indicator_fn (a i INTER (b n INTER m_space m)) x''' =
			(indicator_fn (b n) x''') * (\i. Normal (x i) * indicator_fn (a i) x''') i`
			by (RW_TAC std_ss [indicator_fn_def, IN_INTER,mul_lone,mul_lzero,mul_rzero,mul_rone] ++ METIS_TAC [])
		++ POP_ORW
		++ `!i. Normal (x'' i) * indicator_fn (a' i INTER (b n INTER m_space m)) x''' =
			(indicator_fn (b n) x''') * (\i. Normal (x'' i) * indicator_fn (a' i) x''') i`
			by (RW_TAC real_ss [indicator_fn_def, IN_INTER,mul_lone,mul_lzero,mul_rzero,mul_rone] ++ METIS_TAC [])
		++ POP_ORW
		++ Suff `SIGMA (\i. indicator_fn (b n) x''' * (\i. Normal (x i) * indicator_fn (a i) x''') i) s =
		         SIGMA (\i. indicator_fn (b n) x''' * (\i. Normal (x'' i) * indicator_fn (a' i) x''') i) s'`
	        >> RW_TAC std_ss [le_refl]
		++ `?z. indicator_fn (b n) x''' = Normal z` by RW_TAC std_ss [indicator_fn_def,extreal_of_num_def]
		++ POP_ORW
		++ `!x i:num a. (\i. Normal (x i) * indicator_fn (a i) x''') i <> NegInf` by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,num_not_infty]
		++ (MP_TAC o Q.SPECL [`s`,`(\i. Normal (x i) * indicator_fn (a i) x''')`,`z'`] o INST_TYPE [``:'a`` |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL2
		++ (MP_TAC o Q.SPECL [`s'`,`(\i. Normal (x'' i) * indicator_fn (a' i) x''')`,`z'`] o INST_TYPE [``:'a`` |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL2
		++ METIS_TAC [])
 	    ++ MATCH_MP_TAC psfis_mono
	    ++ Q.EXISTS_TAC `m` ++ Q.EXISTS_TAC `(\t. Normal z * SIGMA (\i. Normal (x'' i) * indicator_fn (a' i INTER (b n INTER m_space m)) t) s')`
	    ++ Q.EXISTS_TAC `fi n`
	    ++ ASM_REWRITE_TAC [] ++ CONJ_TAC
	    >> (`z * SIGMA (\i. x'' i * measure m (a' i INTER (b n INTER m_space m))) s' =
		SIGMA (\i. (\i. z * x'' i) i * measure m ((\i.(a' i INTER (b n INTER m_space m))) i)) s'`
			by FULL_SIMP_TAC std_ss [pos_simple_fn_def, GSYM REAL_SUM_IMAGE_CMUL, REAL_MUL_ASSOC]
		++ POP_ORW
		++ `!t. Normal z * SIGMA (\i. Normal (x'' i) * indicator_fn (a' i INTER (b n INTER m_space m)) t) s' =
			SIGMA (\i. Normal ((\i. (z * x'' i)) i) * indicator_fn ((\i.(a' i INTER (b n INTER m_space m))) i) t) s'`
		     by (RW_TAC std_ss []
			 ++ `!i. (\i. Normal (x'' i) * indicator_fn (a' i INTER (b n INTER m_space m)) t) i <> NegInf`
			          by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,num_not_infty]
			 ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def, GSYM EXTREAL_SUM_IMAGE_CMUL2, mul_assoc,GSYM extreal_mul_def])
	       ++ POP_ORW
	       ++ MATCH_MP_TAC psfis_intro
	       ++ FULL_SIMP_TAC real_ss [pos_simple_fn_def, REAL_LE_MUL, REAL_LT_IMP_LE]
	       ++ METIS_TAC [measure_space_def, sigma_algebra_def, subsets_def, space_def, ALGEBRA_INTER, pos_simple_fn_def])
	    ++ CONJ_TAC >> METIS_TAC []
	    ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
	    ++ RW_TAC std_ss []
	    ++ `!i. Normal (x'' i) * indicator_fn (a' i INTER (b n INTER m_space m)) x''' =
			(indicator_fn (b n) x''') * (\i. Normal (x'' i) * indicator_fn (a' i) x''') i`
			by (RW_TAC real_ss [indicator_fn_def, IN_INTER,mul_lone,mul_lzero,mul_rzero,mul_rone] ++ METIS_TAC [])
	    ++ POP_ORW
	    ++ `?z. indicator_fn (b n) x''' = Normal z` by RW_TAC std_ss [indicator_fn_def,extreal_of_num_def]
	    ++ `!i:num. (\i. Normal (x'' i) * indicator_fn (a' i) x''') i <> NegInf` by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,num_not_infty]
	    ++ (MP_TAC o Q.SPECL [`s'`,`(\i. Normal (x'' i) * indicator_fn (a' i) x''')`,`z'`] o INST_TYPE [``:'a`` |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL2
	    ++ Q.PAT_ASSUM `indicator_fn (b n) x''' = Normal z'` (MP_TAC o GSYM)
	    ++ RW_TAC std_ss [mul_assoc]
	    ++ Q.UNABBREV_TAC `b`
	    ++ FULL_SIMP_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,mul_lone,mul_lzero]
	    ++ RW_TAC std_ss [GSPECIFICATION,mul_rone,mul_rzero,mul_lone,mul_lzero]
	    ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
	    ++ RW_TAC std_ss [mul_rzero,mul_rone,le_refl]
	    ++ METIS_TAC [extreal_of_num_def,extreal_le_def])
   ++ MATCH_MP_TAC SEQ_LE
   ++ Q.EXISTS_TAC `(\n. (\n. z) n * (\n. SIGMA (\i. x i * measure m (a i INTER (b n INTER m_space m))) s) n)`
   ++ Q.EXISTS_TAC `ri`
   ++ REVERSE CONJ_TAC >> RW_TAC std_ss []
   ++ MATCH_MP_TAC SEQ_MUL
   ++ RW_TAC std_ss [SEQ_CONST]
   ++ `r' = pos_simple_fn_integral m s a x`
	by (MATCH_MP_TAC psfis_unique ++ Q.EXISTS_TAC `m` ++ Q.EXISTS_TAC `g`
	    ++ RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
	    ++ Q.EXISTS_TAC `(s,a,x)`
	    ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)` ++ RW_TAC std_ss [PAIR_EQ])
   ++ POP_ORW
   ++ RW_TAC std_ss [pos_simple_fn_integral_def]
   ++ `(\n. SIGMA (\i. x i * measure m (a i INTER (b n INTER m_space m))) s) =
       (\n. SIGMA ((\n. (\i. x i * measure m (a i INTER (b n INTER m_space m)))) n) s)`
	by RW_TAC std_ss []
   ++ POP_ORW
   ++ `FINITE s` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
   ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool`) SEQ_REAL_SUM_IMAGE
   ++ RW_TAC std_ss []
   ++ `(\n. x x' * measure m (a x' INTER (b n INTER m_space m))) =
       (\n. (\n. x x') n * (\n. measure m (a x' INTER (b n INTER m_space m))) n)`
	by RW_TAC std_ss []
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_MUL
   ++ RW_TAC std_ss [SEQ_CONST]
   ++ `(\n. measure m (a x' INTER (b n INTER m_space m))) =
	(measure m) o (\n. a x' INTER (b n INTER m_space m))`
	by RW_TAC std_ss [o_DEF]
   ++ POP_ORW
   ++ MATCH_MP_TAC MONOTONE_CONVERGENCE
   ++ RW_TAC std_ss [IN_FUNSET, SUBSET_DEF, IN_INTER]
   << [METIS_TAC [measure_space_def, sigma_algebra_def, pos_simple_fn_def, ALGEBRA_INTER, subsets_def, space_def],
       Q.UNABBREV_TAC `b` ++ FULL_SIMP_TAC std_ss [GSPECIFICATION, ext_mono_increasing_def]
       ++ METIS_TAC [le_trans, DECIDE ``!n:num. n <= SUC n``,add_lzero],
       `!i. BIGUNION (IMAGE (\n. a i INTER (b n INTER m_space m)) UNIV) = a i INTER m_space m`
           by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_INTER,IN_UNIV]
               ++ EQ_TAC >> METIS_TAC []
	       ++ RW_TAC std_ss []
	       ++ Q.UNABBREV_TAC `b`
	       ++ RW_TAC real_ss [GSPECIFICATION]
	       ++ `f x'' = sup (IMAGE (\i. fi i x'') UNIV)` by FULL_SIMP_TAC std_ss []
	       ++ Cases_on `g x'' = 0` >> METIS_TAC [mul_rzero,extreal_of_num_def]
               ++ `Normal z * g x'' < f x''`
                   by (Cases_on `g x'' = f x''`
                       >> (`0 < f x''` by METIS_TAC [le_lt,pos_simple_fn_def]
                           ++ METIS_TAC [lt_rmul,mul_lone,IN_psfis_eq,pos_simple_fn_not_infty,extreal_lt_eq,extreal_of_num_def])
		       ++ `g x'' < f x''` by METIS_TAC [le_lt]
		       ++ `Normal z < Normal 1` by METIS_TAC [extreal_lt_eq]
		       ++ `0 <= Normal z /\ 0 <= Normal 1` by METIS_TAC [extreal_of_num_def,extreal_le_def,REAL_LE_01,REAL_LT_IMP_LE]
		       ++ METIS_TAC [lt_mul2,mul_lone,extreal_not_infty,pos_simple_fn_not_infty,extreal_lt_eq,extreal_of_num_def,extreal_le_def,psfis_pos])
	       ++ Suff `?n. Normal z * g x'' <= (\n. fi n x'') n` >> RW_TAC std_ss []
               ++ MATCH_MP_TAC sup_le_mono
	       ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [ext_mono_increasing_def,ext_mono_increasing_suc]
	       ++ METIS_TAC [])
       ++ `!i. i IN s==> (a i INTER m_space m = a i)`
            by METIS_TAC [pos_simple_fn_def,SUBSET_INTER1,MEASURE_SPACE_SUBSET_MSPACE]
       ++ METIS_TAC []]);

val pos_fn_integral_eq_mono_conv_limit_borel = store_thm
  ("pos_fn_integral_eq_mono_conv_limit_borel",
   ``!m f fi ri r.
	measure_space m /\
	(!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = f x)) /\
	(!i. ri i IN psfis m (fi i)) /\ ri --> r /\
	(!i x. x IN m_space m ==> (fi i) x <= f x)
	==>
	(pos_fn_integral m f = r)``,
   REPEAT STRIP_TAC
   ++ `f IN measurable (m_space m,measurable_sets m) Borel`
         by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
	     ++ Q.EXISTS_TAC `fi`
	     ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_suc]
	     ++ RW_TAC std_ss [space_def]
	     >> FULL_SIMP_TAC std_ss [measure_space_def]
	     ++ METIS_TAC [IN_MEASURABLE_BOREL_POS_SIMPLE_FN,IN_psfis_eq])
   ++ (MP_TAC o Q.ISPECL [`(m :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`,
			  `(f :'a -> extreal)`, `(fi :num -> 'a -> extreal)`,
			  `ri: num->real`, `r:real`]) psfis_mono_conv_mono_borel
   ++ RW_TAC std_ss []
   ++ Cases_on `?g. r IN psfis m g /\ (!x. x IN m_space m ==> g x <= f x)`
   >> (RW_TAC std_ss [pos_fn_integral_def]
       ++ MATCH_MP_TAC REAL_SUP_MAX
       ++ `!x. {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f x} x =
		x IN {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==>  g x <= f x}` by RW_TAC std_ss [SPECIFICATION]
       ++ POP_ORW
       ++ RW_TAC std_ss [GSPECIFICATION] ++ Q.EXISTS_TAC `g` ++ RW_TAC std_ss [])
   ++ FULL_SIMP_TAC std_ss []
   ++ `!g r'. r' IN psfis m g /\ (!x. x IN m_space m ==> g x <= f x) ==> r' < r`
	by METIS_TAC [REAL_LE_LT]
   ++ RW_TAC std_ss [pos_fn_integral_def, sup]
   ++ MATCH_MP_TAC SELECT_UNIQUE
   ++ RW_TAC std_ss []
   ++ `!y' x. {r | ?g. r IN psfis m g /\ !x. x IN m_space m==> g x <= f x} x =
		x IN {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f x}` by RW_TAC std_ss [SPECIFICATION]
   ++ POP_ORW ++ RW_TAC std_ss [GSPECIFICATION]
   ++ EQ_TAC
   >> (RW_TAC std_ss []
       ++ `~ (r < y)`
		by METIS_TAC [REAL_NOT_LT]
       ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
       ++ `r <= y`
		by (MATCH_MP_TAC REAL_LE_EPSILON
		    ++ RW_TAC std_ss []
		    ++ `?N. !n. n >= N ==>r < ri N + e` by METIS_TAC [SEQ, GSYM ABS_BETWEEN, REAL_LT_SUB_RADD]
		    ++ Cases_on `!n:num. n > N ==> ((ri:num->real) n = ri N)`
		    >> (`ri --> (ri:num->real) (N:num)`
			by (RW_TAC std_ss [SEQ] ++ Q.EXISTS_TAC `N`
			    ++ RW_TAC real_ss [DECIDE ``!(n:num)(m:num). n>=m = ((n = m) \/ (n > m))``]
			    ++ RW_TAC real_ss [])
			++ `r = ri N` by METIS_TAC [SEQ_UNIQ]
			++ METIS_TAC [])
		    ++ FULL_SIMP_TAC std_ss []
		    ++ `mono_increasing ri`
			by (FULL_SIMP_TAC std_ss [mono_increasing_def,ext_mono_increasing_def]
			    ++ REPEAT STRIP_TAC ++ MATCH_MP_TAC psfis_mono
			    ++ METIS_TAC [])
		    ++ FULL_SIMP_TAC std_ss [DECIDE ``!(n:num) m. n > m = m < n``]
		    ++ `(ri:num->real) N < ri n`
			by METIS_TAC [mono_increasing_def, LESS_OR_EQ, REAL_LE_LT]
		    ++ Suff `ri N + e <= y + e` >> METIS_TAC [REAL_LE_TRANS, REAL_LT_IMP_LE, LESS_EQ_REFL, GREATER_EQ]
		    ++ RW_TAC std_ss [REAL_LE_RADD]
		    ++ Suff `ri N < y` >> RW_TAC std_ss [REAL_LT_IMP_LE]
		    ++ Q.PAT_ASSUM `!y':real. P = y' < y` (MP_TAC o GSYM)
		    ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `ri n` ++ METIS_TAC [])
       ++ METIS_TAC [REAL_LE_LT])
   ++ RW_TAC std_ss []
   ++ EQ_TAC
   >> METIS_TAC [REAL_LT_TRANS]
   ++ RW_TAC std_ss []
   ++ `?e. 0 < e /\ y' + e <= r`
	by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
	    ++ FULL_SIMP_TAC std_ss [REAL_NOT_LE]
	    ++ `r <= y'` by METIS_TAC [REAL_LE_EPSILON, REAL_LT_IMP_LE]
   ++ METIS_TAC [REAL_NOT_LT])
   ++ `?N. r - e < ri N` by METIS_TAC [SEQ, GSYM ABS_BETWEEN, GREATER_EQ, LESS_EQ_REFL]
   ++ Q.EXISTS_TAC `(ri:num->real) N` ++ CONJ_TAC >> METIS_TAC []
   ++ FULL_SIMP_TAC std_ss [GSYM REAL_LE_SUB_LADD] ++ METIS_TAC [REAL_LET_TRANS]);


(**********************************************************)
(*  Existence of Convergent sequence                      *)
(**********************************************************)


(**** Define the sequence ****)
val fn_seq_def = Define `fn_seq m f = (\n.
         (\x. SIGMA (\k. (&k / (2 pow n)) * indicator_fn {x | x IN m_space m /\ (&k / (2 pow n) <= f x) /\ (f x < (&k + 1) /(2 pow n))} x) (count (4 ** n)) +
              2 pow (n) * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} x))`;

(**** Define their integrals ****)
val fn_seq_integral_def = Define `fn_seq_integral m f = (\n. SIGMA (\k. (&k / (2 pow n)) * measure m {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n}) (count (4 ** n)) + (2 pow n) * measure m {x | x IN m_space m /\ 2 pow n <= f x} )`;



(******************************************************)
(****   f_n(x) = &k / 2 pow n in the k^th interval ****)
(******************************************************)

val lemma_fn_1 = store_thm
  ("lemma_fn_1",``!m f n x k. x IN m_space m /\
			  k IN count (4 ** n) /\
			  &k / 2 pow n <= f x /\
			  f x < (&k + 1) / 2 pow n ==>
			  (fn_seq m f n x = &k / 2 pow n)``,
  RW_TAC std_ss []
  ++ `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ FULL_SIMP_TAC real_ss [fn_seq_def,indicator_fn_def,GSPECIFICATION,IN_COUNT,mul_rone,mul_rzero,extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def]
  ++ `f x <> PosInf` by METIS_TAC [lt_infty,lt_trans]
  ++ `f x <> NegInf` by METIS_TAC [lt_infty,lte_trans]
  ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
  ++ FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
  ++ `(\k'. Normal (&k' / 2 pow n) * if &k' / 2 pow n <= r /\ r < &(k' + 1) / 2 pow n then Normal 1 else Normal 0) =
      (\k'. Normal((&k' / 2 pow n) * if &k' / 2 pow n <= r /\ r < &(k' + 1) / 2 pow n then 1 else 0))`
         by (RW_TAC std_ss [FUN_EQ_THM] ++ METIS_TAC [extreal_add_def,extreal_mul_def])
  ++ POP_ORW
  ++ `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_NORMAL,extreal_11,extreal_mul_def,extreal_add_def]
  >> (`k + 1 <= 4 ** n` by RW_TAC real_ss [LESS_EQ]
      ++ `&(k + 1) <= (4:real) pow n` by RW_TAC real_ss [REAL_OF_NUM_POW]
      ++ FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ]
      ++ `r * 2 pow n < 4 pow n` by METIS_TAC [REAL_LTE_TRANS]
      ++ METIS_TAC [REAL_LT_RDIV_EQ,REAL_POW_DIV,EVAL ``4/2:real``,real_lte])
  ++ FULL_SIMP_TAC real_ss [GSYM real_lt]
  ++ (MP_TAC o UNDISCH o Q.SPECL [`k`,`count (4 ** n)`] o CONJUNCT2 o Q.SPEC `(\k'. &k' / 2 pow n *
           if &k' / 2 pow n <= r:real /\ r < &(k' + 1) / 2 pow n then 1 else 0)`) (INST_TYPE [alpha |-> ``:num``] REAL_SUM_IMAGE_THM)
  ++ RW_TAC real_ss []
  ++ `count (4 ** n) = k INSERT (count (4 ** n))` by RW_TAC std_ss [GSYM ABSORPTION,IN_COUNT]
  ++ POP_ORW
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
  ++ Suff `SIGMA (\k'. &k' / 2 pow n * if &k' / 2 pow n <= r /\ r < &(k' + 1) / 2 pow n then 1 else 0)
                 (count (4 ** n) DELETE k) = 0:real`
  >> RW_TAC real_ss []
  ++ `FINITE (count (4 ** n) DELETE k)` by RW_TAC std_ss [FINITE_COUNT,FINITE_DELETE]
  ++ ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `count (4 ** n) DELETE k` o INST_TYPE [alpha |-> ``:num``]) REAL_SUM_IMAGE_IN_IF]
  ++ Suff `(\x. if x IN count (4 ** n) DELETE k then (\k'. &k' / 2 pow n *
              if &k' / 2 pow n <= r:real /\ r < &(k' + 1) / 2 pow n then
                1 else 0) x else 0) = (\x:num. 0:real)`
  >> FULL_SIMP_TAC real_ss [REAL_SUM_IMAGE_0]
  ++ RW_TAC real_ss [FUN_EQ_THM,IN_COUNT,IN_DELETE]
  ++ RW_TAC real_ss [COND_EXPAND]
  ++ Cases_on `&x'<=((&k):real)`
  >> (`&(x'+1)<=(&k):real` by FULL_SIMP_TAC real_ss [LESS_EQ,REAL_LE_LT]
      ++ `r * 2 pow n < &(x' + 1)` by METIS_TAC [REAL_LT_RDIV_EQ]
      ++ `r:real * 2 pow n < &k` by METIS_TAC [REAL_LTE_TRANS]
      ++ METIS_TAC [REAL_LT_RDIV_EQ,real_lte])
  ++ FULL_SIMP_TAC std_ss [GSYM real_lt]
  ++ `&(k+1)<=(&x'):real` by FULL_SIMP_TAC real_ss [LESS_EQ,REAL_LE_LT]
  ++ `&x' <= r * 2 pow n` by METIS_TAC [REAL_LE_LDIV_EQ]
  ++ `&(k+1) <= r * 2 pow n` by METIS_TAC [REAL_LE_TRANS]
  ++ METIS_TAC [REAL_LE_LDIV_EQ,real_lte]);


(**********************************************)
(****   f_n(x) = 2 pow n if 2 pow n <= f x ****)
(**********************************************)

val lemma_fn_2 = store_thm
  ("lemma_fn_2",``!m f n x. x IN m_space m /\ 2 pow n <= f x ==> (fn_seq m f n x = 2 pow n)``,
  RW_TAC real_ss [fn_seq_def,indicator_fn_def,GSPECIFICATION,mul_rone]
  ++ `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  ++ `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ Suff `SIGMA (\k. &k / 2 pow n *  if &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n then 1 else 0) (count (4 ** n)) = 0`
  >> RW_TAC real_ss [add_lzero]
  ++ (MP_TAC o Q.SPEC `(\k. &k / 2 pow n * if &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n then 1 else 0)` o UNDISCH o Q.SPEC `count (4 ** n)` o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x'. (\k. &k / 2 pow n * if &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n then 1 else 0) x' <> NegInf`
      by (RW_TAC std_ss [mul_rone,mul_rzero]
          ++ RW_TAC std_ss [extreal_of_num_def,extreal_pow_def,extreal_mul_def,extreal_div_eq,extreal_not_infty])
  ++ Suff `(\x'. if x' IN count (4 ** n) then &x' / 2 pow n * if &x' / 2 pow n <= f x /\ f x < (&x' + 1) / 2 pow n then 1 else 0 else 0) = (\x. 0)`
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
  ++ RW_TAC real_ss [FUN_EQ_THM,IN_COUNT]
  ++ RW_TAC real_ss [COND_EXPAND,mul_rzero,mul_rone]
  ++ `&(x' + 1):real <= 4 pow n` by RW_TAC real_ss [LESS_EQ,REAL_OF_NUM_POW]
  ++ `&(x' + 1):real / 2 pow n <= 4 pow n / 2 pow n` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
  ++ `(&x' + 1) / 2 pow n <= 4 pow n / 2 pow n` by RW_TAC real_ss [extreal_div_eq,extreal_pow_def,extreal_add_def,extreal_of_num_def,extreal_le_def]
  ++ `f x < 4 pow n / 2 pow n` by METIS_TAC [lte_trans]
  ++ `4 pow n / 2 pow n = 2 pow n` by RW_TAC std_ss [extreal_pow_def,extreal_div_eq,extreal_of_num_def,GSYM REAL_POW_DIV,EVAL ``4/2:real``]
  ++ METIS_TAC [extreal_lt_def]);

(************************************************************************)
(*** f(x) is either larger than 2 pow n or is inside some k interval ****)
(************************************************************************)

val lemma_fn_3 = store_thm
  ("lemma_fn_3",``!m f n x. x IN m_space m /\ 0 <= f x ==> (2 pow n <= f x) \/ (?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n)``,
  RW_TAC real_ss [IN_COUNT]
  ++ Cases_on `2 pow n <= f x`
  >> RW_TAC std_ss []
  ++ `f x < 2 pow n` by FULL_SIMP_TAC std_ss [extreal_lt_def]
  ++ `f x <> PosInf` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty,lt_infty,lt_trans]
  ++ `f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,extreal_of_num_def,extreal_not_infty]
  ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
  ++ `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ FULL_SIMP_TAC real_ss [extreal_of_num_def,extreal_pow_def,extreal_le_def,extreal_lt_eq,extreal_div_eq,extreal_add_def]
  ++ Q.EXISTS_TAC `flr (2 pow n * r)`
  ++ CONJ_TAC
  >> (`2 pow n * r < 2 pow n * 2 pow n` by RW_TAC real_ss [REAL_LT_LMUL]
    ++ `2 pow n * 2 pow n = 4:real pow n` by RW_TAC real_ss [GSYM POW_MUL]
    ++ `0 <= 2 pow n * r` by RW_TAC real_ss [REAL_LT_LE_MUL]
    ++ `&(4 ** n) = 4:real pow n` by RW_TAC real_ss [GSYM REAL_OF_NUM_POW]
    ++ FULL_SIMP_TAC real_ss []
    ++ `&flr (2 pow n * r) <= 2 pow n * r` by RW_TAC real_ss [NUM_FLOOR_LE]
    ++ `&flr (2 pow n * r) < 4:real pow n` by METIS_TAC [REAL_LET_TRANS]
    ++ METIS_TAC [REAL_LT])
  ++ CONJ_TAC
  >> (`0 <= 2 pow n * r` by RW_TAC real_ss [REAL_LT_LE_MUL]
     ++ `&flr (2 pow n * r) <= 2 pow n * r` by RW_TAC real_ss [NUM_FLOOR_LE]
     ++ `&flr (2 pow n * r) / 2 pow n <= 2 pow n * r / 2 pow n`
        by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
     ++ METIS_TAC [REAL_EQ_LDIV_EQ,REAL_MUL_COMM])
  ++ `0 <= 2 pow n * r` by RW_TAC real_ss [REAL_LT_LE_MUL]
  ++ `2 pow n * r < &(flr (2 pow n * r) + 1)` by METIS_TAC [NUM_FLOOR_DIV_LOWERBOUND,REAL_LT_01,REAL_OVER1,REAL_MUL_RID]
  ++ `2 pow n * r / 2 pow n < &(flr (2 pow n * r) + 1) / 2 pow n`
      by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
  ++ METIS_TAC [REAL_EQ_LDIV_EQ,REAL_MUL_COMM]);


(*********************************)
(*   fn_(x) = 0 outside m_space  *)
(*********************************)

val lemma_fn_4 = store_thm
("lemma_fn_4",``!m f n x. ~(x IN m_space m) ==> (fn_seq m f n x = 0)``,
  RW_TAC real_ss [fn_seq_def,indicator_fn_def,GSPECIFICATION,mul_rzero,add_rzero]
  ++ METIS_TAC [FINITE_COUNT,EXTREAL_SUM_IMAGE_ZERO]);


(*********************************)
(*       fn_(x) positive         *)
(*********************************)

val lemma_fn_5 = store_thm
  ("lemma_fn_5",``!m f n x. 0 <= f x ==> (0 <= fn_seq m f n x)``,
  RW_TAC real_ss []
  ++ `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ `0 < 2 pow n` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_lt_eq]
  ++ Cases_on `~(x IN m_space m)`
  >> RW_TAC std_ss [lemma_fn_4,le_refl]
  ++ FULL_SIMP_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`n`,`x`]) lemma_fn_3
  ++ RW_TAC real_ss []
  >> RW_TAC real_ss [lt_imp_le,lemma_fn_2]
  ++ `fn_seq m f n x = &k / 2 pow n` by RW_TAC real_ss [lemma_fn_1]
  ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_le_def]
  ++ MATCH_MP_TAC REAL_LE_DIV
  ++ RW_TAC real_ss [REAL_POW_LT,REAL_LT_IMP_LE]);

(**************************************)
(*     integral of f_n is positive    *)
(**************************************)
val lemma_fn_6 = store_thm
  ("lemma_fn_6",``!m f n. (!x. x IN m_space m ==> 0 <= f x) /\ measure_space m /\
			f IN measurable (m_space m,measurable_sets m) Borel
			==> (0 <= fn_seq_integral m f n)``,
  RW_TAC real_ss [fn_seq_integral_def]
  ++ MATCH_MP_TAC REAL_LE_ADD
  ++ REVERSE STRIP_TAC
  >> (MATCH_MP_TAC REAL_LE_MUL
      ++ RW_TAC real_ss [POW_POS]
      ++ `{x | x IN m_space m /\ 2 pow n <= f x} = {x | 2 pow n <= f x} INTER m_space m`
           by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM]
      ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE,MEASURE_SPACE_POSITIVE,positive_def])
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
  ++ RW_TAC std_ss [FINITE_COUNT]
  ++ MATCH_MP_TAC REAL_LE_MUL
  ++ RW_TAC real_ss [REAL_LE_DIV,POW_POS]
  ++ `{x' | x' IN m_space m /\ &x / 2 pow n <= f x' /\ f x' < (&x + 1) / 2 pow n} =
      {x' | &x / 2 pow n <= f x' /\ f x' < (&x + 1) / 2 pow n} INTER m_space m`
      by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM]
  ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE,MEASURE_SPACE_POSITIVE,positive_def]);


(*******************************************************************************)
(*                        MONOTONICALLY INCREASING                             *)
(*******************************************************************************)

val lemma_fn_mono_increasing = store_thm
("lemma_fn_mono_increasing",``!m f x. 0 <= f x ==> mono_increasing (\n. fn_seq m f n x)``,
  RW_TAC std_ss [ext_mono_increasing_suc,ADD1]
  ++ Cases_on `~(x IN m_space m)`
  >> RW_TAC real_ss [lemma_fn_4,le_refl]
  ++ FULL_SIMP_TAC std_ss []
  ++ `!n x k. x IN m_space m /\ (k IN count (4 ** n)) /\ (&k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n) ==> (fn_seq m f n x = &k / 2 pow n)`
      by RW_TAC std_ss [lemma_fn_1]
  ++ `!n x. x IN m_space m /\ 2 pow n <= f x ==> (fn_seq m f n x = 2 pow n)`
       by RW_TAC std_ss [lemma_fn_2]
  ++ `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ `!n k. (k IN count (4 ** (n + 1))) /\ (&k / 2 pow (n + 1) <= f x /\ f x < (&k + 1) / 2 pow (n + 1)) ==> (fn_seq m f n x <= fn_seq m f (n + 1) x)`
       by (RW_TAC real_ss []
   	   ++ `fn_seq m f (n + 1) x = &k / (2 pow (n + 1))` by RW_TAC real_ss []
           ++ `f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,extreal_of_num_def,extreal_not_infty]
           ++ `f x <> PosInf` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty,lt_infty,lt_trans]
           ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases]
	   ++ `0:real <> 2 pow (n + 1)` by RW_TAC real_ss []
           ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def,extreal_mul_def,extreal_le_def,extreal_lt_eq]
	   ++ `&(k + 1) / (2 pow (n + 1)):real = (&(k + 1) / 2) / (2 pow (n + 1) / 2)` by RW_TAC real_ss [REAL_DIV_DENOM_CANCEL]
	   ++ `2 pow (n + 1) / 2 = (2 pow n):real` by (RW_TAC std_ss [GSYM ADD1,pow] ++ RW_TAC real_ss [REAL_EQ_LDIV_EQ,REAL_MUL_COMM])
	   ++ `&k / 2 pow (n + 1) = (&k / 2) / (2 pow (n + 1) / 2):real` by RW_TAC real_ss [REAL_DIV_DENOM_CANCEL]
	   ++ FULL_SIMP_TAC std_ss []
	   ++ STRUCT_CASES_TAC (Q.SPEC `k` EVEN_OR_ODD)
	   >> (FULL_SIMP_TAC std_ss [EVEN_EXISTS]
               ++ FULL_SIMP_TAC real_ss []
	       ++ `&k / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ]
	       ++ `&(2 * m' + 1):real < &(2 * m' + 2)` by RW_TAC real_ss []
	       ++ `&(2 * m' + 1) / 2:real < &(2 * m' + 2) / 2` by RW_TAC real_ss [REAL_LT_RDIV]
	       ++ `&(2 * m' + 1) / 2 / (2 pow n):real < &(2 * m' + 2) / 2 / 2 pow n` by RW_TAC real_ss [REAL_LT_RDIV]
	       ++ `&(2 * m' + 2) / 2 = &(m'+1):real` by RW_TAC real_ss [REAL_EQ_LDIV_EQ,REAL_ADD_LDISTRIB]
	       ++ `r < &(m' + 1) / 2 pow n` by METIS_TAC [REAL_LT_TRANS]
               ++ `&(2 * m') / 2 / 2 pow n = &m' / (2 pow n):real` by METIS_TAC []
	       ++ FULL_SIMP_TAC real_ss []
	       ++ Cases_on `m' IN count (4 ** n)`
	       >> (`fn_seq m f n x = Normal (&m' / 2 pow n)` by METIS_TAC [extreal_le_def,extreal_lt_eq]
		   ++ RW_TAC std_ss [le_refl])
	       ++ FULL_SIMP_TAC real_ss [IN_COUNT,NOT_LESS]
	       ++ `4:real pow n <= &m'` by RW_TAC real_ss [REAL_OF_NUM_POW]
	       ++ `4:real pow n / 2 pow n <= &m' / 2 pow n` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
	       ++ `2 pow n <= r` by METIS_TAC [REAL_LE_TRANS,REAL_POW_DIV,EVAL ``4/2:real``]
	       ++ `fn_seq m f n x = Normal (2 pow n)` by METIS_TAC [extreal_le_def,extreal_lt_eq]
	       ++ `(2 pow n):real <= &m' / 2 pow n` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
	       ++ `&(2*m')/2 = &m':real` by RW_TAC real_ss []
	       ++ RW_TAC std_ss [extreal_le_def])
	   ++ FULL_SIMP_TAC std_ss [ODD_EXISTS]
	   ++ `(k - 1) < k` by RW_TAC real_ss []
	   ++ `&(k - 1) / 2 < (&k) / 2:real` by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_DIV_RMUL]
	   ++ `&(k - 1) / 2 / 2 pow n < (&k) / 2 / (2 pow n):real` by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_DIV_RMUL,REAL_POS_NZ]
	   ++ `&(k - 1) / 2 / 2 pow n <= r` by METIS_TAC [REAL_LTE_TRANS,REAL_LT_IMP_LE]
	   ++ `&(k - 1):real = 2 * &m'` by RW_TAC real_ss []
	   ++ `!x. 2 * x / 2 = x:real` by RW_TAC real_ss [REAL_EQ_LDIV_EQ,REAL_MUL_COMM]
           ++ `&m' / (2 pow n) <= r` by METIS_TAC [REAL_MUL]
 	   ++ `&(k + 1):real = 2 * (&m' + 1)` by RW_TAC real_ss []
           ++ FULL_SIMP_TAC real_ss []
	   ++ `r < &(m' + 1) / (2 pow n)` by METIS_TAC [REAL_MUL,REAL_ADD]
    	   ++ Cases_on `m' IN count (4 ** n)`
	   >> (Q.PAT_ASSUM `!n x k. Q` (MP_TAC o Q.SPECL [`n`,`x`, `m'`])
               ++ RW_TAC std_ss [extreal_le_def,extreal_lt_eq]
	       ++ `&(2 * m'):real <= &SUC (2*m')` by RW_TAC real_ss []
	       ++ `&(2 * m') / 2:real <= &SUC (2 * m') / 2` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL]
	       ++ `&(2 * m') / 2 / 2 pow n <= &SUC (2 * m') / 2 / (2 pow n):real` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL,REAL_POS_NZ]
	       ++ `&(2 * m') / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ]
	       ++ FULL_SIMP_TAC real_ss [REAL_LE_TRANS])
	   ++ FULL_SIMP_TAC real_ss [IN_COUNT,NOT_LESS]
	   ++ `4 pow n <= &m':real` by RW_TAC real_ss [REAL_OF_NUM_POW]
	   ++ `4:real pow n / 2 pow n <= &m' / 2 pow n` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
	   ++ `&(k - 1):real = 2 * &m'` by RW_TAC real_ss []
	   ++ `&m' < &k / 2:real` by METIS_TAC []
	   ++ `&m' / (2 pow n):real  < &k / 2 / 2 pow n` by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
	   ++ `2 pow n <= r` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``,REAL_LET_TRANS,REAL_LTE_TRANS,REAL_LT_IMP_LE]
	   ++ `fn_seq m f n x = Normal (2 pow n)` by METIS_TAC [extreal_le_def,extreal_lt_eq]
	   ++ `2 pow n <= &m' / (2 pow n):real` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
	   ++ `&(2 * m'):real <= &SUC (2 * m')` by RW_TAC real_ss []
	   ++ `&(2 * m') / 2:real <= &SUC (2 * m') / 2` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL]
	   ++ `&(2 * m') / 2 / 2 pow n <= &SUC (2 * m') / 2 / (2 pow n):real` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL,REAL_POS_NZ]
	   ++ `&(2 * m') / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ]
	   ++ METIS_TAC [REAL_LE_TRANS,extreal_le_def])
   ++ `!n. 2 pow (n + 1) <= f x ==> (fn_seq m f n x <= fn_seq m f (n + 1) x)`
        by (RW_TAC real_ss []
	    ++ `2:real pow n < 2 pow (n + 1)` by RW_TAC real_ss [REAL_POW_MONO_LT]
	    ++ `2 pow n < 2 pow (n + 1)` by METIS_TAC [extreal_pow_def,extreal_of_num_def,extreal_lt_eq]
            ++ METIS_TAC [extreal_le_def,extreal_lt_eq,lte_trans,lt_imp_le])
   ++ (MP_TAC o Q.SPECL [`m`,`f`,`n + 1`,`x`]) lemma_fn_3
   ++ RW_TAC std_ss []
   >> RW_TAC std_ss []
   ++ METIS_TAC []);


(*******************************************************************************)
(*                            UPPER BOUNDED BY f                               *)
(*******************************************************************************)

val lemma_fn_upper_bounded = store_thm
("lemma_fn_upper_bounded",``!m f n x. 0 <= f x ==> (fn_seq m f n x <= f x)``,
  RW_TAC std_ss []
  ++ Cases_on `~(x IN m_space m)` >> RW_TAC real_ss [lemma_fn_4]
  ++ FULL_SIMP_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`n`,`x`]) lemma_fn_3
  ++ RW_TAC real_ss []
  >> METIS_TAC [lemma_fn_2,le_refl]
  ++ `fn_seq m f n x =  &k / 2 pow n` by RW_TAC real_ss [lemma_fn_1]
  ++ RW_TAC std_ss []);

(*******************************************************************************)
(*                            f Supremum of fn_seq                             *)
(*******************************************************************************)

val lemma_fn_sup = store_thm
  ("lemma_fn_sup",``!m f x. x IN m_space m /\ 0 <= f x ==> (sup (IMAGE (\n. fn_seq m f n x) UNIV) = f x)``,
  RW_TAC std_ss []
  ++ Cases_on `f x = PosInf`
  >> (`!n:num. fn_seq m f n x = 2 pow n` by METIS_TAC [le_infty,lemma_fn_2]
      ++ RW_TAC std_ss [sup_eq,le_infty]
      ++ `!n. 2 pow n <= y`
            by (RW_TAC std_ss []
		++ POP_ASSUM MATCH_MP_TAC
                ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	        ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	        ++ METIS_TAC [])
      ++ SPOSE_NOT_THEN ASSUME_TAC
      ++ METIS_TAC [EXTREAL_ARCH_POW,extreal_lt_def])
  ++ `!n.  fn_seq m f n x <= f x` by METIS_TAC [lemma_fn_upper_bounded]
  ++ `?r. f x = Normal r` by METIS_TAC [extreal_cases,lt_infty,lte_trans,extreal_of_num_def]
  ++ `!n. fn_seq m f n x <> PosInf` by METIS_TAC [lt_infty,let_trans]
  ++ `!n. fn_seq m f n x <> NegInf` by METIS_TAC [lt_infty,lte_trans,lemma_fn_5,extreal_of_num_def]
  ++ `?r. !n. fn_seq m f n x = Normal (r n)`
         by (Q.EXISTS_TAC `\n. @r. fn_seq m f n x = Normal r`
	     ++ RW_TAC std_ss []
             ++ SELECT_ELIM_TAC
   	     ++ RW_TAC std_ss []
	     ++ METIS_TAC [extreal_cases])
  ++ `?N. f x < 2 pow N` by RW_TAC std_ss [EXTREAL_ARCH_POW]
  ++ `!p n. p <= n ==> 2 pow p <= 2 pow n` by METIS_TAC [pow_le_mono,EVAL ``1<=2``]
  ++ `!n. N <= n ==> f x < 2 pow n` by METIS_TAC [lte_trans]
  ++ `!n. N <= n ==> ?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC [lemma_fn_3,extreal_lt_def]
  ++ `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ `!n k. &k / 2 pow n = Normal (&k / 2 pow n)` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_div_eq]
  ++ `!n z. Normal z / 2 pow n = Normal (z / 2 pow n)` by METIS_TAC [extreal_pow_def,extreal_div_eq,extreal_of_num_def]
  ++ `!n. N <= n ==> (f x - 1 / 2 pow n < fn_seq m f n x)`
        by (RW_TAC real_ss []
	    ++ `?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC []
	    ++ `fn_seq m f n x = &k / 2 pow n` by METIS_TAC [lemma_fn_1]
            ++ `Normal (&k + 1) / Normal (2 pow n) = Normal ((&k + 1) / (2 pow n))` by METIS_TAC [extreal_div_eq]
            ++ `Normal r < Normal ((&k + 1) /  (2 pow n))` by METIS_TAC [extreal_pow_def,extreal_of_num_def,extreal_add_def]
            ++ FULL_SIMP_TAC std_ss [extreal_lt_eq,GSYM REAL_DIV_ADD,extreal_pow_def,extreal_sub_def,extreal_of_num_def,extreal_div_eq,extreal_lt_eq,REAL_LT_SUB_RADD]
	    ++ `r' n = &k / 2 pow n` by METIS_TAC [extreal_div_eq,extreal_11]
            ++ FULL_SIMP_TAC std_ss [])
  ++ `!n. N <= n ==> (r - 1 / 2 pow n < r' n)`
        by (FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq,extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def]
            ++ RW_TAC std_ss []
	    ++ METIS_TAC [extreal_sub_def,extreal_lt_eq])
  ++ `mono_increasing (\n. fn_seq m f n x)` by METIS_TAC [lemma_fn_mono_increasing]
  ++ `mono_increasing r'` by (FULL_SIMP_TAC std_ss [ext_mono_increasing_def,mono_increasing_def] ++ METIS_TAC [extreal_le_def])
  ++ FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq,extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def,extreal_sub_def,extreal_not_infty]
  ++ RW_TAC std_ss [GSYM sup_seq,SEQ,GREATER_EQ]
  ++ `!n. 1:real / 2 pow n = (1 / 2) pow n` by RW_TAC real_ss [POW_ONE,REAL_POW_DIV]
  ++ `!n. r' n < r + 1 / 2 pow n` by METIS_TAC [POW_HALF_POS,REAL_LT_ADDR,REAL_LET_TRANS,REAL_LT_IMP_LE]
  ++ `!n. N <= n ==> (abs (r' n - r) < 1 / 2 pow n)` by METIS_TAC [ABS_BETWEEN,POW_HALF_POS]
  ++ `?N1. (1 / 2) pow N1 < e:real` by RW_TAC std_ss [POW_HALF_SMALL]
  ++ `!n. N1 <= n ==> ((1 / 2:real) pow n <= (1 / 2) pow N1)` by RW_TAC std_ss [POW_HALF_MONO]
  ++ `!n. N1 <= n ==> ((1 / 2:real) pow n < e)` by METIS_TAC [REAL_LET_TRANS]
  ++ Q.EXISTS_TAC `N + N1`
  ++ RW_TAC real_ss []
  ++ `N <= N + N1` by RW_TAC std_ss [LESS_EQ_ADD]
  ++ `N1 <= N + N1` by RW_TAC std_ss [LESS_EQ_ADD]
  ++ `N <= n /\ N1 <= n` by METIS_TAC [LESS_EQ_TRANS]
  ++ METIS_TAC [REAL_LT_TRANS]);


(*******************************************************************************)
(*          SEQ Positive Simple Functions and Define Integral                  *)
(*******************************************************************************)

val lemma_fn_in_psfis = store_thm
  ("lemma_fn_in_psfis",``!m f n.  (!x. x IN m_space m ==> 0 <= f x) /\ measure_space m /\
                                  f IN measurable (m_space m,measurable_sets m) Borel
			 ==> (fn_seq_integral m f n IN psfis m (fn_seq m f n))``,
  RW_TAC std_ss [IN_psfis_eq,pos_simple_fn_def]
  ++ Q.EXISTS_TAC `count (4 ** n + 1)`
  ++ Q.EXISTS_TAC `(\k. if k IN count (4 ** n) then {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} else {x | x IN m_space m /\ 2 pow n <= f x} )`
  ++ Q.EXISTS_TAC `(\k. if k IN count (4 ** n) then &k / 2 pow n else 2 pow n )`
  ++ `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  ++ `FINITE (count (4 ** n + 1))` by RW_TAC std_ss [FINITE_COUNT]
  ++ `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ `!n k. &k / 2 pow n = Normal (&k / 2 pow n)` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_div_eq]
  ++ `!n z. Normal z / 2 pow n = Normal (z / 2 pow n)` by METIS_TAC [extreal_pow_def,extreal_div_eq,extreal_of_num_def]
  ++ CONJ_TAC
  >> (CONJ_TAC >> METIS_TAC [lemma_fn_5,lemma_fn_4,le_refl]
      ++ CONJ_TAC
      >> (RW_TAC real_ss [fn_seq_def,IN_COUNT,GSYM ADD1,COUNT_SUC,EXTREAL_SUM_IMAGE_THM]
          ++ `(\i. Normal (if i < 4 ** n then &i / 2 pow n else 2 pow n) *
		   indicator_fn (if i < 4 ** n then
		   {x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n}
                   else {x | x IN m_space m /\ 2 pow n <= f x}) t) =
	      (\i. if i < 4 ** n then &i / 2 pow n  *
                   indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t
                   else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t)`
                by (RW_TAC std_ss [FUN_EQ_THM]
                    ++ Cases_on `i < 4 ** n` >> RW_TAC std_ss []
                    ++ RW_TAC std_ss [extreal_of_num_def,extreal_pow_def])
	  ++ POP_ORW
	  ++ `count (4 ** n) DELETE 4 ** n = count (4 ** n)` by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT,LESS_EQ_REFL,NOT_LESS]
          ++ RW_TAC std_ss []
	  ++ `Normal (2 pow n) = 2 pow n` by METIS_TAC [extreal_of_num_def,extreal_pow_def]
	  ++ POP_ORW
	  ++ RW_TAC std_ss [GSYM IN_COUNT]
	  ++ METIS_TAC [add_comm,EXTREAL_SUM_IMAGE_IN_IF_ALT])
      ++ CONJ_TAC
      >> (RW_TAC real_ss []
	  >> (`{x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} =
	       {x | Normal (&i / 2 pow n) <= f x /\ f x < Normal (&(i + 1) / 2 pow n)} INTER m_space m`
	         by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM]
                     ++ `(&i + 1:extreal) = &(i + 1)` by RW_TAC std_ss [extreal_add_def,extreal_of_num_def,REAL_ADD]
                     ++ METIS_TAC [])
	      ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
	  ++ `{x | x IN m_space m /\ 2 pow n <= f x} = {x | Normal (2 pow n) <= f x} INTER m_space m`
	        by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM,extreal_of_num_def,extreal_pow_def]
          ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
      ++ CONJ_TAC
      >> RW_TAC std_ss []
      ++ CONJ_TAC
      >> RW_TAC real_ss [extreal_of_num_def,extreal_pow_def,extreal_le_def,REAL_LT_IMP_LE,POW_POS,REAL_LE_DIV]
      ++ CONJ_TAC
      >> (RW_TAC real_ss [DISJOINT_DEF,IN_COUNT,IN_INTER,EXTENSION,GSPECIFICATION]
         << [REVERSE EQ_TAC
	     >> RW_TAC std_ss [NOT_IN_EMPTY]
   	     ++ RW_TAC real_ss []
	     ++ RW_TAC std_ss [NOT_IN_EMPTY]
	     ++ Cases_on `i<j`
	     >> (`i + 1 <= j` by RW_TAC real_ss []
	         ++ `&(i + 1) / 2:real pow n <= &j / 2 pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
                 ++ `&(i + 1) / 2 pow n <= &j / 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
                 ++ `&j / 2 pow n <= f x` by METIS_TAC []
                 ++ `(&i + 1) = &(i + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	         ++ METIS_TAC [lte_trans,extreal_lt_def])
	     ++ `j < i` by RW_TAC real_ss [LESS_OR_EQ]
	     ++ `j + 1 <= i` by RW_TAC real_ss []
	     ++ `&(j + 1) / 2 pow n <= &i / 2:real pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
	     ++ `&(j + 1) / 2 pow n <= &i / 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             ++ `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	     ++ METIS_TAC [lte_trans,extreal_lt_def],

	     REVERSE EQ_TAC >> RW_TAC std_ss [NOT_IN_EMPTY]
             ++ RW_TAC std_ss []
	     ++ RW_TAC real_ss [NOT_IN_EMPTY]
	     ++ `&(i + 1) <= &(4 ** n):real` by RW_TAC real_ss []
	     ++ FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
 	     ++ `&(i + 1) / 2 pow n <= 4 pow n / 2:real pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
 	     ++ `&(i + 1) / 2 pow n <= 2:real pow n` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
 	     ++ `&(i + 1) / 2 pow n <= 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             ++ `(&i + 1) = &(i + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	     ++ METIS_TAC [le_trans,extreal_lt_def],

	     REVERSE EQ_TAC >> RW_TAC std_ss [NOT_IN_EMPTY]
	     ++ RW_TAC real_ss []
	     ++ RW_TAC std_ss [NOT_IN_EMPTY]
	     ++ `&(j + 1) <= &(4 ** n):real` by RW_TAC real_ss []
	     ++ FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
 	     ++ `&(j + 1) / 2 pow n <= 4:real pow n / 2 pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
 	     ++ `&(j + 1) / 2 pow n <= 2:real pow n` by  METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
 	     ++ `&(j + 1) / 2 pow n <= 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             ++ `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	     ++ METIS_TAC [lte_trans,extreal_lt_def]])
     ++ RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,GSPECIFICATION]
     ++ EQ_TAC
     >> (RW_TAC std_ss []
	 ++ Cases_on `k IN count (4 ** n)`
	 >> FULL_SIMP_TAC std_ss [GSPECIFICATION,lemma_fn_3]
	 ++ FULL_SIMP_TAC std_ss [GSPECIFICATION,lemma_fn_3])
     ++ RW_TAC real_ss [IN_COUNT]
     ++ `2 pow n <= f x \/ ?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC [lemma_fn_3]
     >> (Q.EXISTS_TAC `4 ** n`
	 ++ RW_TAC real_ss [GSPECIFICATION])
     ++ Q.EXISTS_TAC `k`
     ++ FULL_SIMP_TAC real_ss [IN_COUNT,GSPECIFICATION]
     ++ METIS_TAC [])
  ++ RW_TAC real_ss [pos_simple_fn_integral_def,fn_seq_integral_def]
  ++ `4 ** n + 1 = SUC (4 ** n)` by RW_TAC real_ss []
  ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss [COUNT_SUC,IN_COUNT,REAL_SUM_IMAGE_THM]
  ++ `count (4 ** n) DELETE 4 ** n = count (4 ** n)` by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT,LESS_EQ_REFL,NOT_LESS]
  ++ RW_TAC std_ss [GSYM IN_COUNT]
  ++ RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
  ++ Suff `SIGMA
           (\k.
              if k IN count (4 ** n) then
                &k / 2 pow n *
                measure m
                  {x |
                   x IN m_space m /\ Normal (&k / 2 pow n) <= f x /\
                   f x < (&k + 1) / 2 pow n}
              else
                0) (count (4 ** n)) =
	    SIGMA
           (\k.
              (if k IN count (4 ** n) then &k / 2 pow n else 2 pow n) *
              measure m
                (if k IN count (4 ** n) then
                   {x |
                    x IN m_space m /\ Normal (&k / 2 pow n) <= f x /\
                    f x < (&k + 1) / 2 pow n}
                 else
                   {x | x IN m_space m /\ 2 pow n <= f x})) (count (4 ** n))`
  >> RW_TAC std_ss [REAL_ADD_COMM]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [FUN_EQ_THM]);


(*******************************************************************************)
(*                          SEQ integrals convergent                           *)
(*******************************************************************************)

val lemma_fn_integrals_conv = store_thm
  ("lemma_fn_integrals_conv",``!m f n.  (!x. x IN m_space m ==> 0 <= f x) /\ measure_space m /\
                               integrable m f
			  ==> ((\n. fn_seq_integral m f n) --> lim (\n. fn_seq_integral m f n))``,
  RW_TAC real_ss [lim]
  ++ `f IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
  ++ SELECT_ELIM_TAC
  ++ RW_TAC std_ss [GSYM convergent]
  ++ MATCH_MP_TAC SEQ_ICONV
  ++ RW_TAC std_ss [SEQ_BOUNDED]
  >> (`!n. 0 <= fn_seq_integral m f n` by RW_TAC std_ss [lemma_fn_6]
      ++ `!n. abs (fn_seq_integral m f n) = fn_seq_integral m f n` by RW_TAC std_ss [ABS_REFL]
      ++ ASM_SIMP_TAC std_ss []
      ++ Q.EXISTS_TAC `pos_fn_integral m f + 1`
      ++ RW_TAC std_ss []
      ++ MATCH_MP_TAC REAL_LT_ADD1
      ++ `fn_seq_integral m f n IN psfis m (fn_seq m f n)` by RW_TAC std_ss [lemma_fn_in_psfis]
      ++ `fn_seq_integral m f n = pos_fn_integral m (fn_seq m f n)`
           by METIS_TAC [pos_fn_integral_pos_simple_fn,IN_psfis_eq]
      ++ POP_ORW
      ++ MATCH_MP_TAC pos_fn_integral_mono
      ++ RW_TAC std_ss [lemma_fn_5,lemma_fn_upper_bounded]
      ++ MATCH_MP_TAC integrable_bounded
      ++ Q.EXISTS_TAC `f`
      ++ RW_TAC std_ss []
      >> METIS_TAC [lemma_fn_upper_bounded,lemma_fn_5,abs_refl]
      ++ METIS_TAC [lemma_fn_in_psfis,IN_psfis_eq,IN_MEASURABLE_BOREL_POS_SIMPLE_FN])
  ++ FULL_SIMP_TAC std_ss [real_ge,GREATER_EQ]
  ++ MATCH_MP_TAC psfis_mono
  ++ Q.EXISTS_TAC `m` ++ Q.EXISTS_TAC `fn_seq m f n` ++ Q.EXISTS_TAC `fn_seq m f m'`
  ++ RW_TAC std_ss [lemma_fn_in_psfis]
  ++ `mono_increasing (\n. fn_seq m f n x)` by RW_TAC std_ss [lemma_fn_mono_increasing]
  ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_def]);


(*****************************************************************)

val integral_sequence = store_thm
  ("integral_sequence",``!m f.  (!x. x IN m_space m ==> 0 <= f x) /\ measure_space m /\ integrable m f
			==> (pos_fn_integral m f = lim (\n. fn_seq_integral m f n))``,
  RW_TAC std_ss []
  ++ MATCH_MP_TAC pos_fn_integral_eq_mono_conv_limit_borel
  ++ Q.EXISTS_TAC `(\n. fn_seq m f n)`
  ++ Q.EXISTS_TAC `(\n. fn_seq_integral m f n)`
  ++ CONJ_TAC
  >> RW_TAC std_ss []
  ++ CONJ_TAC
  >> RW_TAC std_ss [lemma_fn_mono_increasing]
  ++ CONJ_TAC
  >> RW_TAC std_ss [lemma_fn_sup]
  ++ CONJ_TAC
  >> FULL_SIMP_TAC std_ss [lemma_fn_in_psfis,integrable_def]
  ++ CONJ_TAC
  >> RW_TAC std_ss [lemma_fn_integrals_conv]
  ++ RW_TAC std_ss [lemma_fn_upper_bounded]);

val integral_sequence_conv = store_thm
  ("integral_sequence_conv",``!m f.  (!x. x IN m_space m ==> 0 <= f x) /\ measure_space m /\ integrable m f
			==> (\n. fn_seq_integral m f n) --> pos_fn_integral m f``,
    METIS_TAC [integral_sequence,lim,SEQ_UNIQ,lemma_fn_integrals_conv]);

val integrable_thm_lemma = store_thm
  ("integrable_thm_lemma",``!m f. measure_space m /\ integrable m f ==>
	(?fi ri r. (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = fn_plus f x)) /\
	(!i. ri i IN psfis m (fi i)) /\ ri --> r /\
	(!i x. x IN m_space m ==> (fi i) x <= fn_plus f x) /\
	(pos_fn_integral m (fn_plus f) = r)) /\

	(?gi vi v. (!x. x IN m_space m ==> mono_increasing (\i. gi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) univ(:num)) = fn_minus f x)) /\
	(!i. vi i IN psfis m (gi i)) /\ vi --> v /\
	(!i x. x IN m_space m ==> (gi i) x <= fn_minus f x) /\
	(pos_fn_integral m (fn_minus f) = v))``,
    REPEAT STRIP_TAC
    >> (Q.EXISTS_TAC `(\n. fn_seq m (fn_plus f) n)`
	++ Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_plus f) n)`
	++ Q.EXISTS_TAC `lim (\n. fn_seq_integral m (fn_plus f) n)`
	++ CONJ_TAC
	>> RW_TAC std_ss [FN_PLUS_POS,lemma_fn_mono_increasing]
	++ CONJ_TAC
	>> RW_TAC std_ss [FN_PLUS_POS,lemma_fn_sup]
	++ CONJ_TAC
	>> FULL_SIMP_TAC std_ss [FN_PLUS_POS,lemma_fn_in_psfis,integrable_def,IN_MEASURABLE_BOREL_FN_PLUS]
	++ CONJ_TAC
	>> RW_TAC std_ss [FN_PLUS_POS,lemma_fn_integrals_conv,fn_plus_integrable]
	++ CONJ_TAC
	++ RW_TAC std_ss [FN_PLUS_POS,lemma_fn_upper_bounded]
	++ RW_TAC std_ss [FN_PLUS_POS,integral_sequence,fn_plus_integrable])
    ++ Q.EXISTS_TAC `(\n. fn_seq m (fn_minus f) n)`
    ++ Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_minus f) n)`
    ++ Q.EXISTS_TAC `lim (\n. fn_seq_integral m (fn_minus f) n)`
    ++ CONJ_TAC
    >> RW_TAC std_ss [FN_MINUS_POS,lemma_fn_mono_increasing]
    ++ CONJ_TAC
    >> RW_TAC std_ss [FN_MINUS_POS,lemma_fn_sup]
    ++ CONJ_TAC
    >> FULL_SIMP_TAC std_ss [FN_MINUS_POS,lemma_fn_in_psfis,integrable_def,IN_MEASURABLE_BOREL_FN_MINUS]
    ++ CONJ_TAC
    >> RW_TAC std_ss [FN_MINUS_POS,lemma_fn_integrals_conv,fn_minus_integrable]
    ++ CONJ_TAC
    ++ RW_TAC std_ss [FN_MINUS_POS,lemma_fn_upper_bounded]
    ++ RW_TAC std_ss [FN_MINUS_POS,integral_sequence,fn_minus_integrable]);

val integrable_thm = store_thm
  ("integrable_thm",``!m f. measure_space m ==>
        (integrable m f =
	(?fi ri r. (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = fn_plus f x)) /\
	(!i. ri i IN psfis m (fi i)) /\ ri --> r /\
	(!i x. x IN m_space m ==> (fi i) x <= fn_plus f x) /\
	(pos_fn_integral m (fn_plus f) = r)) /\

	(?gi vi v. (!x. x IN m_space m ==> mono_increasing (\i. gi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) univ(:num)) = fn_minus f x)) /\
	(!i. vi i IN psfis m (gi i)) /\ vi --> v /\
	(!i x. x IN m_space m ==> (gi i) x <= fn_minus f x) /\
	(pos_fn_integral m (fn_minus f) = v)))``,
  REPEAT STRIP_TAC
  ++ EQ_TAC  >> FULL_SIMP_TAC std_ss [integrable_thm_lemma]
  ++ STRIP_TAC
  ++ `fn_plus f IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
          ++ Q.EXISTS_TAC `fi`
          ++ FULL_SIMP_TAC std_ss [space_def,IN_psfis_eq,pos_simple_fn_integrable]
          ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [measure_space_def]
          ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL_POS_SIMPLE_FN]
          ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_suc,ADD1])
  ++ `fn_minus f IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
          ++ Q.EXISTS_TAC `gi`
          ++ FULL_SIMP_TAC std_ss [space_def,IN_psfis_eq,pos_simple_fn_integrable]
          ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [measure_space_def]
          ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL_POS_SIMPLE_FN]
          ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_suc,ADD1])
  ++ `f IN measurable (m_space m,measurable_sets m) Borel`
      by METIS_TAC [IN_MEASURABLE_BOREL_PLUS_MINUS]
  ++ RW_TAC std_ss [Once integrable_plus_minus]
  >> (RW_TAC std_ss [Once integrable_pos,FN_PLUS_POS,GSPECIFICATION,IN_psfis_eq]
      ++ Q.EXISTS_TAC `pos_fn_integral m (fn_plus f)`
      ++ RW_TAC std_ss []
      ++ MATCH_MP_TAC psfis_mono_conv_mono_borel
      ++ Q.EXISTS_TAC `m`
      ++ Q.EXISTS_TAC `fn_plus f`
      ++ Q.EXISTS_TAC `fi`
      ++ Q.EXISTS_TAC `ri`
      ++ Q.EXISTS_TAC `g`
      ++ RW_TAC std_ss [IN_psfis_eq]
      ++ METIS_TAC [])
  ++ RW_TAC std_ss [Once integrable_pos,FN_MINUS_POS,GSPECIFICATION,IN_psfis_eq]
  ++ Q.EXISTS_TAC `pos_fn_integral m (fn_minus f)`
  ++ RW_TAC std_ss []
  ++ MATCH_MP_TAC psfis_mono_conv_mono_borel
  ++ Q.EXISTS_TAC `m`
  ++ Q.EXISTS_TAC `fn_minus f`
  ++ Q.EXISTS_TAC `gi`
  ++ Q.EXISTS_TAC `vi`
  ++ Q.EXISTS_TAC `g`
  ++ RW_TAC std_ss [IN_psfis_eq]
  ++ METIS_TAC []);

val integrable_thm_pos = store_thm
  ("integrable_thm_pos",``!m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) ==>
       (integrable m f =
	(?fi ri r. (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = f x)) /\
	(!i. ri i IN psfis m (fi i)) /\ ri --> r /\
	(!i x. x IN m_space m ==> (fi i) x <=  f x) /\
	(pos_fn_integral m f = r)))``,
  RW_TAC std_ss [Once integrable_mspace, integrable_thm]
  ++ `fn_minus (\x. f x * indicator_fn (m_space m) x) = (\x. 0)`
      by (RW_TAC std_ss [FUN_EQ_THM,fn_minus_def,indicator_fn_def,mul_rzero,mul_rone]
          ++ RW_TAC std_ss [mul_rzero,mul_rone,neg_0]
	  ++ METIS_TAC [extreal_lt_def,mul_rone])
  ++ `fn_plus (\x. f x * indicator_fn (m_space m) x) = (\x. f x * indicator_fn (m_space m) x)`
       by (MATCH_MP_TAC FN_PLUS_POS_ID
           ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl])
  ++ RW_TAC std_ss []
  ++ `(?gi vi.
       (!x. x IN m_space m ==> mono_increasing (\i. gi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) univ(:num)) = 0)) /\
       (!i. vi i IN psfis m (gi i)) /\ vi --> pos_fn_integral m (\x. 0) /\
       !i x. x IN m_space m ==> gi i x <= 0) = T`
        by (RW_TAC std_ss []
	    ++ Q.EXISTS_TAC `\i. (\x. 0)`
	    ++ Q.EXISTS_TAC `\i. 0`
	    ++ RW_TAC std_ss [le_refl,psfis_zero,pos_fn_integral_zero,ext_mono_increasing_def,SEQ_CONST]
	    ++ Suff `IMAGE (\i. 0) univ(:num) = (\y. y = 0)` >> RW_TAC std_ss [sup_const]
	    ++ RW_TAC std_ss [EXTENSION,IN_ABS,IN_UNIV,IN_IMAGE])
  ++ POP_ORW
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [GSYM pos_fn_integral_mspace]
  ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]);

val integral_thm = store_thm
  ("integral_thm",``!m f.  measure_space m /\ integrable m f
       ==> (\n. fn_seq_integral m (fn_plus f) n - fn_seq_integral m (fn_minus f) n) --> integral m f``,
  RW_TAC std_ss []
  ++ `(\n. fn_seq_integral m (fn_plus f) n) --> lim (\n. fn_seq_integral m (fn_plus f) n)`
       by METIS_TAC [lemma_fn_integrals_conv,integrable_plus_minus,FN_PLUS_POS]
  ++ `(\n. fn_seq_integral m (fn_minus f) n) --> lim (\n. fn_seq_integral m (fn_minus f) n)`
       by METIS_TAC [lemma_fn_integrals_conv,integrable_plus_minus,FN_MINUS_POS]
  ++ `(\n. (\n. fn_seq_integral m (fn_plus f) n) n - (\n. fn_seq_integral m (fn_minus f) n) n) -->
             (integral m f)`
         by METIS_TAC [SEQ_SUB,integral_sequence,FN_PLUS_POS,FN_MINUS_POS,
                       integral_def,integrable_plus_minus,integral_def]
  ++ FULL_SIMP_TAC std_ss []);

val pos_fn_integral_cmul = store_thm
  ("pos_fn_integral_cmul",``!m f c. measure_space m /\ integrable m f /\
			       (!x. x IN m_space m ==> 0 <= f x) /\ 0 <= c
			==> (pos_fn_integral m (\x. Normal c * (f x)) = c * pos_fn_integral m f)``,
  RW_TAC std_ss []
  ++ `?fi ui u.
           (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
           (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = f x)) /\
           (!i. ui i IN psfis m (fi i)) /\ ui --> u /\
           (!i x. x IN m_space m ==> fi i x <= f x) /\ (pos_fn_integral m f = u)`
		by ((MP_TAC o Q.SPECL [`m`,`f`]) integrable_thm_pos ++ RW_TAC std_ss [])
  ++ `f IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
  ++ `(\x. Normal c * f x) IN measurable (m_space m,measurable_sets m) Borel`
	by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
	++ RW_TAC std_ss [] ++ METIS_TAC [measure_space_def])
  ++ `0 <= Normal c` by METIS_TAC [extreal_of_num_def,extreal_le_def]
  ++ `!x. x IN m_space m ==> mono_increasing (\i. (\i x. Normal c * fi i x) i x)`
          by FULL_SIMP_TAC std_ss [ext_mono_increasing_def,le_lmul_imp]
  ++ `!x. x IN m_space m ==> (sup (IMAGE (\i. Normal c * fi i x) univ(:num)) = Normal c * f x)`
	by RW_TAC std_ss [sup_cmul]
  ++ `!i. (\i. c * ui i) i IN psfis m ((\i x. Normal c * fi i x) i)` by METIS_TAC [psfis_cmul]
  ++ `(\i. c * ui i) --> (c * u)` by RW_TAC std_ss [SEQ_MUL,SEQ_CONST]
  ++ `!i x. x IN m_space m ==> (\i x. Normal c * fi i x) i x <= (\x. Normal c * f x) x`
       by RW_TAC std_ss [le_lmul_imp]
  ++ (MP_TAC o Q.SPECL [`m`,`(\x. Normal c * f x)`,`(\i. (\x. Normal c * (fi i x)))`,
     	       	       	`(\i. c * (ui i))`,`c*u`]) pos_fn_integral_eq_mono_conv_limit_borel
  ++ RW_TAC std_ss []);

val pos_fn_integral_cmul_indicator = store_thm
  ("pos_fn_integral_cmul_indicator",
   ``!m s c. measure_space m /\ s IN measurable_sets m /\ 0 <= c ==>
	   (pos_fn_integral m (\x. Normal c * indicator_fn s x) = c * measure m s)``,
  RW_TAC std_ss []
  ++ `!x. 0 <= indicator_fn s x` by RW_TAC std_ss [indicator_fn_def,le_refl,le_01]
  ++ METIS_TAC [pos_fn_integral_cmul,indicator_fn_integrable,pos_fn_integral_pos_simple_fn,
     	        pos_simple_fn_integral_indicator]);

val integrable_add_pos = store_thm
  ("integrable_add_pos",``!m f g. measure_space m /\ integrable m f /\ integrable m g /\
			        (!x. x IN m_space m ==> 0 <= f x /\ 0 <= g x)
			   ==> integrable m (\x. f x + g x)``,
	RW_TAC std_ss []
	++ `!x. x IN m_space m ==> 0 <= (\x. f x + g x) x` by RW_TAC real_ss [le_add]
	++ `f IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
	++ `g IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
	++ `(\x. f x + g x) IN measurable (m_space m, measurable_sets m) Borel`
		by (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD ++ METIS_TAC [measure_space_def])
	++ (MP_TAC o Q.SPECL [`m`,`(\x. f x + g x)`]) integrable_pos
	++ RW_TAC std_ss [GSPECIFICATION]
	++ Q.EXISTS_TAC `(pos_fn_integral m f) + (pos_fn_integral m g)`
	++ RW_TAC real_ss []
	++ `?fi ri r.
           (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
           (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = f x)) /\
           (!i. ri i IN psfis m (fi i)) /\ ri --> r /\
           (!i x. x IN m_space m ==> fi i x <= f x) /\
           (pos_fn_integral m f = r)`
		by ((MP_TAC o Q.SPECL [`m`,`f`]) integrable_thm_pos ++ RW_TAC std_ss [])
	++ `?fi ri r.
           (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
           (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = g x)) /\
           (!i. ri i IN psfis m (fi i)) /\ ri --> r /\
           (!i x. x IN m_space m ==> fi i x <= g x) /\
           (pos_fn_integral m g = r)`
		by ((MP_TAC o Q.SPECL [`m`,`g`]) integrable_thm_pos ++ RW_TAC std_ss [])
	++ MATCH_MP_TAC psfis_mono_conv_mono_borel
	++ Q.EXISTS_TAC `m`
	++ Q.EXISTS_TAC `(\x. f x + g x)`
	++ Q.EXISTS_TAC `(\i. (\x. (fi i x) + (fi' i x)))`
	++ Q.EXISTS_TAC `(\i. ri i + ri' i)`
	++ Q.EXISTS_TAC `g'`
	++ `!i. ri i + ri' i IN psfis m (\x. fi i x + fi' i x)` by METIS_TAC [psfis_add]
	++ `!x. x IN m_space m ==> (sup (IMAGE (\i. (\i. fi i x) i + (\i. fi' i x) i) univ(:num)) =
                      sup (IMAGE (\i. fi i x) univ(:num)) + sup (IMAGE (\i. fi' i x) univ(:num)))`
             by (REPEAT STRIP_TAC
	         ++ MATCH_MP_TAC sup_add_mono
		 ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_suc]
		 ++ METIS_TAC [psfis_pos])
	++ `(\i. ri i + ri' i) --> (pos_fn_integral m f + pos_fn_integral m g)` by METIS_TAC [SEQ_ADD]
	++ `(\x. f x + g x) IN measurable (m_space m,measurable_sets m) Borel`
		by ( MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
		     ++ Q.EXISTS_TAC `f`
		     ++ Q.EXISTS_TAC `g`
		     ++ RW_TAC std_ss []
		     ++ METIS_TAC [measure_space_def])
	++ FULL_SIMP_TAC real_ss [ext_mono_increasing_def]
	++ METIS_TAC [le_add2]);

val integrable_add_lemma = store_thm
  ("integrable_add_lemma",``!m f g. (measure_space m /\ integrable m f /\ integrable m g)
			   ==> (integrable m (\x. fn_plus f x + fn_plus g x) /\
				integrable m (\x. fn_minus f x + fn_minus g x))``,
  RW_TAC std_ss []
  >> (MATCH_MP_TAC integrable_add_pos ++ METIS_TAC [fn_plus_integrable,FN_PLUS_POS])
  ++ MATCH_MP_TAC integrable_add_pos ++ METIS_TAC [fn_minus_integrable,FN_MINUS_POS]);

val integrable_add = store_thm
  ("integrable_add",``!m f1 f2. measure_space m /\ integrable m f1 /\ integrable m f2
			   ==> integrable m (\x. f1 x + f2 x)``,
  RW_TAC std_ss []
  ++ `(\x. f1 x + f2 x) IN measurable (m_space m,measurable_sets m) Borel`
        by (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
  	    ++ Q.EXISTS_TAC `f1`
	    ++ Q.EXISTS_TAC `f2`
	    ++ RW_TAC std_ss []
	    ++ METIS_TAC [measure_space_def,integrable_def])
  ++ RW_TAC std_ss [Once integrable_plus_minus]
  >> (MATCH_MP_TAC integrable_bounded
	++ Q.EXISTS_TAC `(\x. fn_plus f1 x + fn_plus f2 x)`
	++ RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS,integrable_add_lemma]
	++ METIS_TAC [abs_refl,FN_PLUS_POS,FN_PLUS_ADD_LE])
  ++ MATCH_MP_TAC integrable_bounded
  ++ Q.EXISTS_TAC `(\x. fn_minus f1 x + fn_minus f2 x)`
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_MINUS,integrable_add_lemma]
  ++ METIS_TAC [abs_refl,FN_MINUS_POS,FN_MINUS_ADD_LE]);

val integrable_add_alt = store_thm
  ("integrable_add_alt",``!m f f1 f2. measure_space m /\ (!x. x IN m_space m ==> (f x = f1 x + f2 x)) /\
  			       	      integrable m f1 /\ integrable m f2
				   ==> integrable m f``,
  RW_TAC std_ss [Once integrable_mspace]
  ++ `(\x. f x * indicator_fn (m_space m) x) =
      (\x. (\x. f1 x * indicator_fn (m_space m) x) x +  (\x. f2 x * indicator_fn (m_space m) x) x)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,mul_rzero,mul_rone]
           ++ METIS_TAC [mul_rzero,mul_rone,add_rzero])
  ++ POP_ORW
  ++ MATCH_MP_TAC integrable_add
  ++ METIS_TAC [integrable_mspace]);

val integrable_sum = store_thm
  ("integrable_sum",``!m f s. (FINITE s /\ measure_space m /\
	(!i. i IN s ==> integrable m (f i)))
	 ==> integrable m (\x. SIGMA (\i. (f i) x) s)``,
  Suff `!s:'b->bool. FINITE s ==> (\s:'b->bool. !m f. (FINITE s /\ measure_space m /\
	(!i. i IN s ==> integrable m (f i)))
	 ==> integrable m (\x. SIGMA (\i. (f i) x) s) ) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, NOT_IN_EMPTY, FINITE_INSERT,DELETE_NON_ELEMENT,IN_INSERT]
  >> METIS_TAC [integrable_const,extreal_of_num_def]
  ++ `(\x. SIGMA (\i. f i x) s) IN measurable (m_space m,measurable_sets m) Borel`
        by (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUM
	    ++ RW_TAC std_ss []
	    ++ METIS_TAC [measure_space_def,integrable_def])
  ++ METIS_TAC [integrable_add]);

val integrable_sub = store_thm
  ("integrable_sub",``!m f1 f2. measure_space m /\ integrable m f1 /\ integrable m f2
	   ==> integrable m (\x. f1 x - f2 x)``,
  RW_TAC std_ss []
  ++ `(\x. f1 x - f2 x) = (\x. f1 x + (\x. -f2 x) x)` by RW_TAC std_ss [FUN_EQ_THM,extreal_sub_add]
  ++ POP_ORW
  ++ MATCH_MP_TAC integrable_add
  ++ RW_TAC std_ss []
  ++ `(\x. -f2 x) = (\x. Normal (-1) * f2 x)`
      by METIS_TAC [FUN_EQ_THM,neg_minus1,extreal_of_num_def,extreal_ainv_def]
  ++ POP_ORW
  ++ METIS_TAC [integrable_cmul]);

val integrable_sub_alt = store_thm
  ("integrable_sub_alt",``!m f f1 f2. measure_space m /\ (!x. x IN m_space m ==> (f x = f1 x - f2 x)) /\
  			       	      integrable m f1 /\ integrable m f2
				   ==> integrable m f``,
  RW_TAC std_ss [Once integrable_mspace]
  ++ `(\x. f x * indicator_fn (m_space m) x) =
      (\x. (\x. f1 x * indicator_fn (m_space m) x) x -  (\x. f2 x * indicator_fn (m_space m) x) x)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,mul_rzero,mul_rone]
           ++ METIS_TAC [mul_rzero,mul_rone,sub_rzero])
  ++ POP_ORW
  ++ MATCH_MP_TAC integrable_sub
  ++ METIS_TAC [integrable_mspace]);

val integrable_indicator = store_thm
("integrable_indicator",``!m s. measure_space m /\ s IN measurable_sets m ==> integrable m (indicator_fn s)``,
  METIS_TAC [pos_simple_fn_integrable,pos_simple_fn_indicator]);

val integrable_mul_indicator = store_thm
  ("integrable_mul_indicator",``!m f s. measure_space m /\ integrable m f /\ s IN measurable_sets m
		==> integrable m (\x. f x * indicator_fn s x)``,
  RW_TAC std_ss []
  ++ `indicator_fn s IN measurable (m_space m,measurable_sets m) Borel`
	    by (MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
		++ METIS_TAC [measure_space_def,subsets_def,measurable_sets_def])
  ++ `(\x. f x * indicator_fn s x) IN measurable (m_space m,measurable_sets m) Borel`
     	    by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,measure_space_def,
                          subsets_def,measurable_sets_def,integrable_def]
  ++ `integrable m (\x. fn_plus f x + fn_minus f x)`
       by METIS_TAC [fn_plus_integrable, fn_minus_integrable,integrable_add]
  ++ MATCH_MP_TAC integrable_bounded
  ++ Q.EXISTS_TAC `(\x. fn_plus f x + fn_minus f x)`
  ++ `!x. 0 <= fn_plus f x + fn_minus f x` by METIS_TAC [FN_PLUS_POS,FN_MINUS_POS,le_add]
  ++ `abs 0 = 0` by METIS_TAC [extreal_abs_def,extreal_of_num_def,REAL_ABS_0]
  ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
  ++ Cases_on `f x`
  ++ RW_TAC real_ss [extreal_abs_def,le_infty,lt_infty,fn_minus_def,fn_plus_def,extreal_ainv_def,add_rzero,
     	    	    add_lzero,extreal_add_def,extreal_le_def,abs,REAL_ABS_0,ABS_REFL,lt_antisym]
  ++ FULL_SIMP_TAC std_ss [extreal_abs_def,le_infty,lt_infty,fn_minus_def,fn_plus_def,extreal_ainv_def,
     		   	  add_rzero,add_lzero,extreal_add_def,extreal_le_def,abs,REAL_ABS_0,ABS_REFL,
			  lt_antisym]
  ++ METIS_TAC [lt_infty,extreal_of_num_def,num_not_infty,lt_antisym,extreal_lt_eq,REAL_LT_IMP_LE,
     	        REAL_LE_ANTISYM,REAL_NEG_0,REAL_LE_REFL,lt_antisym,real_lt,extreal_le_def,extreal_abs_def,
		lt_imp_le]);

val integrable_abs = store_thm
  ("integrable_abs",``!m f. measure_space m /\ integrable m f ==> integrable m (\x. abs (f x))``,
  RW_TAC std_ss []
  ++ `(\x. abs (f x)) = (\x. (fn_plus f) x + (fn_minus f) x)`
       by (RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
           ++ Cases_on `f x` ++ RW_TAC std_ss [extreal_abs_def,extreal_add_def,lt_infty,num_not_infty,
	      	       	     	       	       extreal_ainv_def,add_lzero,add_rzero]
           ++ METIS_TAC [lt_infty,num_not_infty,lt_antisym,extreal_lt_eq,extreal_of_num_def,REAL_LT_IMP_LE,
	                ABS_REFL,real_lt,abs,le_antisym,extreal_11,REAL_LE_REFL,extreal_lt_def])
  ++ POP_ORW
  ++ METIS_TAC [integrable_plus_minus,integrable_add]);

val integrable_max = store_thm
  ("integrable_max",``!m f g. measure_space m /\ integrable m f /\ integrable m g
                        ==> integrable m (\x. max (f x) (g x))``,
  RW_TAC std_ss []
  ++ MATCH_MP_TAC integrable_bounded
  ++ Q.EXISTS_TAC `\x. (\x. abs (f x)) x + (\x. abs (g x)) x`
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC >> METIS_TAC [integrable_abs,integrable_add]
  ++ REVERSE CONJ_TAC >> (MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX ++ METIS_TAC [integrable_def,measure_space_def])
  ++ RW_TAC std_ss []
  ++ Cases_on `f x` ++ Cases_on `g x`
  ++ RW_TAC std_ss [extreal_abs_def,extreal_max_def,extreal_add_def,add_rzero,
     	    	    add_lzero,extreal_le_def,le_infty]
  ++ METIS_TAC [REAL_LE_ADDL,REAL_LE_ADDR,ABS_POS]);

val pos_fn_integral_add = store_thm
  ("pos_fn_integral_add",``!m f g. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x /\ 0 <= g x) /\
            integrable m f /\ integrable m g ==>
            (pos_fn_integral m (\x. f x + g x) = pos_fn_integral m f + pos_fn_integral m g)``,
  RW_TAC std_ss []
  ++ `?fi ri r.
           (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
           (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = f x)) /\
           (!i. ri i IN psfis m (fi i)) /\ ri --> r /\
           (!i x. x IN m_space m ==> fi i x <= f x) /\
           (pos_fn_integral m f = r)`
		by ((MP_TAC o Q.SPECL [`m`,`f`]) integrable_thm_pos ++ RW_TAC std_ss [])
  ++ `?fi ri r.
           (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
           (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = g x)) /\
           (!i. ri i IN psfis m (fi i)) /\ ri --> r /\
           (!i x. x IN m_space m ==> fi i x <= g x) /\
           (pos_fn_integral m g = r)`
		by ((MP_TAC o Q.SPECL [`m`,`g`]) integrable_thm_pos ++ RW_TAC std_ss [])
  ++ MATCH_MP_TAC pos_fn_integral_eq_mono_conv_limit_borel
  ++ Q.EXISTS_TAC `\i. \x. fi i x + fi' i x`
  ++ Q.EXISTS_TAC `\i. ri i + ri' i`
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [ext_mono_increasing_def,le_add2]
  ++ CONJ_TAC
  >> (`!x. x IN m_space m ==> (sup (IMAGE (\i. (\i. fi i x) i + (\i. fi' i x) i) univ(:num)) =
            sup (IMAGE (\i. fi i x) univ(:num)) + sup (IMAGE (\i. fi' i x) univ(:num)))`
       by (REPEAT STRIP_TAC
	   ++ MATCH_MP_TAC sup_add_mono
	   ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_suc]
	   ++ METIS_TAC [psfis_pos])
      ++ FULL_SIMP_TAC std_ss [])
  ++ CONJ_TAC >> METIS_TAC [psfis_add]
  ++ CONJ_TAC >> METIS_TAC [SEQ_ADD]
  ++ METIS_TAC [le_add2]);

val pos_fn_integral_sum = store_thm
  ("pos_fn_integral_sum",``!m f s. FINITE s /\ measure_space m /\
        (!i. i IN s ==> (!x. x IN m_space m ==> 0 <= f i x)) /\
	(!i. i IN s ==> integrable m (f i)) ==>
	   (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) = SIGMA (\i. pos_fn_integral m (f i)) s)``,
  Suff `!s:'b->bool. FINITE s ==> (\s:'b->bool. !m f. measure_space m /\ (!i. i IN s ==> (!x. x IN m_space m ==> 0 <= f i x)) /\
	   (!i. i IN s ==> integrable m (f i)) ==>
   	   (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) = SIGMA (\i. pos_fn_integral m (f i)) s)) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,REAL_SUM_IMAGE_THM,pos_fn_integral_zero,DELETE_NON_ELEMENT]
  ++ `SIGMA (\i. pos_fn_integral m (f i)) s = pos_fn_integral m (\x. SIGMA (\i. f i x) s)` by METIS_TAC [IN_INSERT]
  ++ POP_ORW
  ++ `(\x. f e x + SIGMA (\i. f i x) s) = (\x. f e x + (\x. SIGMA (\i. f i x) s) x)` by METIS_TAC []
  ++ POP_ORW
  ++ MATCH_MP_TAC pos_fn_integral_add
  ++ FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ RW_TAC std_ss []
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_POS]
  ++ RW_TAC std_ss [integrable_sum]);

val pos_fn_integral_sum_cmul_indicator = store_thm
("pos_fn_integral_sum_cmul_indicator",
   ``!m s a x. measure_space m /\ FINITE s /\ (!i. i IN s ==> 0 <= x i) /\
            (!i. i IN s ==> a i IN measurable_sets m)  ==>
	   (pos_fn_integral m (\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s) =
            SIGMA (\i. (x i) * measure m (a i)) s)``,
  RW_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`(\i. (\t. Normal (x i) * indicator_fn (a i) t))`,`s`]) pos_fn_integral_sum
  ++ RW_TAC std_ss []
  ++ `!i. i IN s ==> !x'. x' IN m_space m ==> 0 <= Normal (x i) * indicator_fn (a i) x'`
       by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
           ++ METIS_TAC [le_refl,mul_rzero,mul_rone,extreal_of_num_def,extreal_le_def])
  ++ `(!i. i IN s ==> integrable m (\t. Normal (x i) * indicator_fn (a i) t))`
       by METIS_TAC [integrable_cmul,integrable_indicator]
  ++ FULL_SIMP_TAC std_ss []
  ++ NTAC 3 (POP_ASSUM (K ALL_TAC ))
  ++ `!i t. 0 <= indicator_fn (a i) t` by RW_TAC std_ss [indicator_fn_def,le_refl,le_01]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [pos_fn_integral_cmul_indicator]);

val pos_fn_integral_disjoint_sets = store_thm
  ("pos_fn_integral_disjoint_sets",``!m f s t. measure_space m /\ DISJOINT s t /\
  					       s IN measurable_sets m /\ t IN measurable_sets m /\
					       integrable m f  /\ (!x. x IN m_space m ==> 0 <= f x)
		==> (pos_fn_integral m (\x. f x * indicator_fn (s UNION t) x) =
		     pos_fn_integral m (\x. f x * indicator_fn s x) +
		     pos_fn_integral m (\x. f x * indicator_fn t x))``,
  RW_TAC std_ss []
  ++ `(\x. f x * indicator_fn (s UNION t) x) =
      (\x. (\x. f x * indicator_fn s x) x + (\x. f x * indicator_fn t x) x)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,IN_DISJOINT,IN_UNION,mul_rone,mul_rzero]
           ++ Cases_on `x IN s`
	   >> (RW_TAC std_ss [mul_rone,mul_rzero,add_rzero] ++ METIS_TAC [EXTENSION,IN_DISJOINT])
	   ++ RW_TAC std_ss [mul_rone,mul_rzero,add_lzero])
  ++ POP_ORW
  ++ MATCH_MP_TAC pos_fn_integral_add
  ++ RW_TAC std_ss [integrable_mul_indicator,indicator_fn_def,mul_rzero,mul_rone,le_refl]);

val pos_fn_integral_disjoint_sets_sum = store_thm
  ("pos_fn_integral_disjoint_sets_sum",``!m f s a. FINITE s /\ measure_space m /\
	(!i. i IN s ==> a i IN measurable_sets m) /\ (!x. x IN m_space m ==> 0 <= f x) /\
	(!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\ integrable m f
	==> (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
	     SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s)``,

  Suff `!s:'b->bool. FINITE s ==> (\s:'b->bool. !m f a.  measure_space m /\
       (!i. i IN s ==> a i IN measurable_sets m) /\  (!x. x IN m_space m ==> 0 <= f x) /\
	(!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\ integrable m f
	==> (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
	     SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s) ) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM,IMAGE_EMPTY,BIGUNION_EMPTY,FINITE_INSERT,
     	    	    DELETE_NON_ELEMENT,IN_INSERT,BIGUNION_INSERT,IMAGE_INSERT]
  >> RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,NOT_IN_EMPTY,pos_fn_integral_zero]
  ++  `~(e IN s)` by METIS_TAC [DELETE_NON_ELEMENT]
  ++ `DISJOINT (a e) (BIGUNION (IMAGE a s))`
       by (RW_TAC std_ss [DISJOINT_BIGUNION,IN_IMAGE] ++ METIS_TAC [])
  ++ `countable (IMAGE a s)` by METIS_TAC [COUNTABLE_IMAGE,FINITE_COUNTABLE]
  ++ `(IMAGE a s) SUBSET measurable_sets m`
       by (RW_TAC std_ss [SUBSET_DEF,IMAGE_DEF,GSPECIFICATION]
	   ++ METIS_TAC [])
  ++ `BIGUNION (IMAGE a s) IN measurable_sets m`
	by METIS_TAC [sigma_algebra_def,measure_space_def,subsets_def,measurable_sets_def]
  ++ METIS_TAC [pos_fn_integral_disjoint_sets]);

val pos_fn_integral_split = store_thm
("pos_fn_integral_split",``!m f s. measure_space m /\ s IN measurable_sets m /\
           (!x. x IN m_space m ==> 0 <= f x) /\ integrable m f ==>
           (pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn s x) +
                                  pos_fn_integral m  (\x. f x * indicator_fn (m_space m DIFF s) x))``,
  RW_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`m_space m DIFF s`]) pos_fn_integral_disjoint_sets
  ++ RW_TAC std_ss [DISJOINT_DIFF,MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ `s UNION (m_space m DIFF s) = m_space m` by METIS_TAC [UNION_DIFF,MEASURE_SPACE_SUBSET_MSPACE]
  ++ METIS_TAC [pos_fn_integral_mspace]);


val integral_pos_fn = store_thm
("integral_pos_fn",``!m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x)
                       ==> (integral m f = pos_fn_integral m f)``,
  RW_TAC std_ss [integral_def,pos_fn_integral_mspace,FN_PLUS_POS,FN_MINUS_POS]
  ++ `(\x. fn_plus f x * indicator_fn (m_space m) x) = fn_plus (\x. f x * indicator_fn (m_space m) x)`
      by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl,FN_PLUS_POS,fn_plus_def]
          ++ METIS_TAC [mul_rzero,mul_rone])
  ++ `(\x. fn_minus f x * indicator_fn (m_space m) x) = (\x. 0)`
      by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl,FN_MINUS_POS,fn_minus_def,FUN_EQ_THM]
          ++ METIS_TAC [mul_rzero,mul_rone,extreal_lt_def])
  ++ RW_TAC real_ss [pos_fn_integral_zero]
  ++ `!x. 0 <= (\x. f x * indicator_fn (m_space m) x) x`
      by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
  ++ FULL_SIMP_TAC std_ss [FN_PLUS_POS_ID]);

val integral_pos_simple_fn = store_thm
("integral_pos_simple_fn",``!m f s a x. measure_space m /\ pos_simple_fn m f s a x
                            ==> (integral m f = pos_simple_fn_integral m s a x)``,
  RW_TAC std_ss []
  ++ `!x. 0 <= f x` by METIS_TAC [pos_simple_fn_def]
  ++ RW_TAC std_ss [integral_pos_fn]
  ++ METIS_TAC [pos_fn_integral_pos_simple_fn]);


(* ------------------------------------------------------------------------- *)
(* Properties of Integral                                                    *)
(* ------------------------------------------------------------------------- *)

val integral_indicator = store_thm
("integral_indicator",``!m s. measure_space m /\ s IN measurable_sets m ==>
         (integral m (indicator_fn s) = measure m s)``,
  RW_TAC std_ss []
  ++ `!x. 0 <= indicator_fn s x` by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl,le_01]
  ++ METIS_TAC [pos_fn_integral_indicator,integral_pos_fn]);

val integral_add_lemma = store_thm
  ("integral_add_lemma", ``!m f1 f2. measure_space m /\
        integrable m f1 /\ integrable m f2  /\ (!x. 0 <= f1 x) /\ (!x. 0 <= f2 x)
	==> (integral m (\x. f1 x - f2 x) = pos_fn_integral m f1 -  pos_fn_integral m f2)``,
  RW_TAC std_ss []
  ++ `integrable m (\x. f1 x - f2 x)` by FULL_SIMP_TAC std_ss [integrable_sub]
  ++ Q.ABBREV_TAC `f = \x. f1 x - f2 x`
  ++ `!x. f1 x <> NegInf /\ f2 x <> NegInf` by METIS_TAC [lt_infty,num_not_infty,lte_trans]
 (* ++ Q.ABBREV_TAC `h1 = (\x. fn_plus f x + f2 x)`
  ++ Q.ABBREV_TAC `h2 = (\x. fn_minus f x + f1 x)` *)
  ++ `(\x. fn_plus f x + f2 x) = (\x. fn_minus f x + f1 x)`
      by (RW_TAC std_ss [FUN_EQ_THM,fn_plus_def,fn_minus_def]
	  ++ Cases_on `0 < f1 x - f2 x`
	  >> (RW_TAC std_ss []
              ++ Cases_on `f1 x` ++ Cases_on `f2 x`
	      ++ FULL_SIMP_TAC std_ss [extreal_sub_def,extreal_add_def,extreal_ainv_def,
	      	 	       	       extreal_11,add_lzero,lt_infty,lt_antisym]
	      ++ METIS_TAC [extreal_sub_def,extreal_add_def,add_rzero,extreal_of_num_def,REAL_SUB_ADD,
	      	 	    lt_infty,lt_antisym])
          ++  RW_TAC std_ss [add_lzero]
	  ++ Cases_on `f1 x` ++ Cases_on `f2 x`
	  ++ FULL_SIMP_TAC std_ss [extreal_sub_def,extreal_add_def,extreal_ainv_def,
	      	 	       	       extreal_11,add_lzero,lt_infty,lt_antisym]
          ++ METIS_TAC [extreal_sub_def,extreal_add_def,add_rzero,extreal_of_num_def,REAL_SUB_ADD,
	      	        lt_infty,lt_antisym,add_lzero,extreal_ainv_def,lt_le,REAL_SUB_0,REAL_SUB_SUB2,
                        REAL_ADD_COMM,REAL_LE_ANTISYM,extreal_11,real_sub,extreal_le_def,extreal_lt_def])
  ++ RW_TAC std_ss [integral_def]
  ++ `pos_fn_integral m (fn_plus f) + pos_fn_integral m f2 =
      pos_fn_integral m (fn_minus f) + pos_fn_integral m f1`
        by (RW_TAC std_ss []
	    ++ `pos_fn_integral m (fn_plus f) + pos_fn_integral m f2 =
	        pos_fn_integral m (\x. fn_plus f x + f2 x)`
		    by ((MATCH_MP_TAC o GSYM ) pos_fn_integral_add
		     	++ METIS_TAC [FN_PLUS_POS,integrable_plus_minus])
	    ++ POP_ORW
	    ++ `pos_fn_integral m (fn_minus f) + pos_fn_integral m f1 =
	        pos_fn_integral m (\x. fn_minus f x + f1 x)`
		    by ((MATCH_MP_TAC o GSYM ) pos_fn_integral_add
	                ++ METIS_TAC [FN_MINUS_POS,integrable_plus_minus])
	    ++ POP_ORW
	    ++ RW_TAC std_ss [])
  ++ `!a b c d:real. (a + b = c + d) <=> (a - c = d - b)` by REAL_ARITH_TAC
  ++ FULL_SIMP_TAC std_ss []);

val integral_add = store_thm
  ("integral_add", ``!m f g. measure_space m /\ integrable m f /\ integrable m g
	==> (integral m (\x. f x + g x) = integral m f + integral m g)``,
  RW_TAC std_ss []
  ++ `integrable m (\x. fn_plus f x + fn_plus g x)` by METIS_TAC [integrable_add,integrable_plus_minus]
  ++ `integrable m (\x. fn_minus f x + fn_minus g x)` by METIS_TAC [integrable_add,integrable_plus_minus]
  ++ `!x. 0 <= (\x. fn_plus f x + fn_plus g x) x` by METIS_TAC [le_add,FN_PLUS_POS]
  ++ `!x. 0 <= (\x. fn_minus f x + fn_minus g x) x` by METIS_TAC [le_add,FN_MINUS_POS]
  ++ Suff `(\x. f x + g x) = (\x. (\x. fn_plus f x + fn_plus g x) x - (\x. fn_minus f x + fn_minus g x) x)`
  >> (STRIP_TAC
      ++ POP_ORW
      ++ FULL_SIMP_TAC std_ss [integral_add_lemma]
      ++ `pos_fn_integral m (\x. fn_plus f x + fn_plus g x) =
          pos_fn_integral m (fn_plus f) + pos_fn_integral m (fn_plus g)`
      	   by METIS_TAC [pos_fn_integral_add,integrable_plus_minus,FN_PLUS_POS]
      ++ `pos_fn_integral m (\x. fn_minus f x + fn_minus g x) =
      	  pos_fn_integral m (fn_minus f) + pos_fn_integral m (fn_minus g)`
           by METIS_TAC [pos_fn_integral_add,integrable_plus_minus,FN_MINUS_POS]
      ++ RW_TAC std_ss []
      ++ METIS_TAC [REAL_ADD2_SUB2,integral_def])
  ++ RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
  ++ RW_TAC std_ss [add_rzero,sub_rzero,add_lzero,sub_lzero,lt_antisym]
  ++ Cases_on `f x` ++ Cases_on `g x`
  ++ RW_TAC std_ss [add_rzero,sub_rzero,add_lzero,sub_lzero,lt_antisym,neg_0,neg_neg,lt_infty,extreal_add_def,
     	    	    extreal_sub_def,num_not_infty,add_rzero,sub_rzero,add_lzero,sub_lzero,extreal_ainv_def]
  ++ FULL_SIMP_TAC std_ss [add_rzero,sub_rzero,add_lzero,sub_lzero,lt_antisym,neg_0,neg_neg,lt_infty,
     		   	   extreal_add_def,extreal_sub_def,num_not_infty,add_rzero,sub_rzero,add_lzero,
			   sub_lzero,extreal_ainv_def]
  ++ METIS_TAC [lt_antisym,extreal_lt_def,sub_rneg,le_antisym,add_rzero,add_comm,neg_0,neg_neg,lt_infty,
		num_not_infty,extreal_of_num_def,extreal_le_def,REAL_LE_ANTISYM,REAL_SUB_RNEG,REAL_ADD_RID,
		REAL_ADD_COMM,REAL_NEG_SUB,REAL_NEG_NEG,extreal_11]);

val integral_cmul = store_thm
("integral_cmul",``!m f c. measure_space m /\ integrable m f ==>
         (integral m (\x. Normal c * f x) = c * integral m f)``,
  RW_TAC std_ss [integral_def]
  ++ `integrable m (fn_plus f) /\ integrable m (fn_minus f)` by METIS_TAC [integrable_plus_minus]
  ++ Cases_on `0 <= c`
  >> (RW_TAC std_ss [FN_PLUS_CMUL,FN_MINUS_CMUL]
      ++ METIS_TAC [pos_fn_integral_cmul,FN_PLUS_POS,FN_MINUS_POS,REAL_SUB_LDISTRIB])
  ++ `c <= 0` by METIS_TAC [REAL_LT_IMP_LE,real_lt]
  ++ `0 <= -c` by METIS_TAC [REAL_LE_NEG,REAL_NEG_0]
  ++ RW_TAC std_ss [FN_PLUS_CMUL,FN_MINUS_CMUL,extreal_ainv_def]
  ++ `pos_fn_integral m (\x. Normal (-c) * fn_plus f x) = (-c) * pos_fn_integral m (fn_plus f)`
      by METIS_TAC [pos_fn_integral_cmul,FN_PLUS_POS]
  ++ `pos_fn_integral m (\x. Normal (-c) * fn_minus f x) = (-c) * pos_fn_integral m (fn_minus f)`
      by METIS_TAC [pos_fn_integral_cmul,FN_MINUS_POS]
  ++ METIS_TAC [REAL_SUB_LDISTRIB,REAL_NEG_MUL2,REAL_NEG_SUB,REAL_MUL_LNEG]);

val integral_cmul_indicator = store_thm
("integral_cmul_indicator",``!m s c. measure_space m /\ s IN measurable_sets m ==>
         (integral m (\x. Normal c * indicator_fn s x) = c * measure m s)``,
  METIS_TAC [integral_cmul,integral_indicator,integrable_indicator]);

val integral_pos = store_thm
  ("integral_pos", ``!m f. measure_space m /\  integrable m f /\ (!x. x IN m_space m ==> 0 <= f x)
			==> (0 <= integral m f)``,
  RW_TAC std_ss [integral_pos_fn,pos_fn_integral_pos]);

val integral_zero = store_thm
("integral_zero",``!m. measure_space m ==> (integral m (\x. 0) = 0)``,
  RW_TAC real_ss [integral_pos_fn,pos_fn_integral_zero,le_refl]);

val integral_mspace = store_thm
  ("integral_mspace", ``!m f. measure_space m ==>
   	       (integral m f = integral m (\x. f x * indicator_fn (m_space m) x))``,
  RW_TAC std_ss [integral_def]
  ++ `(fn_plus (\x. f x * indicator_fn (m_space m) x)) = (\x. fn_plus f x * indicator_fn (m_space m) x)`
       by (RW_TAC std_ss [indicator_fn_def,fn_plus_def,FUN_EQ_THM]
	  ++ METIS_TAC [mul_rone,mul_lone,mul_rzero,mul_lzero])
  ++ `fn_minus (\x. f x * indicator_fn (m_space m) x) = (\x. fn_minus f x * indicator_fn (m_space m) x)`
       by (RW_TAC std_ss [indicator_fn_def,fn_minus_def,FUN_EQ_THM]
	  ++ METIS_TAC [neg_0,neg_eq0,mul_rone,mul_lone,mul_rzero,mul_lzero])
  ++ RW_TAC std_ss []
  ++ METIS_TAC [pos_fn_integral_mspace,FN_PLUS_POS,FN_MINUS_POS]);

val integral_mono = store_thm
  ("integral_mono",
   ``!m f1 f2. measure_space m /\ integrable m f1 /\ integrable m f2 /\
              (!t. t IN m_space m ==> f1 t <= f2 t) ==>
   	       (integral m f1 <= integral m f2)``,
  RW_TAC std_ss []
  ++ ONCE_REWRITE_TAC [(UNDISCH o Q.SPECL [`m`,`f`]) integral_mspace]
  ++ RW_TAC std_ss [integral_def]
  ++ `!x. (fn_plus (\x. f1 x * indicator_fn (m_space m) x)) x <=
          (fn_plus (\x. f2 x * indicator_fn (m_space m) x)) x`
       by (RW_TAC real_ss [fn_plus_def,lt_imp_le,le_refl,indicator_fn_def,mul_rzero,mul_rone]
           ++ METIS_TAC [extreal_lt_def,mul_rone,lt_imp_le,le_trans])
  ++ `!x. (fn_minus (\x. f2 x * indicator_fn (m_space m) x)) x <=
          (fn_minus (\x. f1 x * indicator_fn (m_space m) x)) x`
       by (RW_TAC real_ss [fn_minus_def,lt_imp_le,le_refl,indicator_fn_def,mul_rzero,mul_rone,
       	  	  	   neg_0,neg_eq0,le_neg]
           ++ METIS_TAC [mul_rone,extreal_lt_def,le_trans,lt_neg,lt_imp_le,neg_0])
  ++ METIS_TAC [pos_fn_integral_mono,FN_PLUS_POS,FN_MINUS_POS,REAL_LE_NEG,REAL_LE_ADD2,real_sub,
		integrable_plus_minus,integrable_mul_indicator,MEASURE_SPACE_MSPACE_MEASURABLE]);

val integral_disjoint_sets = store_thm
  ("integral_disjoint_sets",``!m f s t. measure_space m /\ DISJOINT s t /\
		integrable m f /\ s IN measurable_sets m /\ t IN measurable_sets m
		==> (integral m (\x. f x * indicator_fn (s UNION t) x) =
		    integral m (\x. f x * indicator_fn s x) + integral m (\x. f x * indicator_fn t x))``,
  RW_TAC std_ss []
  ++ `(\x. f x * indicator_fn (s UNION t) x) =
      (\x. (\x. f x * indicator_fn s x) x + (\x. f x * indicator_fn t x) x)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,mul_rzero,mul_rone,IN_UNION]
           ++ METIS_TAC [IN_DISJOINT,mul_rone,mul_rzero,add_rzero,add_lzero])
  ++ `integrable m (\x. fn_plus f x + fn_minus f x)` by METIS_TAC [integrable_plus_minus,integrable_add]
  ++ `integrable m (\x. f x * indicator_fn s x)`
       by METIS_TAC [integrable_mul_indicator]
  ++ `integrable m (\x. f x * indicator_fn t x)`
       by METIS_TAC [integrable_mul_indicator]
  ++ ASM_SIMP_TAC std_ss []
  ++ METIS_TAC [integral_add]);


val integral_disjoint_sets_sum = store_thm
  ("integral_disjoint_sets_sum",``!m f s a. FINITE s /\measure_space m /\
	(!i. i IN s ==> a i IN measurable_sets m) /\
	(!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
	integrable m f
	==> (integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
	     SIGMA (\i. integral m (\x. f x * indicator_fn (a i) x)) s)``,

  Suff `!s:'b->bool. FINITE s ==> (\s:'b->bool. !m f a. FINITE s /\ measure_space m /\
	(!i. i IN s ==> a i IN measurable_sets m) /\
	(!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
	integrable m f
	==> (integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
	     SIGMA (\i. integral m (\x. f x * indicator_fn (a i) x)) s) ) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM,NOT_IN_EMPTY,FINITE_INSERT,DELETE_NON_ELEMENT,
     	    	     IN_INSERT,BIGUNION_INSERT,IMAGE_INSERT]
  >> RW_TAC real_ss [integral_zero,IMAGE_EMPTY,BIGUNION_EMPTY,indicator_fn_def,NOT_IN_EMPTY,mul_rzero]
  ++ `~(e IN s)` by METIS_TAC [DELETE_NON_ELEMENT]
  ++ `DISJOINT (a e) (BIGUNION (IMAGE a s))`
       by (RW_TAC std_ss [DISJOINT_BIGUNION,IN_IMAGE]
	   ++ METIS_TAC [])
  ++ `countable (IMAGE a s)` by METIS_TAC [COUNTABLE_IMAGE,FINITE_COUNTABLE]
  ++ `(IMAGE a s) SUBSET measurable_sets m`
       by (RW_TAC std_ss [SUBSET_DEF,IMAGE_DEF,GSPECIFICATION]
	   ++ METIS_TAC [])
  ++ `BIGUNION (IMAGE a s) IN measurable_sets m`
	by METIS_TAC [sigma_algebra_def,measure_space_def,subsets_def,measurable_sets_def]
  ++ METIS_TAC [integral_disjoint_sets]);

val integral_split = store_thm
  ("integral_split",``!m f a s. FINITE s /\ measure_space m /\
         (!i:num. i IN s ==> a i IN measurable_sets m) /\
         (!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
	 (BIGUNION (IMAGE a s) = m_space m) /\ integrable m f ==>
	(integral m f = SIGMA (\i. integral m (\x. f x * indicator_fn (a i) x)) s)``,
  RW_TAC std_ss []
  ++ `f IN measurable (m_space m,measurable_sets m) Borel` by FULL_SIMP_TAC std_ss [integrable_def]
  ++ RW_TAC std_ss [Once integral_mspace]
  ++ Q.PAT_ASSUM `BIGUNION (IMAGE a s) = m_space m` (ASSUME_TAC o GSYM)
	++ ASM_SIMP_TAC std_ss []
	++ ASM_SIMP_TAC std_ss []
	++ MATCH_MP_TAC integral_disjoint_sets_sum
	++ RW_TAC std_ss []
  );


val finite_space_integral_reduce = store_thm
  ("finite_space_integral_reduce",
   ``!m f. measure_space m /\ f IN measurable (m_space m, measurable_sets m) Borel /\
      (!x. x IN m_space m ==>  f x <> NegInf /\ f x <> PosInf) /\ FINITE (m_space m)  ==>
		(integral m f = finite_space_integral m f)``,
  REPEAT STRIP_TAC
  ++ `?c1 n. BIJ c1 (count n) (IMAGE f (m_space m))` by RW_TAC std_ss [GSYM FINITE_BIJ_COUNT, IMAGE_FINITE]
  ++ `?c. !i. (i IN count n ==> (c1 i = Normal (c i)))`
       by (Q.EXISTS_TAC `(\i. @r. c1 i = Normal r)`
	   ++ RW_TAC std_ss []
           ++ SELECT_ELIM_TAC
	   ++ RW_TAC std_ss []
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	   ++ `?t. (c1 i = f t) /\ t IN m_space m` by METIS_TAC []
	   ++ METIS_TAC [extreal_cases])
  ++ `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
  ++ `!i j. (i <> j) /\ (i IN count n) /\ (j IN count n) ==> DISJOINT (PREIMAGE f {Normal (c i)})(PREIMAGE f {Normal (c j)})`
        by (RW_TAC std_ss [DISJOINT_DEF,EXTENSION,IN_PREIMAGE,IN_INTER,NOT_IN_EMPTY,IN_SING]
            ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	    ++ METIS_TAC [])
  ++ `!i. PREIMAGE f {Normal (c i)} INTER m_space m IN measurable_sets m`
      by (RW_TAC std_ss []
          ++ `PREIMAGE f {Normal (c i)} = {x | f x = Normal (c i)}` by RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION,IN_SING]
          ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL,integrable_def,space_def,m_space_def,subsets_def,measurable_sets_def])
  ++ `pos_simple_fn m (fn_plus f)
	(count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m) (\i. if 0 <= (c i) then c i else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT,FN_PLUS_POS,FN_MINUS_POS]
   << [REVERSE (RW_TAC real_ss [fn_plus_def])
       >> (FULL_SIMP_TAC std_ss [extreal_lt_def,indicator_fn_def,IN_INTER]
           ++ (MP_TAC o Q.SPEC `(\i. Normal (if 0 <= c i then c i else 0) * if t IN PREIMAGE f {Normal (c i)} then 1 else 0)` o UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IN_IF
	   ++ RW_TAC std_ss []
	   ++ POP_ORW
	   ++ Suff `(\x. if x IN count n then Normal (if 0 <= c x then c x else 0) * if t IN PREIMAGE f {Normal (c x)} then 1 else 0 else 0) = (\x. 0)`
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
	   ++ RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `~(x IN count n)`
	   >> RW_TAC std_ss []
	   ++ REVERSE (RW_TAC std_ss [mul_rone,mul_rzero])
	   >> RW_TAC std_ss [extreal_of_num_def]
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_COUNT,IN_IMAGE,IN_PREIMAGE,IN_SING]
	   ++ METIS_TAC [le_antisym,extreal_le_def,extreal_of_num_def])
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (f t = Normal (c i))` by METIS_TAC []
       ++ `count n = i INSERT ((count n) DELETE i)`
	    by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ REVERSE (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,FINITE_DELETE,GSYM extreal_of_num_def,mul_lzero,DELETE_DELETE,add_lzero])
       >> METIS_TAC [extreal_of_num_def,extreal_lt_eq,lt_antisym,real_lt]
       ++ RW_TAC std_ss [indicator_fn_def,IN_INTER,DELETE_DELETE,mul_rzero,add_lzero,IN_PREIMAGE,IN_SING,mul_rone]
       ++ Suff `SIGMA (\i'. Normal (if 0 <= c i' then c i' else 0) * if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >> RW_TAC std_ss [add_rzero]
       ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       ++ REVERSE (RW_TAC std_ss [FINITE_DELETE,mul_rone,mul_rzero])
       >> RW_TAC std_ss [extreal_of_num_def]
       ++ METIS_TAC [IN_DELETE],
       RW_TAC real_ss [],
       FULL_SIMP_TAC std_ss [DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY,IN_PREIMAGE,EXTENSION,IN_SING]
       ++ METIS_TAC [],
       RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_PREIMAGE,IN_SING,IN_INTER]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF]
       ++ METIS_TAC [IN_IMAGE]])
  ++ `pos_simple_fn m (fn_minus f)
	(count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m) (\i. if c i <= 0 then ~ (c i) else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT,FN_PLUS_POS,FN_MINUS_POS]
   << [REVERSE (RW_TAC real_ss [fn_minus_def])
       >> (FULL_SIMP_TAC std_ss [extreal_lt_def,indicator_fn_def,IN_INTER]
           ++ (MP_TAC o Q.SPEC `(\i. Normal (if c i <= 0 then -c i else 0) * if t IN PREIMAGE f {Normal (c i)} then 1 else 0)` o UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IN_IF
	   ++ RW_TAC std_ss []
	   ++ POP_ORW
	   ++ Suff `(\x. if x IN count n then Normal (if c x <= 0 then -c x else 0) * if t IN PREIMAGE f {Normal (c x)} then 1 else 0 else 0) = (\x. 0)`
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
	   ++ RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `~(x IN count n)`
	   >> RW_TAC std_ss []
	   ++ REVERSE (RW_TAC std_ss [mul_rone,mul_rzero])
	   >> RW_TAC std_ss [extreal_of_num_def]
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_COUNT,IN_IMAGE,IN_PREIMAGE,IN_SING]
	   ++ METIS_TAC [REAL_LE_ANTISYM,extreal_of_num_def,REAL_NEG_0,extreal_le_def,IN_COUNT])
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (f t = Normal (c i))` by METIS_TAC []
       ++ `count n = i INSERT ((count n) DELETE i)`
	    by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ REVERSE (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,FINITE_DELETE,GSYM extreal_of_num_def,mul_lzero,DELETE_DELETE,add_lzero])
       >> METIS_TAC [extreal_lt_eq,real_lt,extreal_of_num_def,lt_antisym]
       ++ RW_TAC std_ss [indicator_fn_def,IN_INTER,DELETE_DELETE,mul_rzero,add_lzero,IN_PREIMAGE,IN_SING,mul_rone]
       ++ Suff `SIGMA (\i'. Normal (if c i' <= 0 then -c i' else 0) * if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >> METIS_TAC [add_rzero,extreal_ainv_def]
       ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       ++ REVERSE (RW_TAC std_ss [FINITE_DELETE,mul_rone,mul_rzero])
       >> RW_TAC std_ss [extreal_of_num_def]
       ++ METIS_TAC [IN_DELETE],
       RW_TAC real_ss [] ++ METIS_TAC [REAL_LE_NEG,REAL_NEG_0],
       FULL_SIMP_TAC std_ss [DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY,IN_PREIMAGE,EXTENSION,IN_SING]
       ++ METIS_TAC [],
       RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_PREIMAGE,IN_SING,IN_INTER]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF]
       ++ METIS_TAC [IN_IMAGE]])
  ++ RW_TAC std_ss [finite_space_integral_def]
  ++ `pos_fn_integral m (fn_plus f) = pos_simple_fn_integral m (count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m) (\i. if 0 <= c i then c i else 0)`
            by METIS_TAC [pos_fn_integral_pos_simple_fn]
  ++ `pos_fn_integral m (fn_minus f) = pos_simple_fn_integral m (count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m) (\i. if c i <= 0 then -c i else 0)`
            by METIS_TAC [pos_fn_integral_pos_simple_fn]
  ++ FULL_SIMP_TAC std_ss [integral_def,pos_simple_fn_integral_def]
  ++ RW_TAC std_ss [GSYM REAL_SUM_IMAGE_SUB,GSYM REAL_SUB_RDISTRIB]
  ++ `!x. ((if 0 <= c x then c x else 0) - if c x <= 0 then -c x else 0) = c x`
      by (RW_TAC real_ss []
          ++ METIS_TAC [REAL_LE_ANTISYM,REAL_ADD_RID,real_lt,REAL_LT_ANTISYM])
  ++ POP_ORW
  ++ (MP_TAC o Q.ISPEC `c1:num->extreal` o UNDISCH o Q.ISPEC `count n` o GSYM) REAL_SUM_IMAGE_IMAGE
  ++ Know `INJ c1 (count n) (IMAGE c1 (count n))`
  >> (FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, IN_IMAGE] ++ METIS_TAC [])
  ++ SIMP_TAC std_ss [] ++ STRIP_TAC ++ STRIP_TAC
  ++ POP_ASSUM (MP_TAC o GSYM o Q.SPEC `(\r. real r * measure m (PREIMAGE f {r} INTER m_space m))`)
  ++ RW_TAC std_ss [o_DEF]
  ++ `(IMAGE c1 (count n)) = (IMAGE f (m_space m))`
     by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_IMAGE]
	 ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	 ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss []
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ METIS_TAC [real_normal]);

val finite_space_POW_integral_reduce = store_thm
  ("finite_space_POW_integral_reduce",
   ``!m f. measure_space m /\ (POW (m_space m) = measurable_sets m) /\ FINITE (m_space m) /\
          (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf) ==>
	  (integral m f = SIGMA (\x. real(f x) * measure m {x}) (m_space m))``,
  RW_TAC std_ss []
  ++ `f IN measurable (m_space m, measurable_sets m) Borel`
        by (RW_TAC std_ss [IN_MEASURABLE_BOREL,IN_FUNSET,IN_UNIV,space_def,subsets_def]
	    >> FULL_SIMP_TAC std_ss [measure_space_def]
	    ++ METIS_TAC [INTER_SUBSET,IN_POW])
  ++ `?c n. BIJ c (count n) (m_space m)` by RW_TAC std_ss [GSYM FINITE_BIJ_COUNT]
  ++ `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
  ++ `?x. !i. (i IN count n ==> (f (c i) = Normal (x i)))`
       by (Q.EXISTS_TAC `(\i. @r. f (c i) = Normal r)`
	   ++ RW_TAC std_ss []
           ++ SELECT_ELIM_TAC
	   ++ RW_TAC std_ss []
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	   ++ METIS_TAC [extreal_cases])
  ++ `!i. i IN count n ==> {c i } IN measurable_sets m` by METIS_TAC [IN_POW,IN_SING,BIJ_DEF,SURJ_DEF,SUBSET_DEF]
  ++ `pos_simple_fn m (fn_plus f)
	(count n) (\i. {c i}) (\i. if 0 <= x i then x i else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT,FN_PLUS_POS,FN_MINUS_POS]
   << [REVERSE (RW_TAC real_ss [fn_plus_def])
       >> (FULL_SIMP_TAC std_ss [extreal_lt_def,indicator_fn_def,IN_INTER]
           ++ RW_TAC std_ss [Once  EXTREAL_SUM_IMAGE_IN_IF]
	   ++ Suff `(\i. if i IN count n then Normal (if 0 <= x i then x i else 0) * if t IN {c i} then 1 else 0 else 0) = \x. 0`
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
	   ++ RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `~(x' IN count n)`
	   >> RW_TAC std_ss []
	   ++ REVERSE (RW_TAC std_ss [mul_rone,mul_rzero])
	   >> RW_TAC std_ss [extreal_of_num_def]
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_COUNT,IN_IMAGE,IN_PREIMAGE,IN_SING]
	   ++ METIS_TAC [le_antisym,extreal_le_def,extreal_of_num_def])
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (t = c i)` by METIS_TAC []
       ++ FULL_SIMP_TAC std_ss []
       ++ `count n = i INSERT ((count n) DELETE i)`
	    by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ REVERSE (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,FINITE_DELETE,GSYM extreal_of_num_def,mul_lzero,DELETE_DELETE,add_lzero])
       >> METIS_TAC [extreal_of_num_def,extreal_lt_eq,lt_antisym,real_lt]
       ++ RW_TAC std_ss [indicator_fn_def,IN_INTER,DELETE_DELETE,mul_rzero,add_lzero,IN_PREIMAGE,IN_SING,mul_rone]
       ++ Suff `SIGMA (\i'. Normal (if 0 <= x i' then x i' else 0) * if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >> RW_TAC std_ss [add_rzero]
       ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       ++ REVERSE (RW_TAC std_ss [FINITE_DELETE,mul_rone,mul_rzero])
       >> RW_TAC std_ss [extreal_of_num_def]
       ++ METIS_TAC [IN_DELETE],
       RW_TAC real_ss [],
       FULL_SIMP_TAC std_ss [DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY,IN_PREIMAGE,EXTENSION,IN_SING,BIJ_DEF,INJ_DEF]
       ++ METIS_TAC [],
       RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_PREIMAGE,IN_SING,IN_INTER]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF]
       ++ METIS_TAC [IN_IMAGE]])
   ++ `pos_simple_fn m (fn_minus f)
	(count n) (\i. {c i}) (\i. if x i <= 0 then -(x i) else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT,FN_MINUS_POS,FN_MINUS_POS]
   << [REVERSE (RW_TAC real_ss [fn_minus_def])
       >> (FULL_SIMP_TAC std_ss [extreal_lt_def,indicator_fn_def,IN_INTER]
           ++ RW_TAC std_ss [Once  EXTREAL_SUM_IMAGE_IN_IF]
	   ++ Suff `(\i. if i IN count n then Normal (if x i <= 0 then -(x i) else 0) * if t IN {c i} then 1 else 0 else 0) = \x. 0`
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
	   ++ RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `~(x' IN count n)`
	   >> RW_TAC std_ss []
	   ++ REVERSE (RW_TAC std_ss [mul_rone,mul_rzero])
	   >> RW_TAC std_ss [extreal_of_num_def]
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_COUNT,IN_SING]
	   ++ METIS_TAC [IN_COUNT,extreal_le_def,extreal_of_num_def,REAL_LE_ANTISYM,REAL_NEG_EQ0])
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (t = c i)` by METIS_TAC []
       ++ FULL_SIMP_TAC std_ss []
       ++ `count n = i INSERT ((count n) DELETE i)`
	    by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ REVERSE (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,FINITE_DELETE,GSYM extreal_of_num_def,mul_lzero,DELETE_DELETE,add_lzero])
       >> METIS_TAC [extreal_of_num_def,extreal_lt_eq,lt_antisym,real_lt]
       ++ RW_TAC std_ss [indicator_fn_def,IN_INTER,DELETE_DELETE,mul_rzero,add_lzero,IN_PREIMAGE,IN_SING,mul_rone]
       ++ Suff `SIGMA (\i'. Normal (if x i' <= 0 then -(x i') else 0) * if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >> RW_TAC std_ss [add_rzero,extreal_ainv_def]
       ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       ++ REVERSE (RW_TAC std_ss [FINITE_DELETE,mul_rone,mul_rzero])
       >> RW_TAC std_ss [extreal_of_num_def]
       ++ METIS_TAC [IN_DELETE],
       METIS_TAC [REAL_LE_REFL,REAL_LE_NEG,REAL_NEG_0],
       FULL_SIMP_TAC std_ss [DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY,IN_PREIMAGE,EXTENSION,IN_SING,BIJ_DEF,INJ_DEF]
       ++ METIS_TAC [],
       RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_PREIMAGE,IN_SING,IN_INTER]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF]
       ++ METIS_TAC [IN_IMAGE]])
  ++ RW_TAC std_ss [integral_def]
  ++ (MP_TAC o Q.SPECL [`m`,`fn_plus f`,`count n`,`(\i. {c i})`,`(\i. if 0 <= x i then x i else 0)`]) pos_fn_integral_pos_simple_fn
  ++ (MP_TAC o Q.SPECL [`m`,`fn_minus f`,`count n`,`(\i. {c i})`,`(\i. if x i <= 0 then -(x i) else 0)`]) pos_fn_integral_pos_simple_fn
  ++ RW_TAC std_ss [pos_simple_fn_integral_def,GSYM REAL_SUM_IMAGE_SUB,GSYM REAL_SUB_RDISTRIB]
  ++ NTAC 4 (POP_ASSUM (K ALL_TAC))
  ++ `!x. ((if 0 <= x i then x i else 0) - if x i <= 0:real then -(x i) else 0) = x i`
      by (RW_TAC real_ss [REAL_SUB_RNEG]
          ++ METIS_TAC [REAL_LE_ANTISYM,REAL_ADD_RID,real_lt,REAL_LT_ANTISYM])
  ++ RW_TAC std_ss []
  ++ (MP_TAC o Q.ISPEC `c:num->'a` o UNDISCH o Q.ISPEC `count n` o GSYM) REAL_SUM_IMAGE_IMAGE
  ++ Know `INJ c (count n) (IMAGE c (count n))`
  >> (FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, IN_IMAGE] ++ METIS_TAC [])
  ++ RW_TAC std_ss []
  ++ POP_ASSUM (MP_TAC o GSYM o Q.SPEC `(\x. real(f x) * measure m {x})`)
  ++ RW_TAC std_ss [o_DEF]
  ++ `(IMAGE c (count n)) = (m_space m)`
	by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_IMAGE]
	    ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	    ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss []
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ METIS_TAC [real_normal]);

val finite_POW_prod_measure_reduce = store_thm
  ("finite_POW_prod_measure_reduce",
   ``!m0 m1. measure_space m0 /\ measure_space m1 /\ FINITE (m_space m0) /\ FINITE (m_space m1) /\
             (POW (m_space m0) = measurable_sets m0) /\ (POW (m_space m1) = measurable_sets m1) ==>
  	     (!a0 a1. a0 IN measurable_sets m0 /\ a1 IN measurable_sets m1
             ==> ((prod_measure m0 m1) (a0 CROSS a1) = measure m0 a0 * measure m1 a1))``,
  RW_TAC std_ss [prod_measure_def, measure_def]
  ++ `!s0 s1 x. PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) SUBSET (m_space m1)`
       by (RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE,IN_CROSS]
           ++ METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF])
  ++ `!x. (\s0. Normal (measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)))) x <> NegInf`
       by METIS_TAC [extreal_not_infty]
  ++ `!x. (\s0. Normal (measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)))) x <> PosInf`
       by METIS_TAC [extreal_not_infty]
  ++ FULL_SIMP_TAC std_ss [finite_space_POW_integral_reduce,real_normal]
  ++ `(m_space m0) = a0 UNION ((m_space m0) DIFF a0)`
	by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_UNION, IN_DIFF]
	    ++ METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF])
  ++ POP_ORW
  ++ `DISJOINT a0 (m_space m0 DIFF a0)`
	by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] ++ DECIDE_TAC)
  ++ `FINITE a0` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_FINITE]
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION, FINITE_DIFF]
  ++ `FINITE (m_space m0 DIFF a0)` by RW_TAC std_ss [FINITE_DIFF]
  ++ ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `(m_space m0 DIFF a0)`) REAL_SUM_IMAGE_IN_IF]
  ++ `(\x. (if x IN m_space m0 DIFF a0 then
            (\s0. measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)) * measure m0 {s0}) x else 0)) = (\x. 0)`
	by (RW_TAC std_ss [FUN_EQ_THM, IN_DIFF]
	    ++ RW_TAC std_ss []
	    ++ `PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) = {}`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [NOT_IN_EMPTY, IN_PREIMAGE, IN_CROSS])
	    ++ RW_TAC real_ss [MEASURE_EMPTY])
  ++ RW_TAC real_ss [REAL_SUM_IMAGE_0]
  ++ ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `a0`) REAL_SUM_IMAGE_IN_IF]
  ++ `(\x. (if x IN a0 then (\s0. measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)) * measure m0 {s0}) x else 0)) =
      (\x. if x IN a0 then (\s0. measure m1 a1 * measure m0 {s0}) x else 0)`
	by (RW_TAC std_ss [FUN_EQ_THM] ++ RW_TAC std_ss []
	    ++ `PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) = a1`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_PREIMAGE, IN_CROSS])
	    ++ RW_TAC std_ss [])
  ++ POP_ORW ++ ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_CMUL]
  ++ Suff `SIGMA (\x. measure m0 {x}) a0 = measure m0 a0`
  >> RW_TAC real_ss [REAL_MUL_COMM]
  ++ MATCH_MP_TAC (GSYM MEASURE_REAL_SUM_IMAGE)
  ++ METIS_TAC [IN_SING, IN_POW, SUBSET_DEF]);

val measure_space_finite_prod_measure_POW1 = store_thm
  ("measure_space_finite_prod_measure_POW1",
   ``!m0 m1. measure_space m0 /\ measure_space m1 /\
	     FINITE (m_space m0) /\ FINITE (m_space m1) /\
	     (POW (m_space m0) = measurable_sets m0) /\
	     (POW (m_space m1) = measurable_sets m1) ==>
	measure_space (prod_measure_space m0 m1)``,
   REPEAT STRIP_TAC
   ++ RW_TAC std_ss [prod_measure_space_def]
   ++ `(m_space m0 CROSS m_space m1,
       subsets
         (sigma (m_space m0 CROSS m_space m1)
            (prod_sets (measurable_sets m0) (measurable_sets m1))),
       prod_measure m0 m1) =
	(space (sigma (m_space m0 CROSS m_space m1)
            (prod_sets (measurable_sets m0) (measurable_sets m1))),
	subsets
         (sigma (m_space m0 CROSS m_space m1)
            (prod_sets (measurable_sets m0) (measurable_sets m1))),
       prod_measure m0 m1)`
	by RW_TAC std_ss [sigma_def, space_def]
   ++ POP_ORW
  ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
  ++ `sigma_algebra (sigma (m_space m0 CROSS m_space m1) (prod_sets (measurable_sets m0) (measurable_sets m1)))`
     by (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
         ++ RW_TAC std_ss [subset_class_def, prod_sets_def, GSPECIFICATION, IN_CROSS]
         ++ (MP_TAC o Q.ISPEC `(x' :('a -> bool) # ('b -> bool))`) pair_CASES
         ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
         ++ RW_TAC std_ss [SUBSET_DEF, IN_CROSS]
         ++ (MP_TAC o Q.ISPEC `(x :('a # 'b))`) pair_CASES
         ++ RW_TAC std_ss []
         ++ FULL_SIMP_TAC std_ss [FST, SND]
         ++ METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF])
  ++ RW_TAC std_ss [m_space_def, SPACE_SIGMA, FINITE_CROSS, measurable_sets_def, SIGMA_REDUCE]
  >> (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
      >> (`{} = {} CROSS {}` by RW_TAC std_ss [CROSS_EMPTY]
          ++ POP_ORW
	  ++ METIS_TAC [finite_POW_prod_measure_reduce,
			 measure_space_def, SIGMA_ALGEBRA, subsets_def, space_def,
			 MEASURE_EMPTY,REAL_MUL_RZERO])
      ++ `!x. (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
	by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	    ++ FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
	    ++ Q.PAT_ASSUM `!s'. P s' ==> s IN s'`
		(MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
	    ++ SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
	    ++ `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
     		POW (m_space m0 CROSS m_space m1)`
		by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
		    ++ (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
       		    ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
		    ++ `x'''' IN q CROSS r` by RW_TAC std_ss []
		    ++ FULL_SIMP_TAC std_ss [IN_CROSS]
		    ++ METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
	    ++ ASM_SIMP_TAC std_ss []
	    ++ RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [SND])
      ++ FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce,
      	 	       	       real_normal,extreal_not_infty]
      ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_LE_MUL
      ++ FULL_SIMP_TAC std_ss [measure_space_def, positive_def]
      ++ METIS_TAC [IN_POW, IN_SING, SUBSET_DEF])
  ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  ++ `!x. (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
	by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	    ++ FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
	    ++ Q.PAT_ASSUM `!s'. P s' ==> s IN s'`
		(MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
	    ++ SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
	    ++ `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
     		POW (m_space m0 CROSS m_space m1)`
		by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
		    ++ (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
       		    ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
		    ++ `x'''' IN q CROSS r` by RW_TAC std_ss []
		    ++ FULL_SIMP_TAC std_ss [IN_CROSS]
		    ++ METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
	    ++ ASM_SIMP_TAC std_ss []
	    ++ RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [SND])
  ++ `!x. (PREIMAGE (\s1. (x,s1)) t) SUBSET m_space m1`
	by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	    ++ FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
	    ++ Q.PAT_ASSUM `!s'. P s' ==> t IN s'`
		(MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
	    ++ SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
	    ++ `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
     		POW (m_space m0 CROSS m_space m1)`
		by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
		    ++ (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
       		    ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
		    ++ `x'''' IN q CROSS r` by RW_TAC std_ss []
		    ++ FULL_SIMP_TAC std_ss [IN_CROSS]
		    ++ METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
	    ++ ASM_SIMP_TAC std_ss []
	    ++ RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [SND])
  ++ `(s UNION t) IN subsets (sigma (m_space m0 CROSS m_space m1) (prod_sets (measurable_sets m0) (measurable_sets m1)))`
          by METIS_TAC [ALGEBRA_UNION,SIGMA_ALGEBRA_SIGMA,sigma_algebra_def]
  ++ `!x. (PREIMAGE (\s1. (x,s1)) (s UNION t)) SUBSET m_space m1`
	by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	    ++ FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
	    ++ Q.PAT_ASSUM `!s'. P s' ==> (s UNION t) IN s'`
		(MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
	    ++ SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
	    ++ `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
     		POW (m_space m0 CROSS m_space m1)`
		by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
		    ++ (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
       		    ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
		    ++ `x'''' IN q CROSS r` by RW_TAC std_ss []
		    ++ FULL_SIMP_TAC std_ss [IN_CROSS]
		    ++ METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
	    ++ ASM_SIMP_TAC std_ss []
	    ++ RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [SND])
  ++ FULL_SIMP_TAC std_ss [extreal_not_infty,prod_measure_def, finite_space_POW_integral_reduce,
       GSYM REAL_SUM_IMAGE_ADD,real_normal,GSYM REAL_ADD_RDISTRIB]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss []
  ++ Suff `measure m1 (PREIMAGE (\s1. (x,s1)) (s UNION t)) =
           measure m1 (PREIMAGE (\s1. (x,s1)) s) + measure m1 (PREIMAGE (\s1. (x,s1)) t)`
  >> RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,	GSPECIFICATION]
  ++ Q.PAT_ASSUM `!s. P s ==> t IN s` (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
  ++ Q.PAT_ASSUM `!ss. P ss ==> s IN s'` (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
  ++ SIMP_TAC std_ss [prod_sets_def, POW_SIGMA_ALGEBRA]
  ++ `{s CROSS t | s IN measurable_sets m0 /\ t IN measurable_sets m1} SUBSET POW (m_space m0 CROSS m_space m1)`
	by (RW_TAC std_ss [Once SUBSET_DEF, GSPECIFICATION, IN_POW]
	    ++ (MP_TAC o Q.ISPEC `(x'' :('a -> bool) # ('b -> bool))`) pair_CASES
       	    ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
	    ++ RW_TAC std_ss [SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
  ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss [IN_POW]
  ++ MATCH_MP_TAC MEASURE_ADDITIVE
  ++ Q.PAT_ASSUM `POW (m_space m1) = measurable_sets m1` (MP_TAC o GSYM)
  ++ Q.PAT_ASSUM `POW (m_space m0) = measurable_sets m0` (MP_TAC o GSYM)
  ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT]
  ++ RW_TAC std_ss []
  << [METIS_TAC [SND],
      METIS_TAC [SND],
      ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_UNION, IN_PREIMAGE]]);

val measure_space_finite_prod_measure_POW2 = store_thm
  ("measure_space_finite_prod_measure_POW2",
   ``!m0 m1. measure_space m0 /\ measure_space m1 /\ FINITE (m_space m0) /\ FINITE (m_space m1) /\
	     (POW (m_space m0) = measurable_sets m0) /\ (POW (m_space m1) = measurable_sets m1) ==>
	measure_space (m_space m0 CROSS m_space m1,
		       POW (m_space m0 CROSS m_space m1),
		       prod_measure m0 m1)``,
   REPEAT STRIP_TAC
   ++ `(m_space m0 CROSS m_space m1, POW (m_space m0 CROSS m_space m1), prod_measure m0 m1) =
	(space (m_space m0 CROSS m_space m1, POW (m_space m0 CROSS m_space m1)),
         subsets (m_space m0 CROSS m_space m1, POW (m_space m0 CROSS m_space m1)), prod_measure m0 m1)`
	by RW_TAC std_ss [space_def, subsets_def]
   ++ POP_ORW
   ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   ++ RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
   >> (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
       >> (`{} = {} CROSS {}` by RW_TAC std_ss [CROSS_EMPTY]
	   ++ POP_ORW
	   ++ METIS_TAC [finite_POW_prod_measure_reduce,
			 measure_space_def, SIGMA_ALGEBRA, subsets_def, space_def,
			 MEASURE_EMPTY, REAL_MUL_LZERO])
       ++ `!x. (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
	by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	    ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [SND])
       ++ FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce,
       	  		        extreal_not_infty,real_normal]
       ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
       ++ RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_LE_MUL
       ++ FULL_SIMP_TAC std_ss [measure_space_def, positive_def]
       ++ METIS_TAC [IN_POW, IN_SING, SUBSET_DEF])
  ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  ++ FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce, extreal_not_infty,real_normal,
     		   	   GSYM REAL_SUM_IMAGE_ADD,GSYM REAL_ADD_RDISTRIB]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss []
  ++ Suff `measure m1 (PREIMAGE (\s1. (x,s1)) (s UNION t)) = (measure m1 (PREIMAGE (\s1. (x,s1)) s) + measure m1 (PREIMAGE (\s1. (x,s1)) t))`
  >> RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,	GSPECIFICATION]
  ++ SIMP_TAC std_ss [prod_sets_def, POW_SIGMA_ALGEBRA]
  ++ `{s CROSS t | s IN measurable_sets m0 /\ t IN measurable_sets m1} SUBSET POW (m_space m0 CROSS m_space m1)`
	by (RW_TAC std_ss [Once SUBSET_DEF, GSPECIFICATION, IN_POW]
	    ++ (MP_TAC o Q.ISPEC `(x'' :('a -> bool) # ('b -> bool))`) pair_CASES
       	    ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
	    ++ RW_TAC std_ss [SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
  ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss [IN_POW]
  ++ MATCH_MP_TAC MEASURE_ADDITIVE
  ++ Q.PAT_ASSUM `POW (m_space m1) = measurable_sets m1` (MP_TAC o GSYM)
  ++ Q.PAT_ASSUM `POW (m_space m0) = measurable_sets m0` (MP_TAC o GSYM)
  ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT]
  ++ RW_TAC std_ss []
  << [METIS_TAC [SND],
      METIS_TAC [SND],
      ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_UNION, IN_PREIMAGE]]);

val finite_prod_measure_space_POW = store_thm
 ("finite_prod_measure_space_POW", ``!s1 s2 u v. FINITE s1 /\ FINITE s2  ==>
          (prod_measure_space (s1, POW s1, u) (s2, POW s2, v) =
          (s1 CROSS s2, POW (s1 CROSS s2), prod_measure (s1, POW s1, u) (s2, POW s2, v)))``,
  RW_TAC std_ss [prod_measure_space_def, m_space_def, subsets_def, EXTENSION, subsets_def, sigma_def,
 	        prod_sets_def, IN_POW, IN_BIGINTER, measurable_sets_def, SUBSET_DEF,
	        IN_CROSS, GSPECIFICATION]
  ++ RW_TAC std_ss [GSYM EXTENSION]
  ++ EQ_TAC
	    >> (RW_TAC std_ss []
	        ++ Q.PAT_ASSUM `!s. P ==> x IN s` (MP_TAC o Q.SPEC `POW (s1 CROSS s2)`)
		++ RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS, POW_SIGMA_ALGEBRA]
		++ Suff `(!x''. (?x'. (x'',T) = (\(s,t). (s CROSS t,
                	(!x. x IN s ==> x IN s1) /\ !x. x IN t ==> x IN s2))
              		x') ==> !x. x IN x'' ==> FST x IN s1 /\ SND x IN s2)` >> METIS_TAC []
		++ RW_TAC std_ss []
		++ Cases_on `x'''`
		++ FULL_SIMP_TAC std_ss []
		++ METIS_TAC [IN_CROSS])
  ++ RW_TAC std_ss []
  ++ `x = BIGUNION (IMAGE (\a. {a}) x)`
    by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
	++ POP_ORW
	++ FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
	++ POP_ASSUM MATCH_MP_TAC
	++ CONJ_TAC
	>> (MATCH_MP_TAC FINITE_COUNTABLE ++ MATCH_MP_TAC IMAGE_FINITE
	    ++ (MP_TAC o Q.ISPEC `(s1 :'a -> bool) CROSS (s2 :'b -> bool)`) SUBSET_FINITE
	    ++ RW_TAC std_ss [FINITE_CROSS]
	    ++ POP_ASSUM MATCH_MP_TAC
	    ++ METIS_TAC [SUBSET_DEF, IN_CROSS])
  ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
  ++ Q.PAT_ASSUM `!x. P ==> x IN s` MATCH_MP_TAC
  ++ Q.EXISTS_TAC `({FST a}, {SND a})` ++ RW_TAC std_ss [PAIR_EQ, IN_SING]
  ++ ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_CROSS, IN_SING]
  ++ METIS_TAC [PAIR_EQ, PAIR, FST, SND]);

val finite_POW_prod_measure_reduce3 = store_thm
  ("finite_POW_prod_measure_reduce3",
   ``!m0 m1 m2. measure_space m0 /\ measure_space m1 /\ measure_space m2 /\
                FINITE (m_space m0) /\ FINITE (m_space m1) /\ FINITE (m_space m2) /\
                (POW (m_space m0) = measurable_sets m0) /\
		(POW (m_space m1) = measurable_sets m1) /\
		(POW (m_space m2) = measurable_sets m2) ==>
  	     (!a0 a1 a2. a0 IN measurable_sets m0 /\ a1 IN measurable_sets m1 /\ a2 IN measurable_sets m2
             ==> ((prod_measure3 m0 m1 m2) (a0 CROSS (a1 CROSS a2)) =
                       measure m0 a0 * measure m1 a1 * measure m2 a2))``,
  RW_TAC std_ss [prod_measure3_def, measure_def]
  ++ `measure_space (prod_measure_space m1 m2)` by METIS_TAC [measure_space_finite_prod_measure_POW1]
  ++ `FINITE (m_space (prod_measure_space m1 m2))` by METIS_TAC [prod_measure_space_def,m_space_def,FINITE_CROSS]
  ++ `m_space (prod_measure_space m1 m2) = m_space m1 CROSS (m_space m2)`
         by RW_TAC std_ss [prod_measure_space_def,m_space_def]
  ++ `measurable_sets (prod_measure_space m1 m2) = POW (m_space m1 CROSS (m_space m2))`
        by (`m1 = (m_space m1,measurable_sets m1,measure m1)` by RW_TAC std_ss [MEASURE_SPACE_REDUCE]
	    ++ `m2 = (m_space m2,measurable_sets m2,measure m2)` by RW_TAC std_ss [MEASURE_SPACE_REDUCE]
	    ++ METIS_TAC [finite_prod_measure_space_POW,m_space_def,measurable_sets_def])
  ++ `a1 CROSS a2 IN measurable_sets (prod_measure_space m1 m2)`
        by (RW_TAC std_ss [IN_POW,SUBSET_DEF,IN_CROSS] ++ METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF])
  ++ RW_TAC std_ss [finite_POW_prod_measure_reduce]
  ++ RW_TAC std_ss [prod_measure_space_def,measure_def]
  ++ METIS_TAC [finite_POW_prod_measure_reduce,REAL_MUL_ASSOC]);

val measure_space_finite_prod_measure_POW3 = store_thm
  ("measure_space_finite_prod_measure_POW3",
   ``!m0 m1 m2. measure_space m0 /\ measure_space m1 /\ measure_space m2 /\
	     FINITE (m_space m0) /\ FINITE (m_space m1) /\ FINITE (m_space m2) /\
	     (POW (m_space m0) = measurable_sets m0) /\
	     (POW (m_space m1) = measurable_sets m1) /\
	     (POW (m_space m2) = measurable_sets m2) ==>
	measure_space (m_space m0 CROSS (m_space m1 CROSS m_space m2),
		       POW (m_space m0 CROSS (m_space m1 CROSS m_space m2)),
		       prod_measure3 m0 m1 m2)``,
   REPEAT STRIP_TAC
   ++ `(m_space m0 CROSS (m_space m1 CROSS m_space m2),
        POW (m_space m0 CROSS (m_space m1 CROSS m_space m2)),
        prod_measure3 m0 m1 m2) =
	(space (m_space m0 CROSS (m_space m1 CROSS m_space m2),
         POW (m_space m0 CROSS (m_space m1 CROSS m_space m2))),
         subsets (m_space m0 CROSS (m_space m1 CROSS m_space m2),
                  POW (m_space m0 CROSS (m_space m1 CROSS m_space m2))),
                  prod_measure3 m0 m1 m2)`
	by RW_TAC std_ss [space_def, subsets_def]
   ++ POP_ORW
   ++ `measure_space (prod_measure_space m1 m2)` by METIS_TAC [measure_space_finite_prod_measure_POW1]
   ++ `prod_measure_space m1 m2 = (m_space m1 CROSS m_space m2,
                                   POW (m_space m1 CROSS m_space m2), prod_measure m1 m2)`
           by METIS_TAC [MEASURE_SPACE_REDUCE,finite_prod_measure_space_POW]
   ++ `!x s. s IN POW (m_space m0 CROSS (m_space m1 CROSS m_space m2)) ==>
           (PREIMAGE (\s1. (x,s1)) s) SUBSET (m_space m1 CROSS (m_space m2))`
	        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	            ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	            ++ METIS_TAC [SND])
  ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
  ++ RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
  >> (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
      >> (`{} = {} CROSS ({} CROSS {})` by RW_TAC std_ss [CROSS_EMPTY]
	  ++ POP_ORW
	  ++ RW_TAC real_ss [finite_POW_prod_measure_reduce3,MEASURE_SPACE_EMPTY_MEASURABLE,MEASURE_EMPTY])
      ++ RW_TAC std_ss [Once prod_measure_def,prod_measure3_def]
      ++ RW_TAC std_ss [finite_space_POW_integral_reduce,real_normal,extreal_not_infty]
      ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_LE_MUL
      ++ METIS_TAC [IN_POW, IN_SING, SUBSET_DEF,MEASURE_SPACE_POSITIVE,positive_def,
      	 	    measurable_sets_def,measure_def])
  ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  ++ RW_TAC std_ss [prod_measure3_def]
  ++ ONCE_REWRITE_TAC [prod_measure_def]
  ++ FULL_SIMP_TAC std_ss [finite_space_POW_integral_reduce, extreal_not_infty, real_normal,
     		   	   GSYM REAL_SUM_IMAGE_ADD, GSYM REAL_ADD_RDISTRIB]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [measure_def]
  ++ `PREIMAGE (\s1. (x,s1)) (s UNION t) = (PREIMAGE (\s1. (x,s1)) s) UNION (PREIMAGE (\s1. (x,s1)) t)`
       by RW_TAC std_ss [EXTENSION,IN_PREIMAGE,IN_UNION]
  ++ POP_ORW
  ++ `DISJOINT (PREIMAGE (\s1. (x,s1)) s) (PREIMAGE (\s1. (x,s1)) t)`
       by (RW_TAC std_ss [DISJOINT_DEF,IN_PREIMAGE,EXTENSION,NOT_IN_EMPTY,IN_INTER]
           ++ METIS_TAC [DISJOINT_DEF,EXTENSION,NOT_IN_EMPTY,IN_INTER])
  ++ METIS_TAC [MEASURE_ADDITIVE,measure_def,measurable_sets_def,IN_POW,m_space_def]);

val finite_prod_measure_space_POW3 = store_thm
 ("finite_prod_measure_space_POW3",``!s1 s2 s3 u v w.
         FINITE s1 /\ FINITE s2 /\ FINITE s3 ==>
         (prod_measure_space3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w) =
          (s1 CROSS (s2 CROSS s3),POW (s1 CROSS (s2 CROSS s3)),
           prod_measure3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w)))``,
  RW_TAC std_ss [prod_measure_space3_def,m_space_def, subsets_def, EXTENSION, subsets_def, sigma_def,
 	        prod_sets3_def, IN_POW, IN_BIGINTER, measurable_sets_def, SUBSET_DEF,
	        IN_CROSS, GSPECIFICATION]
  ++ RW_TAC std_ss [GSYM EXTENSION]
  ++ EQ_TAC
	    >> (RW_TAC std_ss []
	        ++ Q.PAT_ASSUM `!s. P ==> x IN s` (MP_TAC o Q.SPEC `POW (s1 CROSS (s2 CROSS s3))`)
		++ RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS, POW_SIGMA_ALGEBRA]
		++ Suff `(!x''. (?x'. (x'',T) =
                         (\(s,t,u'). (s CROSS (t CROSS u'),
         	           (!x. x IN s ==> x IN s1) /\ (!x. x IN t ==> x IN s2) /\
                	    !x. x IN u' ==> x IN s3)) x') ==>
	                    !x. x IN x'' ==> FST x IN s1 /\ FST (SND x) IN s2 /\ SND (SND x) IN s3)`
		>> METIS_TAC []
		++ RW_TAC std_ss []
		++ Cases_on `x'''` ++ Cases_on `r`
		++ FULL_SIMP_TAC std_ss []
		++ METIS_TAC [IN_CROSS])
  ++ RW_TAC std_ss []
  ++ `x = BIGUNION (IMAGE (\a. {a}) x)`
    by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
	++ POP_ORW
	++ FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
	++ POP_ASSUM MATCH_MP_TAC
	++ CONJ_TAC
	>> (MATCH_MP_TAC FINITE_COUNTABLE ++ MATCH_MP_TAC IMAGE_FINITE
	    ++ (MP_TAC o Q.ISPEC `(s1 :'a -> bool) CROSS ((s2 :'b -> bool) CROSS (s3:'c -> bool))`) SUBSET_FINITE
	    ++ RW_TAC std_ss [FINITE_CROSS]
	    ++ POP_ASSUM MATCH_MP_TAC
	    ++ RW_TAC std_ss [SUBSET_DEF, IN_CROSS])
  ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
  ++ Q.PAT_ASSUM `!x. P ==> x IN s` MATCH_MP_TAC
  ++ Q.EXISTS_TAC `({FST a}, {FST (SND a)}, {SND(SND a)})` ++ RW_TAC std_ss [IN_SING]
  ++ RW_TAC std_ss [IN_SING,EXTENSION,IN_CROSS,PAIR]
  ++ METIS_TAC [PAIR]);


(************************************************************)
(* LEBESGUE MONOTONE CONVERGENCE                            *)
(************************************************************)

val lebesgue_monotone_convergence_lemma = store_thm
  ("lebesgue_monotone_convergence_lemma",
	``!m f g s a x ri r. measure_space m /\ pos_simple_fn m g s a x /\
	(!i. integrable m (fi i)) /\
	(!i x. x IN m_space m ==> 0 <= fi i x) /\
	(!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
	(!i. ri i = pos_fn_integral m (fi i)) /\ (ri --> r) /\
	(!x. x IN m_space m ==> (g x <= f x))
	==> (integral m g <= r)``,
  RW_TAC std_ss []
  ++ `integral m g = SIGMA (\i. x i * measure m (a i)) s`
      by METIS_TAC [integral_pos_simple_fn,pos_simple_fn_integral_def]
  ++ ASM_SIMP_TAC std_ss []
  ++ `(\i. ri i) = ri` by RW_TAC std_ss [FUN_EQ_THM]
  ++ `(\i. ri i) --> r` by RW_TAC std_ss []
  ++ `!i. ri i = integral m (fi i)` by METIS_TAC [integral_pos_fn]
  ++ `!i. ri i = SIGMA (\k. integral m (\x. fi i x * indicator_fn (a k) x)) s`
        by (RW_TAC std_ss []
 	    ++ MATCH_MP_TAC integral_split
	    ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def])
  ++ `FINITE s` by METIS_TAC [pos_simple_fn_def]
  ++ (MP_TAC o UNDISCH o Q.SPEC `s`) (INST_TYPE [alpha |-> ``:num``] SEQ_REAL_SUM_IMAGE)
  ++ RW_TAC std_ss []
  ++ Q.PAT_ASSUM `!i. ri i = integral m (fi i)` (K ALL_TAC)
  ++ FULL_SIMP_TAC std_ss []
  ++ POP_ASSUM (MP_TAC o Q.SPECL [` (\i. (\k. integral m (\x. fi i x * indicator_fn (a k) x)))`,
                                  `(\k. lim (\i. integral m (\x. fi i x * indicator_fn (a k) x)))`])
  ++ REPEAT STRIP_TAC
  ++ FULL_SIMP_TAC std_ss [BETA_THM]
  ++ `(!x. x IN s ==>
              (\n. integral m (\x'. fi n x' * indicator_fn (a x) x')) -->
              lim (\i. integral m (\x'. fi i x' * indicator_fn (a x) x')))`
      by (RW_TAC std_ss [lim]
	  ++ Suff `(\l. (\n. integral m (\x''. fi n x'' * indicator_fn (a x') x'')) --> l)
		   (@l. (\i. integral m (\x''. fi i x'' * indicator_fn (a x') x'')) --> l)`
	  >> METIS_TAC []
	  ++ MATCH_MP_TAC SELECT_ELIM_THM
	  ++ RW_TAC std_ss [GSYM convergent]
	  ++ MATCH_MP_TAC SEQ_ICONV
	  ++ RW_TAC std_ss [SEQ_BOUNDED]
	  >> (Q.EXISTS_TAC `r+1`
	      ++ RW_TAC real_ss []
	      ++ `!i. (!x. x IN m_space m ==> 0 <= (\x''. fi i x'' * indicator_fn (a x') x'') x)`
                   by RW_TAC real_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
	      ++ `!i. 0 <= integral m (\x''. fi i x'' * indicator_fn (a x') x'')`
                   by (RW_TAC std_ss []
		       ++ MATCH_MP_TAC integral_pos
		       ++ RW_TAC std_ss []
		       ++ MATCH_MP_TAC integrable_mul_indicator
		       ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def])
	      ++ `(\i. SIGMA (\k. integral m (\x. fi i x * indicator_fn (a k) x)) s) i <= r`
		   by (MATCH_MP_TAC SEQ_MONO_LE
		       ++ RW_TAC std_ss [GSYM integral_pos_fn]
		       ++ MATCH_MP_TAC integral_mono
		       ++ FULL_SIMP_TAC real_ss [ext_mono_increasing_suc,ADD1])
	      ++ `integral m (\x''. fi i x'' * indicator_fn (a x') x'') <=
			SIGMA (\k. integral m (\x. fi i x * indicator_fn (a k) x)) s`
		   by ((MP_TAC o Q.SPEC `(\k. integral m (\x. fi i x * indicator_fn (a k) x))` o
		        UNDISCH o Q.SPEC `s:num->bool`) (INST_TYPE [alpha |-> ``:num``]
				REAL_SUM_IMAGE_POS_MEM_LE)
			++ RW_TAC std_ss [GSYM integral_pos_fn]
			++ MATCH_MP_TAC integral_mono
			++ RW_TAC std_ss []
			>> METIS_TAC [integrable_mul_indicator,pos_simple_fn_def]
			++ RW_TAC real_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl])
	      ++ `r < r+1` by REAL_ARITH_TAC
	      ++ METIS_TAC [ABS_REFL,REAL_LE_TRANS,REAL_LET_TRANS])
	      ++ ONCE_REWRITE_TAC [real_ge]
	      ++ MATCH_MP_TAC integral_mono
	      ++ `!n x. x IN s ==> integrable m (\x''. fi n x'' * indicator_fn (a x) x'')`
                  by METIS_TAC [integrable_mul_indicator,pos_simple_fn_def]
	      ++ RW_TAC real_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
	      ++ FULL_SIMP_TAC real_ss [real_ge,ext_mono_increasing_def])
  ++ FULL_SIMP_TAC std_ss []
  ++ `r = SIGMA (\k. lim (\i. integral m (\x. fi i x * indicator_fn (a k) x))) s`
	by METIS_TAC [SEQ_UNIQ]
  ++ ASM_SIMP_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`(\i. x i * measure m (a i))`,
                        `(\k. lim (\i. integral m (\x. fi i x * indicator_fn (a k) x)))`] o
      UNDISCH o Q.SPEC `s:num->bool`) (INST_TYPE [alpha |-> ``:num``] REAL_SUM_IMAGE_MONO)
  ++ Suff `(!x'. x' IN s ==> x x' * measure m (a x') <=
           lim (\i. integral m (\x. fi i x * indicator_fn (a x') x)))`
  >> RW_TAC real_ss []
  ++ RW_TAC real_ss []
  ++ MATCH_MP_TAC REAL_LE_MUL_EPSILON
  ++ RW_TAC real_ss []
  ++ Q.ABBREV_TAC `b = (\i. {t | t IN a x' /\ Normal (z * (x x')) <= fi i t})`
  ++ `!n. b n IN measurable_sets m`
       by (Q.UNABBREV_TAC `b`
	   ++ RW_TAC std_ss []
	   ++ Suff `{t | t IN a x' /\ Normal (z * x x') <= fi n t} =
                    (a x') INTER ({t | Normal (z * x x') <= fi n t} INTER (m_space m))`
	   >> (RW_TAC std_ss []
	       ++ `a x' IN measurable_sets m` by METIS_TAC [pos_simple_fn_def]
	       ++ `({t | Normal (z * x x') <= fi n t} INTER m_space m) IN measurable_sets m`
                    by METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE,integrable_def]
	       ++ METIS_TAC [ALGEBRA_INTER,measure_space_def,sigma_algebra_def,subsets_def,
	       	  	     measurable_sets_def,space_def,m_space_def])
	       ++ RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
	       ++ REVERSE EQ_TAC
	       >> RW_TAC std_ss []
	       ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
	       ++ Q.PAT_ASSUM `BIGUNION (IMAGE a s) = m_space m` (MP_TAC o GSYM)
	       ++ RW_TAC std_ss [IN_BIGUNION_IMAGE]
	       ++ METIS_TAC [])
  ++ `a x' = BIGUNION (IMAGE b UNIV)`
	by (Q.UNABBREV_TAC `b`
	    ++ RW_TAC std_ss [GSYM GBIGUNION_IMAGE]
	    ++ RW_TAC std_ss [EXTENSION,GSPECIFICATION]
	    ++ REVERSE EQ_TAC
	    >> RW_TAC std_ss []
	    ++ RW_TAC std_ss []
	    ++ `Normal (x x') = g x''` by METIS_TAC [pos_simple_fn_thm1]
 	    ++ `x'' IN (m_space m)`
		by (FULL_SIMP_TAC std_ss [pos_simple_fn_def]
		    ++ Q.PAT_ASSUM `BIGUNION (IMAGE a s) = m_space m` (MP_TAC o GSYM)
		    ++ RW_TAC std_ss [IN_BIGUNION_IMAGE]
		    ++ METIS_TAC [])
	    ++ `Normal (x x') <= f x''` by METIS_TAC []
	    ++ `sup (IMAGE (\i. fi i x'') univ(:num)) = f x''` by METIS_TAC []
	    ++ Cases_on `x x' = 0`
	    >> RW_TAC real_ss [GSYM extreal_of_num_def]
	    ++ `0 < x x'` by METIS_TAC [REAL_LT_LE,pos_simple_fn_def]
	    ++ `z * x x' <  x x'` by METIS_TAC [REAL_LT_LMUL,REAL_MUL_RID,REAL_MUL_COMM]
	    ++ `Normal (z * x x') < f x''` by METIS_TAC [extreal_lt_eq,lte_trans]
	    ++ `?w. (IMAGE (\i. fi i x'') univ(:num)) w /\ Normal (z * x x') < w` by METIS_TAC [sup_lt]
	    ++ Q.PAT_ASSUM `IMAGE (\i. fi i x'') univ(:num) w`
                   (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	    ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	    ++ METIS_TAC [lt_imp_le])
  ++ `measure m o b --> measure m (a x')`
    by (MATCH_MP_TAC MONOTONE_CONVERGENCE
	++ RW_TAC std_ss [IN_FUNSET,IN_UNIV]
	++ Q.UNABBREV_TAC `b`
	++ RW_TAC std_ss [SUBSET_DEF,EXTENSION,GSPECIFICATION]
	++ `x'' IN m_space m` by METIS_TAC [SUBSET_DEF,pos_simple_fn_def,IN_BIGUNION_IMAGE]
 	++ `fi n x'' <= fi (SUC n) x''` by FULL_SIMP_TAC real_ss [ext_mono_increasing_def,LESS_EQ_SUC_REFL]
	++ METIS_TAC [le_trans,LESS_EQ_SUC_REFL])
  ++ `(\i. (\i. z * (x x')) i * (measure m o b) i ) --> ((z * x x') * (measure m (a x')))`
	by (MATCH_MP_TAC SEQ_MUL ++ RW_TAC std_ss [SEQ_CONST])
  ++ Q.ABBREV_TAC `l = lim (\i. integral m (\x. fi i x * indicator_fn (a x') x))`
  ++ `(\i. integral m (\x. fi i x * indicator_fn (a x') x)) --> l` by METIS_TAC []
  ++ MATCH_MP_TAC SEQ_LE
  ++ Q.EXISTS_TAC `(\i. (\i. z * x x') i * (measure m o b) i)`
  ++ Q.EXISTS_TAC `(\i. integral m (\x. fi i x * indicator_fn (a x') x))`
  ++ Q.PAT_ASSUM `a x' = BIGUNION (IMAGE b UNIV)` (MP_TAC o GSYM)
  ++ RW_TAC std_ss [REAL_MUL_ASSOC]
  >> METIS_TAC []
  ++ Suff `!n. z * x x' * measure m (b n) <= integral m (\x. fi n x * indicator_fn (a x') x)`
  >> RW_TAC std_ss []
  ++ `!n. integrable m (indicator_fn (b n))` by METIS_TAC [indicator_fn_integrable]
  ++ RW_TAC std_ss [GSYM integral_indicator,GSYM integral_cmul]
  ++ MATCH_MP_TAC integral_mono
  ++ `integrable m (\x. fi n x * indicator_fn (a x') x)`
      by METIS_TAC [integrable_mul_indicator,pos_simple_fn_def]
  ++ `integrable m (\x''. Normal (z * x x') * indicator_fn (b n) x'')` by METIS_TAC [integrable_cmul]
  ++ RW_TAC real_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
  >> (Q.UNABBREV_TAC `b`
      ++ FULL_SIMP_TAC std_ss [GSPECIFICATION])
  ++ Q.UNABBREV_TAC `b`
  ++ FULL_SIMP_TAC std_ss [GSPECIFICATION]);

val lebesgue_monotone_convergence = store_thm
  ("lebesgue_monotone_convergence",
	``!m f fi ri r.
          measure_space m /\
	  (!i. integrable m (fi i)) /\ (!i x. x IN m_space m ==> 0 <= fi i x) /\
          (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
          (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = f x)) /\
          (!i. ri i = pos_fn_integral m (fi i)) /\ ri --> r /\
 	  (!i x. x IN m_space m ==> fi i x <= f x) ==>
          integrable m f /\ (r = integral m f)``,
  REPEAT STRIP_TAC
  ++ `integrable m f`
      by (`!x. x IN m_space m ==> 0 <= f x` by METIS_TAC [le_trans]
          ++ RW_TAC std_ss [integrable_pos]
          >> (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
              ++ Q.EXISTS_TAC `fi`
	      ++ FULL_SIMP_TAC std_ss [space_def]
	      ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [measure_space_def]
	      ++ RW_TAC std_ss []
	      >> METIS_TAC [integrable_def]
	      ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_suc])
          ++ RW_TAC std_ss [IN_psfis_eq,GSPECIFICATION]
          ++ Q.EXISTS_TAC `r`
          ++ RW_TAC std_ss []
          ++ `pos_simple_fn_integral m s a x = integral m g` by METIS_TAC [integral_pos_simple_fn]
          ++ POP_ORW
          ++ MATCH_MP_TAC lebesgue_monotone_convergence_lemma
          ++ METIS_TAC [])
  ++ RW_TAC std_ss [GSYM REAL_LE_ANTISYM]
  >> (`!i. ri i <= integral m f`
        by(RW_TAC std_ss [GSYM integral_pos_fn]
   	   ++ MATCH_MP_TAC integral_mono
	   ++ METIS_TAC [REAL_LE_TRANS])
      ++ MATCH_MP_TAC SEQ_LE_IMP_LIM_LE
      ++ METIS_TAC [])
  ++ RW_TAC std_ss [Once integral_mspace]
  ++ `integrable m (\x. f x * indicator_fn (m_space m) x)`
       by METIS_TAC [integrable_mspace]
  ++ `!x. 0 <= (\x. f x * indicator_fn (m_space m) x) x`
        by METIS_TAC [le_trans,indicator_fn_def,mul_rone,mul_rzero,le_refl]
  ++ `?fi ri r.
       (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) =
                                (\x. f x * indicator_fn (m_space m) x) x)) /\
       (!i. ri i IN psfis m (fi i)) /\ ri --> r /\
       (!i x. x IN m_space m ==> fi i x <= (\x. f x * indicator_fn (m_space m) x) x) /\
       (pos_fn_integral m (\x. f x * indicator_fn (m_space m) x) = r)`
         by ((MP_TAC o Q.SPECL [`m`,`(\x. f x * indicator_fn (m_space m) x)`]) integrable_thm_pos
             ++ RW_TAC std_ss [])
  ++ MATCH_MP_TAC SEQ_LE_IMP_LIM_LE
  ++ Q.EXISTS_TAC `ri'`
  ++ FULL_SIMP_TAC std_ss [integral_pos_fn]
  ++ RW_TAC std_ss []
  ++ `ri' n = integral m (fi' n)` by METIS_TAC [IN_psfis_eq,integral_pos_simple_fn,pos_simple_fn_integral_def]
  ++ ASM_SIMP_TAC std_ss []
  ++ MATCH_MP_TAC lebesgue_monotone_convergence_lemma
  ++ `ri' n IN psfis m (fi' n)` by METIS_TAC []
  ++ FULL_SIMP_TAC std_ss [IN_psfis_eq]
  ++ Q.EXISTS_TAC `f`
  ++ Q.EXISTS_TAC `s`
  ++ Q.EXISTS_TAC `a`
  ++ Q.EXISTS_TAC `x`
  ++ Q.EXISTS_TAC `ri`
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]);

val lebesgue_monotone_convergence_subset = store_thm
  ("lebesgue_monotone_convergence_subset", ``!m f fi ri r A.
         measure_space m /\ (!i. integrable m (fi i)) /\ (A IN measurable_sets m) /\
         (!i x. x IN m_space m ==> 0 <= fi i x) /\
         (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
         (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = f x)) /\
         (!i. ri i = pos_fn_integral m ((\x. fi i x * indicator_fn A x))) /\ ri --> r /\
         (!i x. x IN m_space m ==> fi i x <= f x) ==>
         integrable m (\x. f x * indicator_fn A x) /\
	 (r = integral m (\x. f x * indicator_fn A x))``,
  RW_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`(\x. f x * indicator_fn A x)`,`(\i. (\x. fi i x * indicator_fn A x))`,`ri`,`r`])
        lebesgue_monotone_convergence
  ++ `!i. integrable m (\x. fi i x * indicator_fn A x)` by METIS_TAC [integrable_mul_indicator]
  ++ `!i x. x IN m_space m ==> 0 <= fi i x * indicator_fn A x`
       by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
  ++ `!x. x IN m_space m ==> mono_increasing (\i. fi i x * indicator_fn A x)`
        by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
	    ++ RW_TAC std_ss [ext_mono_increasing_def,le_refl])
  ++ `(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x * indicator_fn A x) univ(:num)) =
                               f x * indicator_fn A x))`
        by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
	    ++ Suff `IMAGE (\i. 0) univ(:num) = (\y. y = 0)` >> RW_TAC std_ss [sup_const]
	    ++ RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_UNIV,IN_ABS])
  ++ `!i x. x IN m_space m ==> fi i x * indicator_fn A x <= f x * indicator_fn A x`
        by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
  ++ RW_TAC std_ss []);






(* ------------------------------------------------------------------------- *)
(* More properties of Integral                                               *)
(* ------------------------------------------------------------------------- *)


val pos_fn_integral_suminf = store_thm
("pos_fn_integral_suminf", ``!m f. measure_space m /\ (!i x. x IN m_space m ==> 0 <= f i x) /\
      (!i. integrable m (f i)) /\ summable (\i. pos_fn_integral m (f i)) ==>
      integrable m (\x. suminf (\i. f i x)) /\
      (integral m (\x. suminf (\i. f i x)) = suminf (\i. integral m (f i)))``,
  NTAC 3 STRIP_TAC
  ++ (MATCH_MP_TAC o GSYM) lebesgue_monotone_convergence
  ++ Q.EXISTS_TAC `(\n. (\x. SIGMA (\i. f i x) (count n)))`
  ++ Q.EXISTS_TAC `(\n. sum (0,n) (\i. pos_fn_integral m (f i)))`
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC >> METIS_TAC [integrable_sum,FINITE_COUNT]
  ++ CONJ_TAC >> (RW_TAC std_ss [] ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS ++ METIS_TAC [FINITE_COUNT])
  ++ CONJ_TAC >> (RW_TAC std_ss [ext_mono_increasing_def]
              	  ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
	  	  ++ RW_TAC std_ss [FINITE_COUNT,IN_COUNT,SUBSET_DEF]
	  	  ++ DECIDE_TAC)
  ++ CONJ_TAC >> RW_TAC std_ss [ext_suminf_def]
  ++ CONJ_TAC >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,pos_fn_integral_sum,FINITE_COUNT]
  ++ REVERSE (RW_TAC std_ss [ext_suminf_def,le_sup])
  >> (POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss [summable,suminf]
  ++ SELECT_ELIM_TAC
  ++ RW_TAC std_ss [integral_pos_fn]
  ++ METIS_TAC [sums]);


val pos_fn_integral_suminf_integrable = store_thm
("pos_fn_integral_suminf_integrable", ``!m f. measure_space m /\ (!i x. x IN m_space m ==> 0 <= f i x) /\
      (!i. integrable m (f i)) /\ integrable m (\x. suminf (\i. f i x)) ==>
      (integral m (\x. suminf (\i. f i x)) = suminf (\i. integral m (f i)))``,
  RW_TAC std_ss []
  ++ `!x. x IN m_space m ==> 0 <= (\x. suminf (\i. f i x)) x`
       by (RW_TAC std_ss [ext_suminf_def,le_sup]
       	   ++ POP_ASSUM MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ Q.EXISTS_TAC `0`
	   ++ RW_TAC std_ss [COUNT_ZERO,EXTREAL_SUM_IMAGE_THM])
  ++ (MP_TAC o Q.SPECL [`m`, `(\x. suminf (\i. f i x))`,
     	       	        `(\n. (\x. SIGMA (\i. f i x) (count n)))`,
			`(\n. sum (0,n) (\i. pos_fn_integral m (f i)))`,`suminf (\i. integral m (f i))`])
			   lebesgue_monotone_convergence
  ++ RW_TAC std_ss []
  ++ `!i. integrable m (\x. SIGMA (\i. f i x) (count i))`
       by METIS_TAC [integrable_sum,FINITE_COUNT]
  ++ `!i x. x IN m_space m ==> 0 <= SIGMA (\i. f i x) (count i)`
       by (RW_TAC std_ss []
           ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
	   ++ METIS_TAC [FINITE_COUNT])
  ++ `!x. x IN m_space m ==> mono_increasing (\i. SIGMA (\i. f i x) (count i))`
      by (RW_TAC std_ss [ext_mono_increasing_def]
          ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
	  ++ RW_TAC std_ss [FINITE_COUNT,IN_COUNT,SUBSET_DEF]
	  ++ DECIDE_TAC)
  ++ `!i. sum (0,i) (\i. pos_fn_integral m (f i)) = pos_fn_integral m (\x. SIGMA (\i. f i x) (count i))`
       by (RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
           ++ METIS_TAC [pos_fn_integral_sum,FINITE_COUNT])
  ++ `!x. x IN m_space m ==> (sup (IMAGE (\i. SIGMA (\i. f i x) (count i)) univ(:num)) = suminf (\i. f i x))`
        by RW_TAC std_ss [ext_suminf_def]
  ++ `!i x. x IN m_space m ==>
           SIGMA (\i. f i x) (count i) <= suminf (\i. f i x)`
       by (REWRITE_TAC [ext_suminf_def]
           ++ RW_TAC std_ss [le_sup]
           ++ POP_ASSUM MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
  ++ `(\n. pos_fn_integral m (\x. SIGMA (\i. f i x) (count n))) --> suminf (\i. integral m (f i))`
       by (RW_TAC std_ss [suminf]
           ++ SELECT_ELIM_TAC
	   ++ REVERSE (RW_TAC std_ss [sums,REAL_SUM_IMAGE_EQ_sum])
	   >> FULL_SIMP_TAC std_ss [pos_fn_integral_sum,FINITE_COUNT,GSYM integral_pos_fn]
	   ++ FULL_SIMP_TAC std_ss [integral_pos_fn]
	   ++ `(\n. SIGMA (\i. pos_fn_integral m (f i)) (count n)) =
	       (\n. pos_fn_integral m (\x. SIGMA (\i. f i x) (count n)))`
	       	  by METIS_TAC [pos_fn_integral_sum,FINITE_COUNT]
	   ++ RW_TAC std_ss [GSYM convergent]
	   ++ MATCH_MP_TAC SEQ_ICONV
	   ++ RW_TAC std_ss [SEQ_BOUNDED]
	   >> (Q.EXISTS_TAC `pos_fn_integral m (\x. suminf (\i. f i x)) + 1`
	       ++ RW_TAC std_ss []
	       ++ `0 <= pos_fn_integral m (\x. SIGMA (\i. f i x) (count n))`
	            by FULL_SIMP_TAC std_ss [pos_fn_integral_pos]
	       ++ FULL_SIMP_TAC std_ss [GSYM ABS_REFL]
	       ++ Suff `pos_fn_integral m (\x. SIGMA (\i. f i x) (count n)) <=
	                pos_fn_integral m (\x. suminf (\i. f i x))`
	       >> REAL_ARITH_TAC
	       ++ MATCH_MP_TAC pos_fn_integral_mono
	       ++ RW_TAC std_ss [])
           ++ FULL_SIMP_TAC std_ss [real_ge,GREATER_EQ]
	   ++ MATCH_MP_TAC pos_fn_integral_mono
	   ++ RW_TAC std_ss []
	   ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
	   ++ RW_TAC std_ss [FINITE_COUNT,IN_COUNT,SUBSET_DEF]
	   ++ DECIDE_TAC)
  ++ FULL_SIMP_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Radon Nikodym Theorem                                                     *)
(* ------------------------------------------------------------------------- *)

val EXTREAL_SUP_FUN_SEQ_IMAGE = store_thm
("EXTREAL_SUP_FUN_SEQ_IMAGE", ``!(P:real->bool) (P':('a->extreal)->bool) f.
		(?x. P x) /\ (?z. !x. P x ==> x <= z) /\ (P = IMAGE f P')
  	  	 ==> ?g. (!n:num. g n IN P') /\ (\n. f (g n)) --> sup P``,
  REPEAT STRIP_TAC
  ++ `?y. (!n. y n IN P) /\ (!n. y n <= y (SUC n)) /\ (y --> sup P)` by METIS_TAC [REAL_SUP_SEQ]
  ++ Q.EXISTS_TAC `(\n. @r. (r IN P') /\ (f r  = y n))`
  ++ `(\n. f (@r. r IN P' /\ (f r = y n))) = y` by RW_TAC std_ss [FUN_EQ_THM]
  >> (SELECT_ELIM_TAC
      ++ RW_TAC std_ss []
      ++ METIS_TAC [IN_IMAGE])
  ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss []
  >> (SELECT_ELIM_TAC
      ++ RW_TAC std_ss []
      ++ METIS_TAC [IN_IMAGE]));


val max_fn_seq_def = Define `(max_fn_seq g 0 x  = g 0 x ) /\
	 ((max_fn_seq g (SUC n) x) = max (max_fn_seq g n x) (g (SUC n) x))`;

val max_fn_seq_mono = store_thm
  ("max_fn_seq_mono", ``!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x``,
   RW_TAC std_ss [max_fn_seq_def,extreal_max_def,le_refl]);


val EXTREAL_SUP_FUN_SEQ_MONO_IMAGE = store_thm
  ("EXTREAL_SUP_FUN_SEQ_MONO_IMAGE", ``!(P:real->bool) (P':('a->extreal)->bool).
		(?x. P x) /\ (?z. !x. P x ==> x <= z) /\ (P = IMAGE f P') /\
  	  	(!g1 g2. (g1 IN P' /\ g2 IN P' /\ (!x. g1 x <= g2 x))  ==> f g1 <= f g2) /\
		(!g1 g2. g1 IN P' /\ g2 IN P' ==> (\x. max (g1 x) (g2 x)) IN P')  ==>
              ?g. (!n. g n IN P') /\ (!x n. g n x <= g (SUC n) x) /\ (\n. f (g n)) --> sup P``,
  REPEAT STRIP_TAC
  ++ `?g. (!n:num. g n IN P') /\  (\n. f (g n)) --> sup P` by METIS_TAC [EXTREAL_SUP_FUN_SEQ_IMAGE]
  ++ Q.EXISTS_TAC `max_fn_seq g`
  ++ `!n. max_fn_seq g n IN P'`
      by (Induct
 	  >> (`max_fn_seq g 0 = g 0` by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
	      ++ METIS_TAC [])
	      ++ `max_fn_seq g (SUC n) = (\x. max (max_fn_seq g n x) (g (SUC n) x))` by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
	      ++ RW_TAC std_ss []
	      ++ METIS_TAC [])
  ++ `!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x` by RW_TAC real_ss [max_fn_seq_def,extreal_max_def,le_refl]
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ `!n. (!x. g n x <= max_fn_seq g n x)`
      by (Induct >> RW_TAC std_ss [max_fn_seq_def,le_refl]
	  ++ METIS_TAC [le_max2,max_fn_seq_def])
  ++ `!n. f (g n) <= f (max_fn_seq g n)` by METIS_TAC []
  ++ MATCH_MP_TAC SEQ_SANDWICH
  ++ Q.EXISTS_TAC `(\n. f (g n))`
  ++ Q.EXISTS_TAC `(\n. sup P)`
  ++ RW_TAC std_ss []
  >> METIS_TAC [SEQ_CONST]
  ++ `f (max_fn_seq g n) IN (IMAGE f P')` by METIS_TAC [IN_IMAGE]
  ++ METIS_TAC [REAL_SUP_UBOUND_LE,SPECIFICATION]);


val signed_measure_space_def = Define `
    signed_measure_space m = sigma_algebra (m_space m,measurable_sets m) /\ countably_additive m`;

val negative_set_def = Define `
    negative_set m A = A IN measurable_sets m /\
                      (!s. s IN measurable_sets m /\ s SUBSET A ==> measure m s <= 0)`;


(**********************************************************)
(*  Radon Nikodym Theorem                                 *)
(**********************************************************)

val RADON_F_def = Define `RADON_F m v =
             {f | integrable m f /\ (!x. 0 <= f x) /\
	     !A. A IN measurable_sets m ==> (pos_fn_integral m (\x. f x * indicator_fn A x) <= measure v A)}`;

val RADON_F_integrals_def = Define `
	RADON_F_integrals m v = {r | ?f. (r = pos_fn_integral m f) /\ f IN RADON_F m v}`;

val measure_absolutely_continuous_def = Define `
	measure_absolutely_continuous m v =
               (!A. A IN measurable_sets m /\ (measure v A = 0) ==> (measure m A = 0))`;

val lemma_radon_max_in_F = store_thm
  ("lemma_radon_max_in_F",``!f g m v. (measure_space m /\ measure_space v /\
	(m_space v = m_space m) /\ (measurable_sets v = measurable_sets m) /\
        f IN RADON_F m v /\ g IN RADON_F m v)
	     ==> (\x. max (f x) (g x)) IN RADON_F m v``,
    RW_TAC real_ss [RADON_F_def,GSPECIFICATION,REAL_MAX_LE,REAL_LE_MAX,le_max,max_le]
    >> FULL_SIMP_TAC std_ss [integrable_max]
    ++ Q.ABBREV_TAC `A1 = {x | x IN A /\ g x < f x}`
    ++ Q.ABBREV_TAC `A2 = {x | x IN A /\ f x <= g x}`
    ++ `DISJOINT A1 A2`
         by (Q.UNABBREV_TAC `A1` ++ Q.UNABBREV_TAC `A2`
	   ++ RW_TAC std_ss [IN_DISJOINT,GSPECIFICATION]
	   ++ METIS_TAC [extreal_lt_def])
   ++ `A1 UNION A2 = A`
       by (Q.UNABBREV_TAC `A1` ++ Q.UNABBREV_TAC `A2`
	   ++ RW_TAC std_ss [IN_UNION,EXTENSION,GSPECIFICATION]
	   ++ METIS_TAC [extreal_lt_def])
   ++ `(\x. max (f x) (g x) * indicator_fn A x) =
	   (\x. (\x. max (f x) (g x) * indicator_fn A1 x) x +
	   (\x. max (f x) (g x) * indicator_fn A2 x) x)`
       by (Q.UNABBREV_TAC `A1` ++ Q.UNABBREV_TAC `A2`
	   ++ RW_TAC std_ss [indicator_fn_def,GSPECIFICATION,FUN_EQ_THM]
	   ++ Cases_on `g x < f x`
	   >> (RW_TAC std_ss [mul_rone,mul_rzero,add_rzero] ++ METIS_TAC [extreal_lt_def])
	   ++ RW_TAC real_ss [mul_rone,mul_rzero,add_lzero] ++ METIS_TAC [extreal_lt_def])
   ++ `additive v` by METIS_TAC [measure_space_def,sigma_algebra_def,COUNTABLY_ADDITIVE_ADDITIVE]
   ++ `A SUBSET m_space m` by RW_TAC std_ss [MEASURE_SPACE_SUBSET_MSPACE]
   ++ `A1 = ({x | g x < f x} INTER m_space m) INTER A`
       by (Q.UNABBREV_TAC `A1`
           ++ RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION,CONJ_SYM]
	   ++ METIS_TAC [SUBSET_DEF])
   ++ `A2 = ({x | f x <= g x} INTER m_space m) INTER A`
       by (Q.UNABBREV_TAC `A2`
           ++ RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION,CONJ_SYM]
	   ++ METIS_TAC [SUBSET_DEF])
   ++ `A1 IN measurable_sets m`
       by (ASM_SIMP_TAC std_ss []
	   ++ MATCH_MP_TAC MEASURE_SPACE_INTER
	   ++ RW_TAC std_ss []
	   ++ METIS_TAC [IN_MEASURABLE_BOREL_LT,m_space_def,space_def,subsets_def,
                         measurable_sets_def,integrable_def])
   ++ `A2 IN measurable_sets m`
       by (ASM_SIMP_TAC std_ss []
	   ++ MATCH_MP_TAC MEASURE_SPACE_INTER
	   ++ RW_TAC std_ss []
	   ++ METIS_TAC [IN_MEASURABLE_BOREL_LE,m_space_def,space_def,subsets_def,
                         measurable_sets_def,integrable_def])
   ++ `measure v A = measure v A1 + measure v A2` by METIS_TAC [ADDITIVE]
   ++ Q.PAT_ASSUM `A1 = M` (K ALL_TAC)
   ++ Q.PAT_ASSUM `A2 = M` (K ALL_TAC)
   ++ `!x. max (f x) (g x) * indicator_fn A1 x = f x * indicator_fn A1 x`
       by (Q.UNABBREV_TAC `A1`
	   ++ RW_TAC std_ss [extreal_max_def,indicator_fn_def,GSPECIFICATION,mul_rone,mul_rzero]
	   ++ METIS_TAC [extreal_lt_def])
   ++ `!x. max (f x) (g x) * indicator_fn A2 x = g x * indicator_fn A2 x`
       by (Q.UNABBREV_TAC `A2`
	   ++ RW_TAC std_ss [extreal_max_def,indicator_fn_def,GSPECIFICATION,mul_rone,mul_rzero]
	   ++ METIS_TAC [extreal_lt_def])
   ++ ASM_SIMP_TAC std_ss []
   ++ `integrable m (\x. f x * indicator_fn A1 x)` by METIS_TAC [integrable_mul_indicator]
   ++ `integrable m (\x. g x * indicator_fn A2 x)`  by METIS_TAC [integrable_mul_indicator]
   ++ `!x. 0 <= (\x. f x * indicator_fn A1 x) x`
       by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_01,le_refl]
   ++ `!x. 0 <= (\x. g x * indicator_fn A2 x) x`
       by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_01,le_refl]
   ++ FULL_SIMP_TAC std_ss [REAL_LE_ADD2,pos_fn_integral_add]);

val lemma_radon_seq_conv_sup = store_thm
  ("lemma_radon_seq_conv_sup",``!f m v. (measure_space m /\ measure_space v /\
     (m_space v = m_space m) /\ (measurable_sets v = measurable_sets m)) ==>
	?f_n. (!n. f_n n IN RADON_F m v) /\ (!x n. f_n n x <= f_n (SUC n) x) /\
	 ((\n. pos_fn_integral m (f_n n)) --> sup (RADON_F_integrals m v))``,
    RW_TAC std_ss [RADON_F_integrals_def]
    ++ MATCH_MP_TAC EXTREAL_SUP_FUN_SEQ_MONO_IMAGE
    ++ CONJ_TAC
    >> (Q.EXISTS_TAC `0`
	++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	++ RW_TAC std_ss [GSPECIFICATION]
	++ Q.EXISTS_TAC `(\x. 0)`
	++ RW_TAC real_ss [RADON_F_def,GSPECIFICATION,pos_fn_integral_zero,mul_lzero,le_refl]
	>> METIS_TAC [integrable_const,extreal_of_num_def]
	++ METIS_TAC [measure_space_def,positive_def])
    ++ CONJ_TAC
    >> (Q.EXISTS_TAC `measure v (m_space v)`
	++ RW_TAC std_ss []
	++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	++ RW_TAC std_ss [GSPECIFICATION,RADON_F_def]
	++ POP_ASSUM (MP_TAC o Q.SPEC `m_space m`)
	++ RW_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE, GSYM pos_fn_integral_mspace])
    ++ CONJ_TAC
    >> RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_IMAGE,RADON_F_def]
    ++ CONJ_TAC
    >> RW_TAC std_ss [RADON_F_def,GSPECIFICATION,pos_fn_integral_mono]
    ++ RW_TAC std_ss [lemma_radon_max_in_F]);

val RN_lemma1 = store_thm
("RN_lemma1",``!m v e. measure_space m /\ measure_space v /\ 0 < e /\
                       (m_space v = m_space m) /\ (measurable_sets v = measurable_sets m) ==>
              (?A. A IN measurable_sets m /\
               measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
               !B. B IN measurable_sets m /\ B SUBSET A ==> -e < measure m B - measure v B)``,
  RW_TAC std_ss []
  ++ Q.ABBREV_TAC `d = (\A. measure m A - measure v A)`
  ++ Q.ABBREV_TAC `h = (\A. if (!B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF A) ==> -e < d B)
                            then {}
                            else
                              @B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF A) /\ d B <= -e )`
  ++ `!A. A IN measurable_sets m ==> h A  IN measurable_sets m`
        by (RW_TAC std_ss []
	    ++ METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE,real_lte])
  ++ Q.ABBREV_TAC `A = SIMP_REC {} (\a. a UNION h a)`
  ++ `A 0 = {}` by METIS_TAC [SIMP_REC_THM]
  ++ `!n. A (SUC n) = (A n) UNION (h (A n))` by (Q.UNABBREV_TAC `A` ++ RW_TAC std_ss [SIMP_REC_THM])
  ++ `!n. A n IN measurable_sets m`
        by (Induct >> RW_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE]
	    ++ RW_TAC std_ss [MEASURE_SPACE_UNION])
  ++ `!n. (?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e) ==>
               d (A (SUC n)) <= d (A n) - e`
       by (RW_TAC std_ss []
           ++ `~(!B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) ==> -e < d B)`
                 by METIS_TAC [real_lte]
           ++ `h (A n) = (@B. B IN measurable_sets m /\ B SUBSET m_space m DIFF (A n) /\ d B <= -e)`
                by (Q.UNABBREV_TAC `h` ++ RW_TAC std_ss [])
           ++ POP_ORW
	   ++ SELECT_ELIM_TAC
	   ++ RW_TAC std_ss []
	   >> METIS_TAC []
           ++ `DISJOINT (A n) x`
               by (RW_TAC std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
                   ++ METIS_TAC [SUBSET_DEF,IN_DIFF])
           ++ `d ((A n) UNION x) = d (A n) + d x`
                 by (Q.UNABBREV_TAC `d`
                     ++ RW_TAC std_ss []
		     ++ `measure m (A n UNION x) = measure m (A n) + measure m x`
                           by (MATCH_MP_TAC ADDITIVE
                               ++ FULL_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE])
		     ++ `measure v (A n UNION x) = measure v (A n) + measure v x`
                           by (MATCH_MP_TAC ADDITIVE
                               ++ FULL_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE])
		     ++ POP_ORW ++ POP_ORW
		     ++ REAL_ARITH_TAC)
          ++ POP_ORW
	  ++ METIS_TAC [REAL_LE_LADD,real_sub])
  ++ `!n. d (A (SUC n)) <= d (A n)`
        by (RW_TAC std_ss []
            ++ Cases_on `(?B. B IN measurable_sets m /\ B SUBSET m_space m DIFF A n /\ d B <= -e)`
            >> (`d (A n) <= d (A n) + e` by METIS_TAC [REAL_LT_IMP_LE,REAL_LE_ADDR]
		++ `d (A n) - e <= d (A n)` by METIS_TAC [REAL_LE_SUB_RADD]
		++ METIS_TAC [REAL_LE_TRANS])
	    ++ `!B. B IN measurable_sets m /\ B SUBSET m_space m DIFF A n ==> -e < d B` by METIS_TAC [real_lte]
	    ++ METIS_TAC [UNION_EMPTY,REAL_LE_REFL])
  ++ Cases_on `?n. !B. ((B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n))) ==> -e < d B)`
  >> (Q.PAT_ASSUM `!n. A (SUC n) = a UNION b` (K ALL_TAC)
      ++ FULL_SIMP_TAC std_ss []
      ++ `!n. m_space m DIFF (A n) IN measurable_sets m`
            by METIS_TAC [MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE]
      ++ Suff `!n. d (m_space m) <= d (m_space m DIFF (A n))`
      >> METIS_TAC []
      ++ Induct
      >> RW_TAC std_ss [DIFF_EMPTY,REAL_LE_REFL]
      ++ `measure m (m_space m DIFF A (SUC n')) = measure m (m_space m) - measure m (A (SUC n'))`
           by METIS_TAC [MEASURE_COMPL]
      ++ `measure v (m_space m DIFF A (SUC n')) = measure v (m_space m) - measure v (A (SUC n'))`
           by METIS_TAC [MEASURE_COMPL]
      ++ `measure m (m_space m DIFF A n') = measure m (m_space m) - measure m (A n')`
           by METIS_TAC [MEASURE_COMPL]
      ++ `measure v (m_space m DIFF A n') = measure v (m_space m) - measure v (A n')`
           by METIS_TAC [MEASURE_COMPL]
      ++ `d (m_space m DIFF A n') = d (m_space m) - d (A n')`
             by (Q.UNABBREV_TAC `d`
                 ++ FULL_SIMP_TAC std_ss []
		 ++ REAL_ARITH_TAC)
      ++ `d (m_space m DIFF A (SUC n')) = d (m_space m) - d (A (SUC n'))`
             by (Q.UNABBREV_TAC `d`
                 ++ FULL_SIMP_TAC std_ss []
		 ++ REAL_ARITH_TAC)
      ++ FULL_SIMP_TAC std_ss []
      ++ `d (m_space m) - d (A n') <= d (m_space m) - d (A (SUC n'))`
           by METIS_TAC [real_sub,MEASURE_SPACE_MSPACE_MEASURABLE,REAL_LE_LADD,REAL_LE_NEG]
      ++ METIS_TAC [REAL_LE_TRANS])
  ++ `!n. ?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e`
        by METIS_TAC [real_lte]
  ++ `!n. d (A n) <= - &n * e`
       by (Induct
           >> METIS_TAC [REAL_MUL_LZERO,REAL_NEG_0,REAL_LE_REFL,MEASURE_EMPTY,measure_def,REAL_SUB_RZERO]
           ++ `d (A (SUC n)) <= d (A n) - e` by METIS_TAC []
	   ++ RW_TAC std_ss [ADD1,GSYM REAL_ADD,REAL_NEG_ADD,REAL_ADD_RDISTRIB,GSYM REAL_NEG_MINUS1]
	   ++ `d (A n) + -e <= -&n * e + -e` by METIS_TAC [REAL_LE_ADD2,REAL_LE_REFL]
	   ++ METIS_TAC [real_sub,REAL_LE_TRANS])
  ++ `!n. - d (A n) <= - d (A (SUC n))` by METIS_TAC [REAL_LE_NEG]
  ++ `!n. A n SUBSET A (SUC n)` by METIS_TAC [SUBSET_UNION]
  ++ `measure m o A --> measure m (BIGUNION (IMAGE A univ(:num)))`
       by METIS_TAC [MONOTONE_CONVERGENCE2,IN_FUNSET,IN_UNIV,measure_def,measurable_sets_def]
  ++ `measure v o A --> measure v (BIGUNION (IMAGE A univ(:num)))`
       by METIS_TAC [MONOTONE_CONVERGENCE2,IN_FUNSET,IN_UNIV,measure_def,measurable_sets_def]
  ++ FULL_SIMP_TAC std_ss [o_DEF]
  ++ `BIGUNION (IMAGE A UNIV) IN measurable_sets m`
      by METIS_TAC [SIGMA_ALGEBRA_ENUM,measure_space_def,subsets_def,measurable_sets_def,IN_FUNSET,IN_UNIV]
  ++ `!n. -d (A n) = measure v (A n) - measure m (A n)`
        by (Q.UNABBREV_TAC `d`
            ++ RW_TAC std_ss [REAL_NEG_SUB])
  ++ Q.ABBREV_TAC `r = (\n. measure v (A n) - measure m (A n))`
  ++ Q.ABBREV_TAC `l1 = measure m (BIGUNION (IMAGE A UNIV))`
  ++ Q.ABBREV_TAC `l2 = measure v (BIGUNION (IMAGE A UNIV))`
  ++ `r --> (l2 - l1)`
      by (Q.UNABBREV_TAC `r` ++ Q.UNABBREV_TAC `l2` ++ Q.UNABBREV_TAC `l1` ++ METIS_TAC [SEQ_SUB])
  ++ `mono_increasing r` by METIS_TAC [mono_increasing_suc]
  ++ `?n. - d (BIGUNION (IMAGE A UNIV)) < &n * e` by METIS_TAC [REAL_ARCH]
  ++ `&n * e <= -d (A n)` by METIS_TAC [REAL_LE_NEG,REAL_NEG_NEG,REAL_MUL_LNEG]
  ++ `-d (BIGUNION (IMAGE A univ(:num))) < -d (A n)` by METIS_TAC [REAL_LTE_TRANS]
  ++ `-d (A n) <= - d (BIGUNION (IMAGE A UNIV))`
       by (RW_TAC std_ss []
           ++ Q.UNABBREV_TAC `d`
	   ++ FULL_SIMP_TAC std_ss []
	   ++ Suff `r n <= l2 - l1`
	   >> METIS_TAC [REAL_NEG_SUB]
	   ++ MATCH_MP_TAC SEQ_MONO_LE
	   ++ METIS_TAC [mono_increasing_suc,ADD1])
  ++ METIS_TAC [real_lte]);

val RN_lemma2 = store_thm
("RN_lemma2",``!m v. measure_space m /\ measure_space v /\
         (m_space v = m_space m) /\
         (measurable_sets v = measurable_sets m) ==>
         (?A. A IN measurable_sets m /\
          measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
         !B. B IN measurable_sets m /\ B SUBSET A ==> 0 <= measure m B - measure v B)``,
  RW_TAC std_ss []
  ++ Q.ABBREV_TAC `d = (\a. measure m a - measure v a)`
  ++ Q.ABBREV_TAC `p = (\a b n. a IN measurable_sets m /\ a SUBSET b /\ d b <= d a /\ (!c. c IN measurable_sets m /\ c SUBSET a ==> -((1 / 2) pow n) < d c))`
  ++ Q.ABBREV_TAC `sts = (\s. IMAGE (\A. s INTER A) (measurable_sets m))`
  ++ `!s t. s IN measurable_sets m /\ t IN sts s ==> t IN measurable_sets m`
        by (RW_TAC std_ss []
            ++ Q.UNABBREV_TAC `sts`
	    ++ FULL_SIMP_TAC std_ss [IN_IMAGE,MEASURE_SPACE_INTER])
  ++ `!s t. t IN sts s ==> t SUBSET s`
        by (RW_TAC std_ss []
            ++ Q.UNABBREV_TAC `sts`
	    ++ FULL_SIMP_TAC std_ss [IN_IMAGE,INTER_SUBSET])
  ++ `!s. s IN measurable_sets m ==> measure_space (s, sts s, measure m)`
      by METIS_TAC [MEASURE_SPACE_RESTRICTED]
  ++ `!s. s IN measurable_sets m ==> measure_space (s, sts s, measure v)`
      by METIS_TAC [MEASURE_SPACE_RESTRICTED]
  ++ `!n. 0:real < (1 / 2) pow n` by METIS_TAC [POW_HALF_POS]
  ++ `!s n. s IN measurable_sets m ==> ?A. p A s n`
         by (RW_TAC std_ss []
             ++ `?A. A IN (sts s) /\ measure m s - measure v s <= measure m A - measure v A /\
                (!B. B IN (sts s) /\ B SUBSET A ==>  -((1 / 2) pow n) < measure m B - measure v B)`
                 by (RW_TAC std_ss []
                     ++ (MP_TAC o Q.SPECL [`(s,sts s,measure m)`,`(s,sts s,measure v)`,`(1 / 2) pow n`]) RN_lemma1
	             ++ RW_TAC std_ss [m_space_def,measure_def,measurable_sets_def])
	     ++ Q.EXISTS_TAC `A`
	     ++ Q.UNABBREV_TAC `p`
	     ++ FULL_SIMP_TAC std_ss []
             ++ RW_TAC std_ss []
	     << [METIS_TAC [],METIS_TAC [],
                 `A SUBSET s` by METIS_TAC []
		 ++ Suff `c IN sts s`
		 >> METIS_TAC []
                 ++ Q.UNABBREV_TAC `sts`
		 ++ FULL_SIMP_TAC std_ss [IN_IMAGE]
		 ++ Q.EXISTS_TAC `c`
		 ++ METIS_TAC [SUBSET_INTER2,SUBSET_TRANS]])
  ++ Q.ABBREV_TAC `A = PRIM_REC (m_space m) (\a n. @b. p b a n)`
  ++ `A 0 = m_space m` by METIS_TAC [PRIM_REC_THM]
  ++ `!n. A (SUC n) = @b. p b (A n) n`
        by (Q.UNABBREV_TAC `A` ++ RW_TAC std_ss [PRIM_REC_THM])
  ++ `!n. A n IN measurable_sets m`
       by (Induct >> METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]
           ++ RW_TAC std_ss []
	   ++ SELECT_ELIM_TAC
	   ++ FULL_SIMP_TAC std_ss []
 	   ++ METIS_TAC [])
  ++ `!n. p (A (SUC n)) (A n) n` by METIS_TAC []
  ++ `!n. A (SUC n) SUBSET (A n)` by METIS_TAC []
  ++ `!n. d (A n) <= d (A (SUC n))` by METIS_TAC []
  ++ `!n c. (c IN measurable_sets m /\ c SUBSET (A (SUC n)) ==> -((1 / 2) pow n) < d c)` by METIS_TAC []
  ++ Q.EXISTS_TAC `BIGINTER (IMAGE A UNIV)`
  ++ CONJ_TAC
  >> METIS_TAC [SIGMA_ALGEBRA_FN_BIGINTER,IN_UNIV,IN_FUNSET,subsets_def,measurable_sets_def,measure_space_def]
  ++ REVERSE CONJ_TAC
  >> (RW_TAC std_ss []
      ++ SPOSE_NOT_THEN ASSUME_TAC
      ++ FULL_SIMP_TAC std_ss [GSYM real_lt]
      ++ `0 < - (measure m B - measure v B)` by METIS_TAC [REAL_LT_NEG,REAL_NEG_0]
      ++ `?n. measure m B - measure v B < -((1 / 2) pow n)`
           by METIS_TAC [POW_HALF_SMALL,REAL_LT_NEG,REAL_NEG_NEG]
      ++ `d B < -((1 / 2) pow n)` by METIS_TAC []
      ++ `!n. B SUBSET A n` by METIS_TAC [SUBSET_BIGINTER,IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [REAL_LT_ANTISYM])
  ++ `measure m o A --> measure m (BIGINTER (IMAGE A UNIV))`
        by (MATCH_MP_TAC (GSYM MONOTONE_CONVERGENCE_BIGINTER2)
            ++ RW_TAC std_ss [IN_UNIV,IN_FUNSET])
  ++ `measure v o A --> measure v (BIGINTER (IMAGE A UNIV))`
        by (MATCH_MP_TAC (GSYM MONOTONE_CONVERGENCE_BIGINTER2)
            ++ RW_TAC std_ss [IN_UNIV,IN_FUNSET])
  ++ `BIGINTER (IMAGE A UNIV) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_BIGINTER]
  ++ FULL_SIMP_TAC std_ss [o_DEF]
  ++ Q.ABBREV_TAC `r = (\n. measure v (A n) - measure m (A n))`
  ++ Q.ABBREV_TAC `l1 = measure m (BIGINTER (IMAGE A UNIV))`
  ++ Q.ABBREV_TAC `l2 = measure v (BIGINTER (IMAGE A UNIV))`
  ++ `r --> (l2 - l1)`
      by (Q.UNABBREV_TAC `r` ++ Q.UNABBREV_TAC `l2` ++ Q.UNABBREV_TAC `l1` ++ METIS_TAC [SEQ_SUB])
  ++ `!n. r n = -d (A n)` by METIS_TAC [REAL_NEG_SUB]
  ++ `mono_decreasing r` by METIS_TAC [mono_decreasing_suc,REAL_LE_NEG,REAL_NEG_NEG]
  ++ `l2 - l1 <= r 0` by (MATCH_MP_TAC SEQ_LE_MONO ++ METIS_TAC [mono_decreasing_suc,ADD1])
  ++ Q.UNABBREV_TAC `r`
  ++ FULL_SIMP_TAC std_ss []
  ++ METIS_TAC [REAL_NEG_SUB,REAL_LE_NEG]);


val Radon_Nikodym = store_thm
  ("Radon_Nikodym",``!m v. measure_space m /\ measure_space v /\ (m_space v = m_space m) /\
         (measurable_sets v = measurable_sets m) /\
          measure_absolutely_continuous v m
            ==> (?f. integrable m f /\ (!x. 0 <= f x) /\
                (!A. A IN measurable_sets m ==>
                      (pos_fn_integral m (\x. f x * indicator_fn A x) = measure v A)))``,
  RW_TAC std_ss []
  ++ `?f_n. (!n. f_n n IN RADON_F m v) /\ (!x n. f_n n x <= f_n (SUC n) x) /\
            (\n. pos_fn_integral m (f_n n)) --> sup (RADON_F_integrals m v)`
       by RW_TAC std_ss [lemma_radon_seq_conv_sup]
  ++ Q.ABBREV_TAC `g = (\x. sup (IMAGE (\n. f_n n x) UNIV))`
  ++ Q.EXISTS_TAC `g`
  ++ `!x. 0 <= g x`
       by (Q.UNABBREV_TAC `g`
           ++ RW_TAC std_ss [le_sup]
           ++ MATCH_MP_TAC le_trans
	   ++ Q.EXISTS_TAC `f_n 0 x`
	   ++ RW_TAC std_ss []
	   >> FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION]
	   ++ POP_ASSUM MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	   ++ METIS_TAC [])
 ++ `!i x. x IN m_space m ==> f_n i x <= g x`
     by (RW_TAC std_ss []
         ++ Q.UNABBREV_TAC `g`
	 ++ RW_TAC std_ss [le_sup]
	 ++ POP_ASSUM MATCH_MP_TAC
	 ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	 ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	 ++ METIS_TAC [])
  ++ `!i. integrable m (f_n i)` by FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION]
  ++ `!i x. x IN m_space m ==> 0 <= f_n i x` by FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION]
  ++ `!x. x IN m_space m ==> (sup (IMAGE (\i. f_n i x) univ(:num)) = g x)` by METIS_TAC []
  ++ `!x. x IN m_space m ==> mono_increasing (\i. f_n i x)`
         by FULL_SIMP_TAC std_ss [ext_mono_increasing_suc]
  ++ (MP_TAC o Q.SPECL [`m`,`g`,`f_n`,`(\n. pos_fn_integral m (f_n n))`,`sup (RADON_F_integrals m v)`])
       lebesgue_monotone_convergence
  ++ RW_TAC std_ss []
  ++ `!A. A IN measurable_sets m ==> ?r. (\n. pos_fn_integral m (\x. f_n n x * indicator_fn A x)) --> r`
       by (RW_TAC std_ss []
           ++ RW_TAC std_ss [GSYM convergent]
	      ++ MATCH_MP_TAC SEQ_ICONV
	      ++ RW_TAC std_ss [SEQ_BOUNDED]
	      >> (Q.EXISTS_TAC `pos_fn_integral m g + 1`
	          ++ RW_TAC std_ss []
	          ++ `0 <= pos_fn_integral m (\x. f_n n x * indicator_fn A' x)`
		       by (MATCH_MP_TAC pos_fn_integral_pos
		           ++ METIS_TAC [indicator_fn_def,mul_rzero,mul_rone,le_refl,integrable_mul_indicator])
	 	  ++ FULL_SIMP_TAC std_ss [GSYM ABS_REFL]
		  ++ Suff `pos_fn_integral m (\x. f_n n x * indicator_fn A' x) <= pos_fn_integral m g`
		  >> REAL_ARITH_TAC
		  ++ MATCH_MP_TAC pos_fn_integral_mono
		  ++ METIS_TAC [integrable_mul_indicator,indicator_fn_def,mul_rzero,mul_rone,le_refl])
	      ++ FULL_SIMP_TAC std_ss [real_ge,GREATER_EQ]
	      ++ MATCH_MP_TAC pos_fn_integral_mono
	      ++ `!x. x IN m_space m ==> (\x. f_n n x * indicator_fn A' x) x <=
	      	      	   	     	 (\x. f_n m' x * indicator_fn A' x) x`
                   by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
		       ++ FULL_SIMP_TAC std_ss [GSYM ext_mono_increasing_suc,ext_mono_increasing_def])
	      ++ METIS_TAC [integrable_mul_indicator,indicator_fn_def,mul_rzero,mul_rone,le_refl])
  ++ `!A. A IN measurable_sets m ==> (\n. pos_fn_integral m (\x. f_n n x * indicator_fn A x)) -->
     	       		       	     pos_fn_integral m (\x. g x * indicator_fn A x)`
        by (RW_TAC std_ss []
	    ++ `?r. (\n. pos_fn_integral m (\x. f_n n x * indicator_fn A' x)) --> r` by METIS_TAC []
	    ++ (MP_TAC o Q.SPECL [`m`,`g`,`f_n`,`(\n. pos_fn_integral m (\x. f_n n x * indicator_fn A' x))`,
	                          `r`,`A'`])  lebesgue_monotone_convergence_subset
            ++ RW_TAC std_ss []
	    ++ `!x. 0 <= (\x. g x * indicator_fn A' x) x`
                 by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
	    ++ Suff `pos_fn_integral m (\x. g x * indicator_fn A' x) =
	             integral m (\x. g x * indicator_fn A' x)`
	    >> METIS_TAC []
	    ++ FULL_SIMP_TAC std_ss [integral_pos_fn])
  ++ `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g x * indicator_fn A x) <= measure v A`
         by (RW_TAC std_ss []
	     ++ MATCH_MP_TAC SEQ_LE_IMP_LIM_LE
	     ++ Q.EXISTS_TAC `(\n. pos_fn_integral m (\x. f_n n x * indicator_fn A' x))`
	     ++ RW_TAC std_ss []
	     ++ FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION])
  ++ `g IN RADON_F m v` by FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION]
  ++ `(\n. pos_fn_integral m (f_n n)) --> pos_fn_integral m g`
       by FULL_SIMP_TAC std_ss [pos_fn_integral_mspace,MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ `pos_fn_integral m g = sup (RADON_F_integrals m v)` by FULL_SIMP_TAC std_ss [integral_pos_fn]
  ++ Q.ABBREV_TAC `nu = (\A. measure v A - pos_fn_integral m (\x. g x * indicator_fn A x))`
  ++ `!A x. 0 <= (\x. g x * indicator_fn A x) x`
      by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_01,le_refl]
  ++ `!A. A IN measurable_sets m ==> 0 <= pos_fn_integral m (\x. g x * indicator_fn A x)`
          by FULL_SIMP_TAC std_ss [pos_fn_integral_pos,integrable_mul_indicator]
  ++ `!A. A IN measurable_sets m ==> 0 <= nu A` by METIS_TAC [REAL_SUB_LE]
  ++ `positive (m_space m,measurable_sets m,nu)`
       by (RW_TAC std_ss [positive_def,measure_def,measurable_sets_def]
	   ++ Q.UNABBREV_TAC `nu`
	   ++ RW_TAC real_ss [MEASURE_EMPTY,indicator_fn_def,NOT_IN_EMPTY,pos_fn_integral_zero,mul_rzero])
  ++ `measure_space (m_space m,measurable_sets m,nu)`
      by (FULL_SIMP_TAC std_ss [measure_space_def,m_space_def,measurable_sets_def,
      	 		        countably_additive_def,measure_def]
          ++ Q.UNABBREV_TAC `nu`
          ++ RW_TAC std_ss [o_DEF]
	  ++ `(\x. measure v (f x) - pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) =
	      (\x. (\x. measure v (f x)) x - (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) x)`
                 by RW_TAC std_ss []
          ++ POP_ORW
	  ++ MATCH_MP_TAC SER_SUB
	  ++ CONJ_TAC >> METIS_TAC [o_DEF,countably_additive_def]
	  ++ `measure_space m` by METIS_TAC [measure_space_def,countably_additive_def]
	  ++ `(!i x. 0 <= (\i x. g x * indicator_fn (f i) x) i x)`
               by RW_TAC std_ss [mul_rzero,mul_rone,indicator_fn_def,le_refl]
	  ++ FULL_SIMP_TAC std_ss [IN_FUNSET,IN_UNIV]
	  ++ `!i. integrable m (\x. g x * indicator_fn (f i) x)`
               by METIS_TAC [integrable_mul_indicator]
	  ++ (MP_TAC o Q.SPECL [`m`,`(\i:num. (\x. g x * indicator_fn (f i) x))`])
                  pos_fn_integral_suminf_integrable
	  ++ RW_TAC std_ss []
	  ++ `!x. (\x. suminf (\i. g x * indicator_fn (f i) x)) x <= g x`
                by (RW_TAC std_ss []
		    ++ `suminf (\i. g x * (\i. indicator_fn (f i) x) i) =
		        g x * suminf (\i. indicator_fn (f i) x)`
              		 by (MATCH_MP_TAC ext_suminf_cmul
                             ++ RW_TAC std_ss [mul_rone,mul_rzero,le_refl,indicator_fn_def,le_01])
		    ++ FULL_SIMP_TAC std_ss []
		    ++ Suff `suminf (\i. indicator_fn (f i) x) <= 1`
		    >> METIS_TAC [le_lmul_imp,mul_rone]
		    ++ RW_TAC std_ss [ext_suminf_def,sup_le]
		    ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
		    ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
		    ++ (MP_TAC o Q.SPECL [`count n`,` BIGUNION (IMAGE f (count n))`,`f`])
		       	       indicator_fn_split
		    ++ RW_TAC std_ss [FINITE_COUNT]
		    ++ POP_ASSUM (MP_TAC o GSYM o Q.SPEC `BIGUNION (IMAGE f (count n))`)
		    ++ RW_TAC std_ss [SUBSET_REFL]
		    ++ `!x. SIGMA (\i. indicator_fn (BIGUNION (IMAGE f (count n)) INTER f i) x) (count n) =
		            SIGMA (\i. indicator_fn (f i) x) (count n)`
 			  by (RW_TAC std_ss []
			      ++ (MATCH_MP_TAC o REWRITE_RULE [FINITE_COUNT] o Q.SPEC `count n` o
			          INST_TYPE [``:'a`` |-> ``:num``])
			      	 	       EXTREAL_SUM_IMAGE_EQ
			      ++ RW_TAC std_ss [IN_COUNT,indicator_fn_def,mul_rzero,mul_rone,
			      	 	        IN_BIGUNION_IMAGE,IN_INTER]
			      ++ METIS_TAC [])
                    ++ Suff `indicator_fn (BIGUNION (IMAGE f (count n))) x <= 1`
		    >> METIS_TAC []
		    ++ METIS_TAC [indicator_fn_def,le_refl,le_01])
          ++ `integrable m (\x. suminf (\i. g x * indicator_fn (f i) x))`
               by (MATCH_MP_TAC integrable_bounded
	           ++ Q.EXISTS_TAC `g`
		   ++ RW_TAC std_ss []
		   >> (Suff `0 <= suminf (\i. g x * indicator_fn (f i) x)` >> METIS_TAC [abs_refl]
		       ++ RW_TAC std_ss [ext_suminf_def,le_sup]
		       ++ POP_ASSUM MATCH_MP_TAC
		       ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
		       ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
		       ++ Q.EXISTS_TAC `0`
		       ++ RW_TAC std_ss [COUNT_ZERO,EXTREAL_SUM_IMAGE_THM])
                   ++ RW_TAC std_ss [ext_suminf_def]
	  	   ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
	  	   ++ Q.EXISTS_TAC `(\n. (\x. SIGMA (\i. g x * indicator_fn (f i) x) (count n)))`
	  	   ++ RW_TAC std_ss []
	  	   >> ((MATCH_MP_TAC o INST_TYPE [``:'b`` |-> ``:num``]) IN_MEASURABLE_BOREL_SUM
	      	       ++ RW_TAC std_ss []
	      	       ++ Q.EXISTS_TAC `(\i. (\x. g x * indicator_fn (f i) x))`
	      	       ++ Q.EXISTS_TAC `count n`
	      	       ++ RW_TAC std_ss [FINITE_COUNT]
	      	       ++ METIS_TAC [integrable_def])
	           ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
	  	   ++ RW_TAC std_ss [FINITE_COUNT,SUBSET_DEF,IN_COUNT,indicator_fn_def,
		      	     	     mul_rone,mul_rzero,le_refl]
	  	   ++ DECIDE_TAC)
	  ++ `(\x. suminf (\i. g x * indicator_fn (f i) x)) =
	      (\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x)`
	        by (RW_TAC std_ss [FUN_EQ_THM]
	 	    ++ `suminf (\i. g x * (\i. indicator_fn (f i) x) i) =
		        g x * suminf (\i. indicator_fn (f i) x)`
              		 by (MATCH_MP_TAC ext_suminf_cmul
                             ++ RW_TAC std_ss [mul_rone,mul_rzero,le_refl,indicator_fn_def,le_01])
		    ++ FULL_SIMP_TAC std_ss [indicator_fn_suminf])
          ++ `integral m (\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x) =
	      pos_fn_integral m (\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x)`
              by (MATCH_MP_TAC integral_pos_fn
	          ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl])
          ++ FULL_SIMP_TAC std_ss []
	  ++ `(\i. integral m (\x. g x * indicator_fn (f i) x)) =
	      (\i. pos_fn_integral m (\x. g x * indicator_fn (f i) x))`
                by RW_TAC std_ss [FUN_EQ_THM,integral_pos_fn]
          ++ POP_ORW
	  ++ MATCH_MP_TAC SUMMABLE_SUM
	  ++ RW_TAC std_ss [summable,sums,REAL_SUM_IMAGE_EQ_sum]
	  ++ RW_TAC std_ss [GSYM convergent]
	  ++ MATCH_MP_TAC SEQ_ICONV
	  ++ RW_TAC std_ss [SEQ_BOUNDED]
	  >> (Q.EXISTS_TAC `pos_fn_integral m (\x. suminf (\i. g x * indicator_fn (f i) x)) + 1`
	      ++ RW_TAC std_ss []
	      ++ `0 <= SIGMA (\i. pos_fn_integral m (\x'. g x' * indicator_fn (f i) x')) (count n)`
                   by (MATCH_MP_TAC REAL_SUM_IMAGE_POS
		       ++ RW_TAC std_ss [FINITE_COUNT]
		       ++ MATCH_MP_TAC integral_pos
		       ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl])
  	      ++ FULL_SIMP_TAC std_ss [GSYM ABS_REFL]
	      ++ Suff `SIGMA (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) (count n) <=
    	      	       suminf (\i. integral m (\x. g x * indicator_fn (f i) x))`
	      >> REAL_ARITH_TAC
	      ++ (MP_TAC o GSYM o Q.SPECL [`m`,`(\i. (\x. g x * indicator_fn (f i) x))`,`count n`] o
	      	           INST_TYPE [``:'b`` |-> ``:num``]) pos_fn_integral_sum
              ++ RW_TAC std_ss [FINITE_COUNT]
	      ++ `suminf (\i. integral m (\x. g x * indicator_fn (f i) x)) =
	          pos_fn_integral m (\x. suminf (\i. g x * indicator_fn (f i) x))`
                   by FULL_SIMP_TAC std_ss []
	      ++ POP_ORW
	      ++ MATCH_MP_TAC pos_fn_integral_mono
	      ++ FULL_SIMP_TAC std_ss []
	      ++ CONJ_TAC
	      >> ((MP_TAC o Q.SPECL [`m`,`(\i. (\x. g x * indicator_fn (f i) x))`,`count n`] o
	      	 	    INST_TYPE [``:'b`` |-> ``:num``]) integrable_sum
		  ++ FULL_SIMP_TAC std_ss [FINITE_COUNT])
	      ++ CONJ_TAC
	      >> (RW_TAC std_ss [ext_suminf_def,le_sup]
	          ++ POP_ASSUM MATCH_MP_TAC
		  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
		  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
		  ++ METIS_TAC [])
	      ++ RW_TAC std_ss []
	      ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
	      ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl,FINITE_COUNT])
          ++ FULL_SIMP_TAC std_ss [real_ge,GREATER_EQ]
	  ++ MATCH_MP_TAC REAL_SUM_IMAGE_MONO_SET
	  ++ RW_TAC std_ss [FINITE_COUNT,SUBSET_DEF,IN_COUNT]
	  ++ DECIDE_TAC)
  ++ `!A. A IN measurable_sets m ==> nu A <= nu (m_space m)` by METIS_TAC [MEASURE_SPACE_INCREASING,INCREASING,MEASURE_SPACE_SUBSET_MSPACE,measure_def,measurable_sets_def,m_space_def,MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ Cases_on `nu A = 0` >> METIS_TAC [REAL_SUB_0]
  ++ `0 < nu A` by METIS_TAC [REAL_LT_LE,MEASURE_SPACE_POSITIVE,positive_def]
  ++ `0 < nu (m_space m)` by METIS_TAC [REAL_LTE_TRANS]
  ++ `0 <> measure m (m_space m)`
       by (SPOSE_NOT_THEN ASSUME_TAC
           ++ `measure v (m_space m) = 0` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,measure_absolutely_continuous_def]
           ++ `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) <= 0`
               by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]
           ++ `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) =  0`
               by METIS_TAC [REAL_LE_ANTISYM,MEASURE_SPACE_MSPACE_MEASURABLE]
           ++ `nu (m_space m) = 0` by (Q.UNABBREV_TAC `nu` ++ METIS_TAC [REAL_SUB_RZERO])
           ++ METIS_TAC [REAL_LT_IMP_NE])
  ++ `0 < measure m (m_space m)` by METIS_TAC [REAL_LT_LE,MEASURE_SPACE_POSITIVE,positive_def,
					       MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ Q.ABBREV_TAC `z = nu (m_space m) / (2 * measure m (m_space m)) `
  ++ `0 < z` by METIS_TAC [REAL_LT_DIV,REAL_LT_MUL,EVAL ``0 < 2:real``]
  ++ Q.ABBREV_TAC `snu = (\A. nu A - z * (measure m A))`
  ++ `?A'. A' IN measurable_sets m /\ snu(m_space m) <= snu (A') /\
       (!B. B IN measurable_sets m /\ B SUBSET A' ==> 0 <= snu (B))`
        by (Q.UNABBREV_TAC `snu`
            ++ RW_TAC std_ss []
	    ++ (MP_TAC o Q.SPECL [`(m_space m, measurable_sets m, nu)`,
	       	       	          `(m_space m, measurable_sets m, (\A. z * measure m A))`]) RN_lemma2
	    ++ RW_TAC std_ss [m_space_def,measurable_sets_def,measure_def]
	    ++ METIS_TAC [MEASURE_SPACE_CMUL,REAL_LT_IMP_LE])
  ++ Q.ABBREV_TAC `g' = (\x. g x + Normal z * indicator_fn (A') x)`
  ++ `!A. A IN measurable_sets m ==>
          (pos_fn_integral m (\x. g' x * indicator_fn A x) =
           pos_fn_integral m (\x. g x * indicator_fn A x) + z * measure m (A INTER A'))`
       by (REPEAT STRIP_TAC
           ++ `measure m (A'' INTER A') = pos_fn_integral m (indicator_fn (A'' INTER A'))`
                by METIS_TAC [pos_fn_integral_indicator,MEASURE_SPACE_INTER]
           ++ POP_ORW
	   ++ `z * pos_fn_integral m (indicator_fn (A'' INTER A')) =
               pos_fn_integral m (\x. Normal z * indicator_fn (A'' INTER A') x)`
                by ((MATCH_MP_TAC o GSYM) pos_fn_integral_cmul
                    ++ METIS_TAC [REAL_LT_IMP_LE,indicator_fn_def,le_01,le_refl,
		       		  integrable_indicator,MEASURE_SPACE_INTER])
           ++ POP_ORW
	   ++ Q.UNABBREV_TAC `g'`
	   ++ `(\x. (\x. g x + Normal z * indicator_fn A' x) x * indicator_fn A'' x) =
               (\x. (\x. g x * indicator_fn A'' x) x + (\x. Normal z * indicator_fn (A'' INTER A') x) x)`
                by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,IN_INTER]
                    ++ METIS_TAC [mul_rone,mul_rzero,add_rzero,indicator_fn_def,IN_INTER])
           ++ POP_ORW
	   ++ MATCH_MP_TAC pos_fn_integral_add
	   ++ FULL_SIMP_TAC std_ss []
	   ++ CONJ_TAC >> (RW_TAC std_ss [indicator_fn_def,le_01,le_refl,mul_rone,mul_rzero]
                           ++ FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_le_def,REAL_LT_IMP_LE])
           ++ RW_TAC std_ss []
	   >> METIS_TAC [integrable_mul_indicator]
	   ++ METIS_TAC [integrable_cmul,integrable_indicator,MEASURE_SPACE_INTER])
  ++ `!A. A IN measurable_sets m ==> ((A INTER A') IN measurable_sets m /\ (A INTER A') SUBSET A')`
         by METIS_TAC [INTER_SUBSET,MEASURE_SPACE_INTER]
  ++ `!A. A IN measurable_sets m ==> 0 <= nu (A INTER A') - z * measure m (A INTER A')`
         by (Q.UNABBREV_TAC `snu` ++ METIS_TAC [MEASURE_SPACE_INTER])
  ++ `!A. A IN measurable_sets m ==> z * measure m (A INTER A') <= nu (A INTER A')`
        by METIS_TAC [REAL_SUB_LE]
  ++ `!A. A IN measurable_sets m ==>
          pos_fn_integral m (\x. g x * indicator_fn A x) + z * measure m (A INTER A') <=
          pos_fn_integral m (\x. g x * indicator_fn A x) + nu (A INTER A')`
         by METIS_TAC [REAL_LE_LADD]
  ++ `!A. A IN measurable_sets m ==> nu (A INTER A') <= nu A`
         by (RW_TAC std_ss []
             ++ (MATCH_MP_TAC o REWRITE_RULE [measurable_sets_def,measure_def] o
                                Q.SPEC `(m_space m,measurable_sets m,nu)`) INCREASING
	     ++ METIS_TAC [MEASURE_SPACE_INCREASING,MEASURE_SPACE_INTER,INTER_SUBSET])
  ++ `!A. A IN measurable_sets m ==>
          pos_fn_integral m (\x. g x * indicator_fn A x) + z * measure m (A INTER A') <=
          pos_fn_integral m (\x. g x * indicator_fn A x) + nu (A)`
           by METIS_TAC [REAL_LE_LADD,REAL_LE_TRANS]
  ++ `!A. A IN measurable_sets m ==>
          pos_fn_integral m (\x. g x * indicator_fn A x) + z * measure m (A INTER A') <= measure v A`
           by (Q.UNABBREV_TAC `nu`
	       ++ METIS_TAC [REAL_SUB_ADD2])
  ++ `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g' x * indicator_fn A x) <= measure v A`
        by METIS_TAC []
  ++ `!x. 0 <= g' x`
       by (Q.UNABBREV_TAC `g'`
           ++ RW_TAC std_ss []
	   ++ MATCH_MP_TAC le_add
	   ++ RW_TAC std_ss []
	   ++ MATCH_MP_TAC le_mul
	   ++ RW_TAC real_ss [extreal_le_def,extreal_of_num_def,indicator_fn_def,REAL_LT_IMP_LE])
  ++ `integrable m g'`
       by (Q.UNABBREV_TAC `g'`
           ++ `(\x. g x + Normal z * indicator_fn A' x) =
               (\x. g x + (\x. Normal z * indicator_fn A' x) x)` by RW_TAC std_ss []
           ++ POP_ORW
	   ++ MATCH_MP_TAC integrable_add
	   ++ METIS_TAC [integrable_indicator,integrable_cmul])
  ++ `g' IN RADON_F m v` by RW_TAC std_ss [RADON_F_def,GSPECIFICATION]
  ++ `pos_fn_integral m g' IN RADON_F_integrals m v`
       by (FULL_SIMP_TAC std_ss [RADON_F_integrals_def,GSPECIFICATION]
           ++ METIS_TAC [])
  ++ `pos_fn_integral m (\x. g' x * indicator_fn (m_space m) x) =
      pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) +
      z * measure m A'`
         by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,MEASURE_SPACE_SUBSET_MSPACE,SUBSET_INTER2]
  ++ `pos_fn_integral m g' = pos_fn_integral m g + z * measure m A'`
       by METIS_TAC [pos_fn_integral_mspace]
  ++ `0 < snu (m_space m)`
       by (Q.UNABBREV_TAC `snu`
           ++ RW_TAC std_ss []
           ++ `0 < 2 * measure m (m_space m)` by RW_TAC real_ss [REAL_LT_MUL]
	   ++ Q.UNABBREV_TAC `z`
	   ++ RW_TAC std_ss [real_div]
	   ++ `inv (2 * measure m (m_space m)) = inv 2 * inv (measure m (m_space m))`
                  by METIS_TAC [EVAL ``0 <> 2:real``,REAL_INV_MUL]
	   ++ `nu (m_space m) * inv 2 * inv (measure m (m_space m)) * measure m (m_space m) =
               nu (m_space m) * inv 2`
                 by METIS_TAC [REAL_MUL_LINV,REAL_MUL_ASSOC,REAL_MUL_RID]
           ++ RW_TAC std_ss [REAL_MUL_ASSOC]
	   ++ RW_TAC std_ss [GSYM real_div,REAL_NEG_HALF]
	   ++ FULL_SIMP_TAC real_ss [REAL_LT_DIV])
  ++ `0 < snu A'` by METIS_TAC [REAL_LTE_TRANS]
  ++ `z * measure m A' < nu (A')` by METIS_TAC [REAL_SUB_LT]
  ++ `0 <= z * measure m A'` by METIS_TAC [REAL_LE_MUL,REAL_LT_IMP_LE,MEASURE_SPACE_POSITIVE,positive_def]
  ++ `0 < nu A'` by METIS_TAC [REAL_LET_TRANS]
  ++ `0 <> measure m A'`
        by (SPOSE_NOT_THEN ASSUME_TAC
            ++ `measure v A' = 0`
                by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,measure_absolutely_continuous_def]
            ++ `pos_fn_integral m (\x. g x * indicator_fn A' x) <= 0` by METIS_TAC []
            ++ `pos_fn_integral m (\x. g x * indicator_fn A' x) =  0` by METIS_TAC [REAL_LE_ANTISYM]
            ++ `nu A' = 0` by (Q.UNABBREV_TAC `nu` ++ METIS_TAC [REAL_SUB_RZERO])
            ++ METIS_TAC [REAL_LT_IMP_NE])
  ++ `0 < measure m A'`
      by METIS_TAC [REAL_LT_LE,MEASURE_SPACE_POSITIVE,positive_def,MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ `0 < z * measure m A'` by METIS_TAC [REAL_LT_MUL]
  ++ `pos_fn_integral m g < pos_fn_integral m g'` by METIS_TAC [REAL_LET_ADD2,REAL_LE_REFL,REAL_ADD_RID]
  ++ Suff `pos_fn_integral m g' <= pos_fn_integral m g` >> FULL_SIMP_TAC std_ss [real_lte]
  ++ `pos_fn_integral m g = sup (RADON_F_integrals m v)` by METIS_TAC [integral_pos_fn]
  ++ `?x. x IN (RADON_F_integrals m v)` by METIS_TAC []
  ++ `?z. !x. x IN RADON_F_integrals m v ==> x <= z`
       by (RW_TAC std_ss [RADON_F_integrals_def,GSPECIFICATION]
           ++ Q.EXISTS_TAC `measure v (m_space m)`
	   ++ RW_TAC std_ss [RADON_F_def,GSPECIFICATION]
	   ++ RW_TAC std_ss [pos_fn_integral_mspace]
	   ++ METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE])
  ++ METIS_TAC [REAL_SUP_UBOUND_LE,SPECIFICATION]);

val _ = export_theory();
