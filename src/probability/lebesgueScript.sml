(* ------------------------------------------------------------------------- *)
(* Lebesgue Theory defined on the extended real numbers                      *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble, Cambridge University                    *)
(* ------------------------------------------------------------------------- *)

(* interactive mode
app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
    	  "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory",
	  "transcTheory", "rich_listTheory", "pairTheory",
	  "combinTheory", "realLib", "optionTheory", "real_sigmaTheory",
	  "util_probTheory", "extrealTheory", "measureTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib arithmeticTheory realTheory prim_recTheory
     seqTheory pred_setTheory res_quanTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory
     real_sigmaTheory util_probTheory extrealTheory measureTheory;

val _ = new_theory "lebesgue";

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
quietdec := false;
*)

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)


val pos_simple_fn_integral_def = Define
   `pos_simple_fn_integral m s a x =
	Normal (SIGMA (\i:num. (x i) * ((measure m) (a i))) s)`;

val psfs_def = Define
   `psfs m f = {(s,a,x) | pos_simple_fn m f s a x}`;

val psfis_def = Define
   `psfis m f = IMAGE (\(s,a,x). pos_simple_fn_integral m s a x) (psfs m f)`;

val pos_fn_integral_def = Define
   `pos_fn_integral m f = sup {r | ?g. r IN psfis m g /\ !x. g x <= f x}`;

val integral_def = Define
   `integral m f =
	pos_fn_integral m (fn_plus f) - pos_fn_integral m (fn_minus f)`;

val integrable_def = Define
   `integrable m f =
        f IN measurable (m_space m, measurable_sets m) Borel /\
	pos_fn_integral m (fn_plus f) <> PosInf /\
	pos_fn_integral m (fn_minus f) <> PosInf`;

val finite_space_integral_def = Define
   `finite_space_integral m f =
	SIGMA (\r. r * Normal (measure m (PREIMAGE f {r} INTER m_space m)))
              (IMAGE f (m_space m))`;

val prod_measure_def = Define
   `prod_measure m0 m1 =
	(\a. real (integral m0 (\s0. Normal (measure m1 (PREIMAGE (\s1. (s0,s1)) a)))))`;

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
       ++ FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s' :num -> bool)`)
       	  		        EXTREAL_SUM_IMAGE_IN_IF]
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
               ++ (MP_TAC o Q.SPEC `(\j. indicator_fn (a j INTER b (i:num)) t)` o UNDISCH o
	       	   Q.SPEC `s` o GSYM o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	       ++ Suff `(!x. x IN s ==> 0 <= (\j. indicator_fn (a j INTER b i) t) x)`
	       >> RW_TAC std_ss []
	       ++ RW_TAC std_ss [indicator_fn_def,le_refl,le_01])
       ++ POP_ORW
       ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       ++ `INJ p' (s CROSS s')
	   (IMAGE p' (s CROSS s'))`
	     by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       ++ (MP_TAC o Q.SPEC `(\i:num. Normal (y (SND (p i))) * indicator_fn ((\(i:num,j:num). a i INTER b j) (p i)) t)` o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s':num -> bool)`)
       	  	 	 EXTREAL_SUM_IMAGE_IN_IF]
       ++ `(\x'.if x' IN s CROSS s' then
                Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x'
		 else 0))` by METIS_TAC []
       ++ POP_ORW
       ++ RW_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_IN_IF, EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE]
       ++  `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
	by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
	    ++ (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [FST,SND]
	    ++ EQ_TAC
            >> (STRIP_TAC ++ Q.EXISTS_TAC `(r,q)` ++ RW_TAC std_ss [FST, SND])
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
       ++ (MP_TAC o Q.SPEC `(\i:num. (x (FST (p i))) *
       	  	    	   measure m ((\(i:num,j:num). a i INTER b j) (p i)))` o
	   UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'` o
       	   INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) REAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s:num -> bool)CROSS(s':num -> bool)`)
       	  	 	 REAL_SUM_IMAGE_IN_IF]
       ++ `(\x'. if x' IN s CROSS s' then
                (x (FST x')) * measure m ((\(i,j). a i INTER b j) x') else 0) =
	   (\x'. (if x' IN s CROSS s' then
		(\x'. (x (FST x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))`
		by METIS_TAC []
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
		(\x'. (y (SND x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))`
		by METIS_TAC []
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
       ++ (MP_TAC o Q.SPEC `(\x. (y (FST x)) * measure m (a (SND x) INTER b (FST x)))` o
       	   UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o
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
  ++ (MP_TAC o UNDISCH o Q.SPECL [`i`,`s DELETE i`] o CONJUNCT2 o
      Q.ISPEC `(\i:num. Normal (x i) * indicator_fn (a i) y)`) EXTREAL_SUM_IMAGE_THM
  ++ RW_TAC std_ss [INSERT_DELETE,DELETE_DELETE]
  ++ `!j. j IN (s DELETE i) ==> ~(y IN a j)`
	    by (RW_TAC std_ss [IN_DELETE]
		++ `DISJOINT (a i) (a j)` by METIS_TAC []
		++ FULL_SIMP_TAC std_ss [DISJOINT_DEF, INTER_DEF, EXTENSION,
		   		 	 GSPECIFICATION,NOT_IN_EMPTY]
		++ METIS_TAC [])
  ++ RW_TAC std_ss [Once EXTREAL_SUM_IMAGE_IN_IF]
  ++ `!j. j IN s DELETE i ==> (indicator_fn (a j) y = 0)`
      by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ RW_TAC std_ss [mul_rzero, EXTREAL_SUM_IMAGE_ZERO, add_rzero, indicator_fn_def, mul_rone]);

val pos_simple_fn_le = store_thm
  ("pos_simple_fn_le",``!m f g s a x x' i. measure_space m /\
  			 pos_simple_fn m f s a x /\ pos_simple_fn m g s a x' /\
                        (!x. x IN m_space m ==> g x <= f x) /\
 			(i IN s) /\ ~(a i = {}) ==> (Normal (x' i) <= Normal (x i))``,
  RW_TAC std_ss []
  ++ `!t. t IN a i ==> (f t = Normal (x i))` by METIS_TAC [pos_simple_fn_thm1]
  ++ `!t. t IN a i ==> (g t = Normal (x' i))` by METIS_TAC [pos_simple_fn_thm1]
  ++ METIS_TAC [CHOICE_DEF,pos_simple_fn_def,MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF]);

val pos_simple_fn_cmul = store_thm
 ("pos_simple_fn_cmul", ``!m f z. measure_space m /\ pos_simple_fn m f s a x /\ 0 <= z
 			==> (?s' a' x'. pos_simple_fn m (\t. Normal z * f t) s' a' x')``,
  RW_TAC std_ss [pos_simple_fn_def]
  ++ Q.EXISTS_TAC `s` ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `(\i. z * (x i))`
  ++ RW_TAC std_ss [REAL_LE_MUL, GSYM extreal_mul_def]
  >> METIS_TAC [extreal_le_def, extreal_of_num_def, le_mul]
  ++ (MP_TAC o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) t)`,`z`] o
      UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
  ++ FULL_SIMP_TAC std_ss [mul_assoc]);

val pos_simple_fn_cmul_alt = store_thm
("pos_simple_fn_cmul_alt", ``!m f s a x z. measure_space m /\ 0 <= z /\ pos_simple_fn m f s a x
			     ==> pos_simple_fn m (\t. Normal z * f t) s a (\i. z * x i)``,
  RW_TAC std_ss [pos_simple_fn_def, REAL_LE_MUL, GSYM extreal_mul_def]
  >> METIS_TAC [extreal_le_def, extreal_of_num_def, le_mul]
  ++ (MP_TAC o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) t)`,`z`] o
      UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
  ++ `!x'. (\i. Normal (x i) * indicator_fn (a i) t) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero]
	    ++ RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
  ++ FULL_SIMP_TAC std_ss [mul_assoc]);

val pos_simple_fn_add = store_thm
 ("pos_simple_fn_add",``!m f g. measure_space m /\
 			 pos_simple_fn m f s a x /\ pos_simple_fn m g s' a' x'
			 ==> (?s'' a'' x''. pos_simple_fn m (\t. f t + g t) s'' a'' x'')``,
  REPEAT STRIP_TAC
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`a'`,`x'`]) pos_simple_fn_integral_present
  ++ RW_TAC std_ss []
  ++ Q.EXISTS_TAC `k`
  ++ Q.EXISTS_TAC `c` ++ Q.EXISTS_TAC `(\i. z i + z' i)`
  ++ RW_TAC std_ss [pos_simple_fn_def, REAL_LE_ADD, GSYM extreal_add_def]
  >> METIS_TAC [le_add, pos_simple_fn_def]
  ++ RW_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_ADD]
  ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_EQ
  ++ METIS_TAC [extreal_of_num_def, extreal_le_def, add_rdistrib]);

val pos_simple_fn_add_alt = store_thm
 ("pos_simple_fn_add_alt",``!m f g s a x y. measure_space m /\
 			     pos_simple_fn m f s a x /\ pos_simple_fn m g s a y
			     ==> pos_simple_fn m (\t. f t + g t) s a (\i. x i + y i)``,
  RW_TAC std_ss [pos_simple_fn_def, REAL_LE_ADD, GSYM extreal_add_def, le_add,
  	 	 GSYM EXTREAL_SUM_IMAGE_ADD]
  ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_EQ
  ++  METIS_TAC [extreal_of_num_def, extreal_le_def, add_rdistrib]);

val pos_simple_fn_indicator = store_thm
  ("pos_simple_fn_indicator",``!m A. measure_space m /\ A IN measurable_sets m
				==> ?s a x. pos_simple_fn m (indicator_fn A) s a x``,
  RW_TAC real_ss []
  ++ `FINITE {0:num;1:num}` by METIS_TAC [FINITE_INSERT, FINITE_SING]
  ++ Q.EXISTS_TAC `{0:num;1:num}`
  ++ Q.EXISTS_TAC `(\i. if i = 0 then (m_space m DIFF A) else A)`
  ++ Q.EXISTS_TAC `(\i. if i = 0 then 0 else 1)`
  ++ RW_TAC real_ss [pos_simple_fn_def, indicator_fn_def, FINITE_SING, IN_SING,
     	    	     MEASURE_SPACE_MSPACE_MEASURABLE]
 << [METIS_TAC [le_01,le_refl],
     `{1:num} DELETE 0 = {1}` by (RW_TAC std_ss [EXTENSION, IN_DELETE, IN_SING]
     	      	       	          ++ DECIDE_TAC)
     ++ RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, FINITE_SING, GSYM extreal_of_num_def, mul_lzero,
     	       	        add_lzero,EXTREAL_SUM_IMAGE_SING,mul_rzero,mul_rone],
     METIS_TAC [MEASURE_SPACE_DIFF, MEASURE_SPACE_MSPACE_MEASURABLE],
     RW_TAC real_ss [],
     FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF,
     		   	   NOT_IN_EMPTY,IN_INSERT,IN_SING]
     ++ METIS_TAC [],
     RW_TAC std_ss [IMAGE_DEF]
     ++ `{if i:num = 0 then m_space m DIFF A else A | i IN {0; 1}} = {m_space m DIFF A ; A}`
  	     by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INSERT, IN_SING]
  		 ++ EQ_TAC >> METIS_TAC []
                 ++ RW_TAC std_ss [] >> METIS_TAC []
		 ++ Q.EXISTS_TAC `1:num`
                 ++ RW_TAC real_ss [])
     ++ RW_TAC std_ss [BIGUNION_INSERT, BIGUNION_SING]
     ++ METIS_TAC [UNION_DIFF, MEASURE_SPACE_SUBSET_MSPACE]]);

val pos_simple_fn_indicator_alt = store_thm
("pos_simple_fn_indicator_alt",``!m s. measure_space m /\ s IN measurable_sets m
				==> pos_simple_fn m (indicator_fn s) {0:num;1:num}
				    (\i:num. if i = 0 then (m_space m DIFF s) else s)
				    (\i. if i = 0 then 0 else 1)``,
  RW_TAC std_ss []
  ++ `FINITE {0:num;1:num}` by METIS_TAC [FINITE_INSERT, FINITE_SING]
  ++ `{1:num} DELETE 0 = {1}` by (RW_TAC std_ss [EXTENSION, IN_DELETE, IN_SING]
     	      	       	          ++ DECIDE_TAC)
  ++ RW_TAC real_ss [pos_simple_fn_def, indicator_fn_def, FINITE_SING, IN_SING,
     	    	     MEASURE_SPACE_MSPACE_MEASURABLE, EXTREAL_SUM_IMAGE_THM, mul_rone, mul_lone,
		     mul_rzero, mul_lzero, EXTREAL_SUM_IMAGE_SING, GSYM extreal_of_num_def,
		     add_rzero,add_lzero]
  << [METIS_TAC [le_01,le_refl],
     METIS_TAC [MEASURE_SPACE_DIFF, MEASURE_SPACE_MSPACE_MEASURABLE],
     RW_TAC real_ss [],
     FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF,
     		   	   NOT_IN_EMPTY,IN_INSERT,IN_SING]
     ++ METIS_TAC [],
     RW_TAC std_ss [IMAGE_DEF]
     ++ `{if i:num = 0 then m_space m DIFF s else s | i IN {0; 1}} = {m_space m DIFF s ; s}`
  	     by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INSERT,IN_SING]
  		 ++ EQ_TAC >> METIS_TAC []
                 ++ RW_TAC std_ss [] >> METIS_TAC []
		 ++ Q.EXISTS_TAC `1:num`
                 ++ RW_TAC real_ss [])
     ++ RW_TAC std_ss [BIGUNION_INSERT, BIGUNION_SING]
     ++ METIS_TAC [UNION_DIFF, MEASURE_SPACE_SUBSET_MSPACE]]);

val pos_simple_fn_max = store_thm
("pos_simple_fn_max",``!m f s a x g s'b y.
	measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
	?s'' a'' x''. pos_simple_fn m (\x. max (f x) (g x)) s'' a'' x''``,
  RW_TAC std_ss []
  ++ `?p n. BIJ p (count n) (s CROSS s')`
      by FULL_SIMP_TAC std_ss [GSYM FINITE_BIJ_COUNT, pos_simple_fn_def, FINITE_CROSS]
  ++ `?p'. BIJ p' (s CROSS s') (count n) /\ (!x. x IN (count n) ==> ((p' o p) x = x)) /\
      (!x. x IN (s CROSS s') ==> ((p o p') x = x))` by (MATCH_MP_TAC BIJ_INV ++ RW_TAC std_ss [])
  ++ Q.EXISTS_TAC `IMAGE p' (s CROSS s')`
  ++ Q.EXISTS_TAC `(\(i,j). a i INTER b j) o p`
  ++ Q.EXISTS_TAC `(\n. max ((x o FST o p) n) ((y o SND o p)n))`
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def, extreal_max_def]
  ++ `!i j. i IN IMAGE p' (s CROSS s') /\ j IN IMAGE p' (s CROSS s') /\ i <> j
      ==> DISJOINT (((\(i,j). a i INTER b j) o p) i) (((\(i,j). a i INTER b j) o p) j)`
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
	++ `!s'' x. (?x'. ((x = p' x') /\ FST x' IN s /\ SND x' IN s')) =
	   	    (?x1 x2. ((x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s'))`
            by METIS_TAC [PAIR, FST, SND]
	++ POP_ORW
        ++ `!s''. (?x. (s'' = (\(i,j). a i INTER b j) (p x)) /\ ?x1 x2. (x = p' (x1,x2)) /\
	              x1 IN s /\ x2 IN s') =
                  (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\  x1 IN s /\
		      x2 IN s')`
            by METIS_TAC []
        ++ POP_ORW
        ++ FULL_SIMP_TAC std_ss [o_DEF, IN_CROSS]
        ++ `!s''. (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\  x1 IN s /\
	              x2 IN s') =
                  (?x1 x2. (s'' = (\(i,j). a i INTER b j) (x1,x2)) /\ x1 IN s /\ x2 IN s')`
             by METIS_TAC [FST,SND]
        ++ POP_ORW
       	++ RW_TAC std_ss []
        ++ Suff `(?x1 x2. x' IN a x1 INTER b x2 /\ x1 IN s /\ x2 IN s') = x' IN m_space m`
        >> METIS_TAC []
       	++ RW_TAC std_ss [IN_INTER]
        ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       	++ `m_space m = (BIGUNION (IMAGE a s)) INTER (BIGUNION (IMAGE b s'))`
             by METIS_TAC [INTER_IDEMPOT]
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
  >> (RW_TAC std_ss [max_def] ++ FULL_SIMP_TAC std_ss [IN_IMAGE, IN_CROSS])
  ++ RW_TAC std_ss []
  >> (RW_TAC std_ss [Once EXTREAL_SUM_IMAGE_IN_IF]
      ++ `(\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) x') x else 0)) =
      	  (\x. (if x IN s' then (\i. Normal (y i) *
                SIGMA (\j. indicator_fn (a j INTER b i) x') s) x else 0))`
	  by (RW_TAC std_ss [FUN_EQ_THM]
	      ++ RW_TAC std_ss []
	      ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	      ++ (MP_TAC o REWRITE_RULE [Once INTER_COMM] o
	      	  Q.ISPEC `(b :num -> 'a -> bool) (x'' :num)` o
		  UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
		  Q.ISPECL [`(s :num -> bool)`,
		  `m_space (m:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`,
		  `(a :num -> 'a -> bool)`]) indicator_fn_split
		++ Q.PAT_ASSUM `!i. i IN s' ==> (b:num->'a->bool) i IN measurable_sets m`
		     (ASSUME_TAC o UNDISCH o Q.SPEC `x''`)
		++ `!a m. measure_space m /\ a IN measurable_sets m ==> a SUBSET m_space m`
		     by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
		     	               subset_class_def, subsets_def, space_def]
		++ POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
		       Q.ISPECL [`(b :num -> 'a -> bool) (x'' :num)`,
		       `(m : ('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`])
		++ ASM_SIMP_TAC std_ss [])
      ++ `(\x. if x IN s' then Normal (y x) * indicator_fn (b x) x' else 0) =
          (\x. if x IN s' then (\i. Normal (y i) * indicator_fn (b i) x') x else 0)`
          by METIS_TAC []
      ++ POP_ORW ++ POP_ORW
      ++ `!i. i IN s' ==> (Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) x') s =
      	                   SIGMA (\j. Normal (y i) * indicator_fn (a j INTER b i) x') s)`
           by (RW_TAC std_ss []
               ++ (MP_TAC o Q.SPECL [`(\j. indicator_fn (a j INTER (b:num->'a->bool) i) x')`,
	       	  	             `y (i:num)`] o
		   UNDISCH o Q.ISPEC `s:num->bool` o GSYM o
		   INST_TYPE [alpha |-> ``:num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	       ++ FULL_SIMP_TAC std_ss [])
      ++ RW_TAC std_ss []
      ++ (MP_TAC o Q.ISPEC `(\n':num. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
                           indicator_fn ((\(i:num,j:num). a i INTER b j) (p n')) x')` o
                   UNDISCH o Q.SPEC `p'` o UNDISCH o
                   Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
                   INST_TYPE [``:'b``|->``:num``]) EXTREAL_SUM_IMAGE_IMAGE
      ++ RW_TAC std_ss [o_DEF]
      ++ POP_ASSUM (K ALL_TAC)
      ++ RW_TAC std_ss [Once ((UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`)
      	 	       	     EXTREAL_SUM_IMAGE_IN_IF)]
      ++ `!x. (\j. Normal (y x) * indicator_fn (a j INTER b x) x') =
      	      (\x j. Normal (y x) * indicator_fn (a j INTER b x) x') x` by METIS_TAC []
      ++ POP_ORW
      ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_IF_ELIM, EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE]
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
      ++ (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) x')`
          o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o
	  Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o INST_TYPE [``:'b``|->``:num#num``])
	  	  EXTREAL_SUM_IMAGE_IMAGE
       ++ RW_TAC std_ss [o_DEF]
       ++ Suff `!x'''. x''' IN (s CROSS s') ==>
       	  ((\x. Normal (y (SND x)) * indicator_fn (a (FST x) INTER b (SND x)) x') x''' =
	   (\x''. if x'' IN s CROSS s' then Normal (max (x (FST x'')) (y (SND x''))) *
	        indicator_fn ((\(i,j). a i INTER b j) x'') x' else 0) x''')`
       >> (RW_TAC std_ss []
           ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(s:num->bool) CROSS (s':num->bool)`)
	      	  EXTREAL_SUM_IMAGE_EQ
	   ++ RW_TAC std_ss []
	   ++ DISJ1_TAC
	   ++ RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero])
       ++ RW_TAC std_ss [FUN_EQ_THM]
       ++ Cases_on `x'''`
       ++ RW_TAC real_ss [indicator_fn_def, mul_rone, mul_rzero]
       ++ `q IN s` by METIS_TAC [IN_CROSS,FST,SND]
       ++ `x' IN (a q)` by METIS_TAC [IN_INTER]
       ++ `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s = Normal (x q)`
           by (`pos_simple_fn m f s a x` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
	       ++ METIS_TAC [pos_simple_fn_thm1, pos_simple_fn_def])
       ++ `r IN s'` by METIS_TAC [IN_CROSS, FST, SND]
       ++ `x' IN (b r)` by METIS_TAC [IN_INTER]
       ++ `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' = Normal (y r)`
          by (`pos_simple_fn m g s' b y` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
	      ++ METIS_TAC [pos_simple_fn_thm1])
       ++ FULL_SIMP_TAC std_ss [extreal_le_def, max_def])
  ++ RW_TAC std_ss [Once EXTREAL_SUM_IMAGE_IN_IF]
  ++ `(\x''. if x'' IN s then Normal (x x'') * indicator_fn (a x'') x' else 0) =
      (\x''. if x'' IN s then (\i. Normal (x i) * indicator_fn (a i) x') x'' else 0)`
          by METIS_TAC []
  ++ POP_ORW
  ++ `(\x''. (if x'' IN s then (\i. Normal (x i) * indicator_fn (a i) x') x'' else 0)) =
      (\x''. (if x'' IN s then (\i. Normal (x i) *
      	     SIGMA (\j. indicator_fn (a i INTER b j) x') s') x'' else 0))`
	 by (RW_TAC std_ss [FUN_EQ_THM]
	     ++ RW_TAC std_ss []
	     ++ FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
	     ++ (MP_TAC o Q.ISPEC `(a:num -> 'a -> bool) (x'':num)` o UNDISCH_ALL o
	     	 REWRITE_RULE [GSYM AND_IMP_INTRO] o
		 Q.ISPECL [`(s':num -> bool)`,
		  `m_space (m:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`,
		  `(b :num -> 'a -> bool)`]) indicator_fn_split
	     ++ `a x'' SUBSET m_space m` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE]
	     ++ RW_TAC std_ss [])
  ++ POP_ORW
  ++ `!(i:num). i IN s ==> (Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) x') s' =
     		            SIGMA (\j. Normal (x i) * indicator_fn (a i INTER b j) x') s')`
         by (RW_TAC std_ss []
             ++ (MP_TAC o Q.SPECL [`(\j. indicator_fn ((a:num->'a->bool) i INTER b j) x')`,
	     		  	   `x (i:num)`] o UNDISCH o Q.ISPEC `s':num->bool` o GSYM o
		 INST_TYPE [alpha |-> ``:num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
	     ++ RW_TAC std_ss [])
  ++ RW_TAC std_ss []
  ++ (MP_TAC o Q.ISPEC `(\n':num. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
                         indicator_fn ((\(i:num,j:num). a i INTER b j) (p n')) x')` o
               UNDISCH o Q.SPEC `p'` o UNDISCH o
               Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
               INST_TYPE [``:'b``|->``:num``]) EXTREAL_SUM_IMAGE_IMAGE
  ++ RW_TAC std_ss [o_DEF]
  ++ POP_ASSUM (K ALL_TAC)
  ++ RW_TAC std_ss [Once (Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`
     	    	   	 EXTREAL_SUM_IMAGE_IN_IF)]
  ++ `!x''. (\j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') =
     	    (\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') x''` by METIS_TAC []
  ++ POP_ORW
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_IF_ELIM, EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE]
  ++ Suff `!x'''. x''' IN (s CROSS s') ==>
            ((\x''. Normal (x (FST x'')) * indicator_fn (a (FST x'') INTER b (SND x'')) x') x''' =
	     (\x''. if x'' IN s CROSS s' then Normal (max (x (FST x'')) (y (SND x''))) *
	          indicator_fn ((\(i,j). a i INTER b j) x'') x' else 0) x''')`
  >> (RW_TAC std_ss []
      ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(s:num->bool) CROSS (s':num->bool)`)
      	    EXTREAL_SUM_IMAGE_EQ
      ++ RW_TAC std_ss []
      ++ DISJ1_TAC
      ++ RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero])
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ Cases_on `x'''`
  ++ RW_TAC real_ss [indicator_fn_def, mul_rone, mul_rzero]
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
("pos_simple_fn_not_infty",``!m f s a x. pos_simple_fn m f s a x
			==> (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf)``,
  RW_TAC std_ss [pos_simple_fn_def]
  ++ `(!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) x') i <> NegInf)`
       by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone]
           ++ RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
  ++ `(!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) x') i <> PosInf)`
       by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone]
           ++ RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
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
  ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def,
      		    	    extreal_add_def, extreal_11]
  ++ REVERSE CONJ_TAC
  >> (RW_TAC std_ss [GSYM REAL_SUM_IMAGE_ADD]
      ++ FULL_SIMP_TAC std_ss [REAL_ADD_RDISTRIB])
      ++ RW_TAC std_ss [REAL_LE_ADD,le_add,GSYM extreal_add_def]
  ++ (MP_TAC o Q.SPECL [`\i. Normal (z i) * indicator_fn ((c:num->'a->bool) i) (x':'a)`,
      	      		 `\i. Normal (z' i) * indicator_fn ((c:num->'a->bool) i) (x':'a)`] o
       GSYM o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_ADD
  ++ RW_TAC std_ss []
  ++ MATCH_MP_TAC ((UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_EQ)
  ++ FULL_SIMP_TAC std_ss [add_rdistrib,extreal_le_def,extreal_of_num_def]);

val pos_simple_fn_integral_add_alt = store_thm
  ("pos_simple_fn_integral_add_alt", ``!m f s a x g y.	measure_space m /\
        pos_simple_fn m f s a x /\ pos_simple_fn m g s a y ==>
  	  (pos_simple_fn_integral m s a x +
           pos_simple_fn_integral m s a y =
 	   pos_simple_fn_integral m s a (\i. x i + y i))``,
  RW_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def, GSYM extreal_add_def]
  ++ RW_TAC std_ss [extreal_add_def,extreal_11, GSYM REAL_SUM_IMAGE_ADD]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [REAL_ADD_RDISTRIB]);

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
  ++ RW_TAC std_ss [pos_simple_fn_integral_def,extreal_le_def]
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
  ++ METIS_TAC [REAL_LE_RMUL_IMP,MEASURE_SPACE_POSITIVE,positive_def,REAL_LT_LE]);

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
   METIS_TAC [le_antisym, le_refl, pos_simple_fn_integral_mono]);

val psfis_unique = store_thm
 ("psfis_unique", ``!m f a b.
	measure_space m /\ a IN psfis m f /\ b IN psfis m f ==>	(a = b)``,
   METIS_TAC [le_antisym, le_refl, psfis_mono]);

val pos_simple_fn_integral_indicator = store_thm
 ("pos_simple_fn_integral_indicator", ``!m A. measure_space m /\ A IN measurable_sets m ==>
	(?s a x. pos_simple_fn m (indicator_fn A) s a x /\
		 (pos_simple_fn_integral m s a x = Normal (measure m A)))``,
  RW_TAC std_ss []
  ++ Q.EXISTS_TAC `{0; 1}`
  ++ Q.EXISTS_TAC `\i. if i = 0 then m_space m DIFF A else A`
  ++ Q.EXISTS_TAC `\i. if i = 0 then 0 else 1`
  ++ `{1:num} DELETE 0 = {1}` by RW_TAC real_ss [Once EXTENSION, IN_SING, IN_DELETE]
  ++ RW_TAC real_ss [pos_simple_fn_indicator_alt, pos_simple_fn_integral_def,
     	    	     REAL_SUM_IMAGE_THM,REAL_SUM_IMAGE_SING,FINITE_SING]);

val psfis_indicator = store_thm
  ("psfis_indicator",
   ``!m A. measure_space m /\ A IN measurable_sets m ==>
		Normal (measure m A) IN psfis m (indicator_fn A)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Suff `?s a x. pos_simple_fn m (indicator_fn A) s a x /\
		    (pos_simple_fn_integral m s a x = Normal (measure m A))`
   >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [] ++ Q.EXISTS_TAC `(s,a,x)`
       ++ RW_TAC std_ss [PAIR_EQ])
   ++ MATCH_MP_TAC pos_simple_fn_integral_indicator
   ++ ASM_REWRITE_TAC []);

val pos_simple_fn_integral_cmul = store_thm
  ("pos_simple_fn_integral_cmul", ``!m f s a x z.
 		measure_space m /\ pos_simple_fn m f s a x /\ 0 <= z ==>
	    (pos_simple_fn m (\x. Normal z * f x) s a (\i. z * x i) /\
	    (pos_simple_fn_integral m s a (\i. z * x i) =
	     Normal z * pos_simple_fn_integral m s a x))``,
  RW_TAC std_ss [pos_simple_fn_integral_def, pos_simple_fn_def,REAL_LE_MUL,
  	 	 extreal_11,extreal_mul_def,GSYM REAL_SUM_IMAGE_CMUL,REAL_MUL_ASSOC]
  >> METIS_TAC [le_mul,extreal_le_def,extreal_of_num_def]
  ++ RW_TAC std_ss [(UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_CMUL, mul_assoc,
     	    	    mul_assoc,extreal_mul_def]);

val psfis_cmul = store_thm
 ("psfis_cmul", ``!m f a z. measure_space m /\ a IN psfis m f /\ 0 <= z ==>
	Normal z * a IN psfis m (\x. Normal z * f x)``,
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
("pos_simple_fn_integral_cmul_alt",``!m f s a x z. measure_space m /\ 0 <= z /\
				    pos_simple_fn m f s a x ==>
         (?s' a' x'. (pos_simple_fn m (\t. Normal z * f t) s' a' x') /\
         (pos_simple_fn_integral m s' a' x' = Normal z * pos_simple_fn_integral m s a x))``,
  RW_TAC real_ss []
  ++ Q.EXISTS_TAC `s` ++ Q.EXISTS_TAC `a` ++ Q.EXISTS_TAC `(\i. z * x i)`
  ++ RW_TAC std_ss [pos_simple_fn_cmul_alt]
  ++ FULL_SIMP_TAC real_ss [pos_simple_fn_integral_def, pos_simple_fn_def, REAL_MUL_ASSOC,
     		   	    extreal_11, extreal_mul_def,GSYM REAL_SUM_IMAGE_CMUL]);

val IN_psfis = store_thm
  ("IN_psfis",
   ``!m r f. r IN psfis m f
     ==> ?s a x. pos_simple_fn m f s a x /\ (r = pos_simple_fn_integral m s a x)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   ++ Cases_on `x'`++ Cases_on `x` ++ Cases_on `r` ++ Cases_on `r'`
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [PAIR_EQ]
   ++ METIS_TAC []);

val IN_psfis_eq = store_thm
  ("IN_psfis_eq",
   ``!m r f. r IN psfis m f =
       ?s a x. pos_simple_fn m f s a x /\ (r = pos_simple_fn_integral m s a x)``,
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
  ++ FULL_SIMP_TAC std_ss [PAIR_EQ,pos_simple_fn_def]
  ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
  ++ RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
  ++ RW_TAC std_ss [extreal_of_num_def,extreal_le_def]);

val pos_simple_fn_integral_zero = store_thm
("pos_simple_fn_integral_zero",``!m s a x. measure_space m /\ pos_simple_fn m (\t. 0) s a x
                                 ==> (pos_simple_fn_integral m s a x = 0)``,
  RW_TAC std_ss []
  ++ `pos_simple_fn m (\t. 0) {1:num} (\i:num. if i=1 then (m_space m) else {}) (\i:num. 0) /\
   (pos_simple_fn_integral m  {1:num} (\i:num. if i=1 then (m_space m) else {}) (\i:num. 0) = 0)`
      by RW_TAC real_ss [pos_simple_fn_integral_def, pos_simple_fn_def,
      	 		 FINITE_SING, EXTREAL_SUM_IMAGE_SING, IMAGE_SING,BIGUNION_SING, IN_SING,
         		 MEASURE_SPACE_MSPACE_MEASURABLE, GSYM extreal_of_num_def, mul_lzero,
			 le_refl, REAL_SUM_IMAGE_0]
  ++ METIS_TAC [pos_simple_fn_integral_unique]);

val pos_simple_fn_integral_zero_alt = store_thm
("pos_simple_fn_integral_zero_alt",``!m s a x. measure_space m /\ pos_simple_fn m g s a x /\
				           (!x. x IN m_space m ==> (g x = 0))
                                      ==> (pos_simple_fn_integral m s a x = 0)``,
  RW_TAC std_ss [pos_simple_fn_integral_def,extreal_of_num_def,extreal_11]
  ++ `FINITE s` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
  ++ RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF]
  ++ Suff `(\i. if i IN s then x i * measure m (a i) else 0) = \x. 0`
  >> RW_TAC std_ss [REAL_SUM_IMAGE_0]
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ Cases_on `a x' = {}` >> FULL_SIMP_TAC real_ss [MEASURE_EMPTY]
  ++ RW_TAC std_ss []
  ++ Suff `x x' = 0` >> FULL_SIMP_TAC real_ss []
  ++ `?y. y IN a x'` by METIS_TAC [CHOICE_DEF]
  ++ `y IN m_space m` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE, SUBSET_DEF, pos_simple_fn_def]
  ++ METIS_TAC [pos_simple_fn_thm1,extreal_11]);

val psfis_zero = store_thm
 ("psfis_zero", ``!m a. measure_space m ==> ((a IN psfis m (\x. 0)) = (a = 0))``,
  RW_TAC std_ss []
  ++ EQ_TAC  >> METIS_TAC [IN_psfis_eq,pos_simple_fn_integral_zero]
  ++ RW_TAC std_ss [IN_psfis_eq]
  ++ Q.EXISTS_TAC `{1}` ++ Q.EXISTS_TAC `(\i. m_space m)` ++ Q.EXISTS_TAC `(\i. 0)`
  ++ RW_TAC real_ss [pos_simple_fn_integral_def, pos_simple_fn_def, FINITE_SING,
 		     EXTREAL_SUM_IMAGE_SING, REAL_SUM_IMAGE_SING, IMAGE_SING, BIGUNION_SING,
		     IN_SING, MEASURE_SPACE_MSPACE_MEASURABLE, mul_lzero,
		     GSYM extreal_of_num_def, le_refl]);

val pos_simple_fn_integral_not_infty = store_thm
 ("pos_simple_fn_integral_not_infty", ``!m s a x. pos_simple_fn_integral m s a x <> NegInf /\
 				      	   pos_simple_fn_integral m s a x <> PosInf``,
  RW_TAC std_ss [pos_simple_fn_integral_def,extreal_not_infty]);

val psfis_not_infty = store_thm
 ("psfis_not_infty", ``!m f a. a IN psfis m f ==> (a <> NegInf) /\ (a <> PosInf)``,
  METIS_TAC [IN_psfis_eq,pos_simple_fn_integral_not_infty]);

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
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, NOT_IN_EMPTY]
  >> (`(\t. f e t + SIGMA (\i. f i t) s) =
       (\t. (\t. f e t) t + (\t. SIGMA (\i. f i t) s) t)` by RW_TAC std_ss []
      ++ POP_ORW
      ++ `(\i. x e i + SIGMA (\j. x j i) s) =
          (\i. (\i. x e i) i + (\i. SIGMA (\j. x j i) s) i)` by RW_TAC std_ss []
      ++ POP_ORW
      ++ MATCH_MP_TAC pos_simple_fn_add_alt
      ++ RW_TAC std_ss [] >> METIS_TAC [IN_INSERT]
      ++ Cases_on `s <> {}` >> METIS_TAC [IN_INSERT]
      ++ FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_THM, REAL_SUM_IMAGE_THM, pos_simple_fn_def,
      	 	       	        IN_SING,le_refl, GSYM extreal_of_num_def, mul_lzero,
				EXTREAL_SUM_IMAGE_0])
  ++ Cases_on `s = {}`
  >> (RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, REAL_SUM_IMAGE_THM, add_rzero] ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ `SIGMA (\i. pos_simple_fn_integral m s' a (x i)) s =
      pos_simple_fn_integral m s' a (\j. SIGMA (\i. x i j) s)`
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
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM]
  ++ Cases_on `s = {}`
  >> (RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING, EMPTY_DELETE, EXTREAL_SUM_IMAGE_THM, add_rzero]
     ++ METIS_TAC [IN_SING])
  ++ `?c k z. pos_simple_fn m (\t. SIGMA (\i. f i t) s) k c z /\
        (pos_simple_fn_integral m k c z =
         SIGMA (\i. pos_simple_fn_integral m (s' i) (a i) (x i)) s)`
        by METIS_TAC [IN_INSERT]
  ++ (MP_TAC o Q.SPECL [`m`,`f (e:'b)`,`s' (e:'b)`,`a (e:'b)`,`x (e:'b)`,`(\t. SIGMA (\i:'b. f i t) s)`,`k`,`c`,`z`]) pos_simple_fn_integral_present
  ++ FULL_SIMP_TAC std_ss [IN_INSERT, DELETE_NON_ELEMENT]
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
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, psfis_zero, DELETE_NON_ELEMENT, IN_INSERT]
  ++ `!t. (\i. f i t) = (\i. (\i. f i t) i)` by METIS_TAC []
  ++ POP_ORW
  ++ `(\t. f e t + SIGMA (\i. f i t) s) = (\t. f e t + (\t. SIGMA (\i. f i t) s) t)`
       by METIS_TAC []
  ++ POP_ORW
  ++ METIS_TAC [psfis_add]);

val psfis_intro = store_thm
 ("psfis_intro",
   ``!m a x P. measure_space m /\ (!i. i IN P ==> a i IN measurable_sets m) /\
              (!i. i IN P ==> 0 <= x i) /\ FINITE P
          ==> Normal (SIGMA (\i. (x i) * measure m (a i)) P) IN
                 psfis m (\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) P)``,
  RW_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_NORMAL]
  ++ `!t. (\i. Normal (x i) * indicator_fn (a i) t) =
	   (\i. (\i t. Normal (x i) * indicator_fn (a i) t) i t)`
	by METIS_TAC []
  ++ POP_ORW
  ++ MATCH_MP_TAC psfis_sum
  ++ RW_TAC std_ss []
  ++ METIS_TAC [psfis_cmul, psfis_indicator,extreal_mul_def]);

val pos_simple_fn_integral_sub = store_thm
  ("pos_simple_fn_integral_sub",
   ``!m f s a x g s' b y.
	measure_space m /\
	(!x. g x <= f x) /\ (!x. g x <> PosInf) /\
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
   >> (`!i. (if (i IN k /\ ~(c i = {})) then z i - z' i else 0) * measure m (c i) =
	    (if i IN k then z i - z' i else 0) * measure m (c i)`
		by (RW_TAC std_ss [] ++ FULL_SIMP_TAC real_ss [MEASURE_EMPTY])
	++ POP_ORW
	++ RW_TAC std_ss [extreal_sub_def, extreal_11, GSYM REAL_SUM_IMAGE_SUB]
	++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
	++ RW_TAC std_ss [REAL_SUB_RDISTRIB])
  ++ `!x. g x <> NegInf` by METIS_TAC [lt_infty,lte_trans,extreal_not_infty,extreal_of_num_def]
  ++ CONJ_TAC
  >> METIS_TAC [le_sub_imp,add_lzero]
  ++ REVERSE (RW_TAC real_ss [])
  >> (`?q. q IN c i` by METIS_TAC [CHOICE_DEF]
      ++ METIS_TAC [pos_simple_fn_thm1, REAL_SUB_LE, extreal_le_def])
  ++ `!i. (Normal (if (i IN k /\ ~(c i = {})) then z i - z' i else 0) * indicator_fn (c i) x') =
	(Normal (if i IN k then z i - z' i else 0) * indicator_fn (c i) x')`
	by (RW_TAC std_ss []
	    ++ FULL_SIMP_TAC real_ss [indicator_fn_def, mul_rzero, mul_rone, NOT_IN_EMPTY])
  ++ POP_ORW
  ++ `SIGMA (\i. Normal (if i IN k then z i - z' i else 0) * indicator_fn (c i) x') k =
      SIGMA (\i. Normal (z i - z' i) * indicator_fn (c i) x') k`
         by ((MP_TAC o REWRITE_RULE [SPECIFICATION] o Q.SPECL [`k`,`k`,`(\i. Normal (z i - z' i) * indicator_fn (c i) x')`])(INST_TYPE [alpha |-> ``:num``] EXTREAL_SUM_IMAGE_IF_ELIM)
	     ++ RW_TAC real_ss []
	     ++ `!x. (\i. Normal (z i - z' i) * indicator_fn (c i) x') x <> NegInf`
                  by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                      ++ RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
             ++ RW_TAC std_ss []
             ++ `(\x. if x IN k then Normal (z x - z' x) * indicator_fn (c x) x' else 0) =
                 (\i. Normal (if i IN k then z i - z' i else 0) * indicator_fn (c i) x')`
                   by (RW_TAC real_ss [FUN_EQ_THM,indicator_fn_def,mul_rzero,mul_rone]
	               ++ Cases_on `i IN k` >> METIS_TAC []
		       ++ RW_TAC real_ss [mul_lzero, GSYM extreal_of_num_def])
	     ++ FULL_SIMP_TAC real_ss [])
  ++ POP_ORW
  ++ RW_TAC std_ss [GSYM extreal_sub_def]
  ++ (MP_TAC o Q.SPEC `(\i. (Normal (z i) - Normal (z' i)) * indicator_fn (c i) x')` o
      UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  ++ `!x. x IN k ==> (\i. (Normal (z i) - Normal (z' i)) * indicator_fn (c i) x') x <> NegInf`
        by (RW_TAC std_ss [extreal_sub_def, indicator_fn_def, mul_rzero, mul_rone]
            ++ RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
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
	measure_space m /\ (!x. g x <= f x) /\ (!x. g x <> PosInf) /\
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

(* ---------------------------------------------------- *)
(* Properties of Integrals of Positive Functions        *)
(* ---------------------------------------------------- *)

val pos_fn_integral_pos_simple_fn = store_thm
("pos_fn_integral_pos_simple_fn",``!m f s a x. measure_space m /\ pos_simple_fn m f s a x ==> (pos_fn_integral m f = pos_simple_fn_integral m s a x)``,
  RW_TAC std_ss [pos_fn_integral_def,sup_eq,IN_psfis_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ METIS_TAC [pos_simple_fn_integral_mono])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ METIS_TAC [le_refl]);

val pos_fn_integral_mspace = store_thm
  ("pos_fn_integral_mspace",``!m f. measure_space m  /\ (!x. 0 <= f x)
	 ==> (pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn (m_space m) x))``,
  RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >> (RW_TAC real_ss [le_sup]
      ++ POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)])
      ++ RW_TAC real_ss [GSPECIFICATION,indicator_fn_def]
      ++ Q.EXISTS_TAC `(\x. g x * indicator_fn (m_space m) x)`
      ++ REVERSE (RW_TAC real_ss [indicator_fn_def,IN_psfis_eq,mul_rone,mul_rzero,le_refl])
      ++ FULL_SIMP_TAC std_ss [IN_psfis_eq,pos_simple_fn_def]
      ++ Q.EXISTS_TAC `s`
      ++ Q.EXISTS_TAC `a`
      ++ Q.EXISTS_TAC `x`
      ++ RW_TAC real_ss [mul_rzero,le_refl,mul_rone]
      ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss [mul_rzero,le_refl,mul_rone,indicator_fn_def]
      ++ METIS_TAC [extreal_of_num_def,extreal_le_def])
  ++ RW_TAC real_ss [sup_le]
  ++ POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)])
  ++ RW_TAC real_ss [GSPECIFICATION]
  ++ Q.PAT_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
  ++ RW_TAC std_ss [Once (GSYM SPECIFICATION),GSPECIFICATION]
  ++ Q.EXISTS_TAC `(\x. g x * indicator_fn (m_space m) x)`
  ++ RW_TAC std_ss [IN_psfis_eq]
  >> (FULL_SIMP_TAC real_ss [IN_psfis_eq,pos_simple_fn_def,indicator_fn_def]
      ++ Q.EXISTS_TAC `s`
      ++ Q.EXISTS_TAC `a`
      ++ Q.EXISTS_TAC `x`
      ++ RW_TAC real_ss [le_refl,mul_rzero,mul_rone]
      ++MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss [mul_rzero,le_refl,mul_rone,indicator_fn_def]
      ++ METIS_TAC [extreal_of_num_def,extreal_le_def])
  ++ FULL_SIMP_TAC std_ss [indicator_fn_def,le_refl,mul_rzero,mul_rone]
  ++ METIS_TAC [mul_rone,mul_rzero]);

val pos_fn_integral_zero = store_thm
("pos_fn_integral_zero",``!m. measure_space m ==> (pos_fn_integral m (\x. 0) = 0)``,
  RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ MATCH_MP_TAC psfis_mono
      ++ Q.EXISTS_TAC `m` ++ Q.EXISTS_TAC `g` ++ Q.EXISTS_TAC `(\x. 0)`
      ++ RW_TAC std_ss [psfis_zero])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ Q.EXISTS_TAC `(\x. 0)`
  ++ RW_TAC std_ss [le_refl,psfis_zero]);

val pos_fn_integral_mono = store_thm
("pos_fn_integral_mono",``!f g. ((!x. 0 <= f x /\ f x <= g x) ==> (pos_fn_integral m f <= pos_fn_integral m g))``,
  RW_TAC std_ss [pos_fn_integral_def]
  ++ MATCH_MP_TAC sup_le_sup_imp
  ++ RW_TAC std_ss []
  ++ Q.EXISTS_TAC `x`
  ++ RW_TAC std_ss [le_refl]
  ++ `x IN {r | ?g. r IN psfis m g /\ !x. g x <= f x}` by METIS_TAC [IN_DEF]
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ `?g. x IN psfis m g /\ !x. g x <= f x` by (FULL_SIMP_TAC std_ss [GSPECIFICATION] ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss [GSPECIFICATION]
  ++ METIS_TAC [le_trans]);

val pos_fn_integral_mono_mspace = store_thm
  ("pos_fn_integral_mono_mspace",``!m f g. measure_space m /\ (!x. x IN m_space m ==> g x <= f x) /\
   (!x. 0 <= f x) /\ (!x. 0 <= g x) ==> (pos_fn_integral m g <= pos_fn_integral m f)``,
  RW_TAC std_ss [Once pos_fn_integral_mspace]
  ++ `pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn (m_space m) x)`
      by RW_TAC std_ss [Once pos_fn_integral_mspace]
  ++ POP_ORW
  ++ MATCH_MP_TAC pos_fn_integral_mono
  ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]);

val pos_fn_integral_pos = store_thm
("pos_fn_integral_pos",``!m f. measure_space m /\ (!x. 0 <= f x) ==> 0 <= pos_fn_integral m f``,
  RW_TAC std_ss []
  ++ `0 = pos_fn_integral m (\x. 0)` by METIS_TAC [pos_fn_integral_zero]
  ++ POP_ORW
  ++ MATCH_MP_TAC pos_fn_integral_mono
  ++ RW_TAC std_ss [le_refl]);

val pos_fn_integral_cmul = store_thm
("pos_fn_integral_cmul",``!f c. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) /\ 0 <= c ==> (pos_fn_integral m (\x. Normal c * f x) =  Normal c * pos_fn_integral m f)``,
  RW_TAC std_ss []
  ++ Cases_on `c = 0`
  >> RW_TAC std_ss [GSYM extreal_of_num_def,mul_lzero,pos_fn_integral_zero]
  ++ `0 < c` by FULL_SIMP_TAC std_ss [REAL_LT_LE]
  ++ RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >> (Suff `y / (Normal c) <= sup {r | ?g. r IN psfis m g /\ !x. g x <= f x}`
      >> METIS_TAC [le_ldiv,mul_comm]
      ++ RW_TAC std_ss [le_sup]
      ++ POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ Q.EXISTS_TAC `(\x. g x / (Normal c))`
      ++ REVERSE (RW_TAC std_ss [])
      >> METIS_TAC [mul_comm,le_ldiv]
      ++ RW_TAC std_ss [extreal_div_def]
	  ++ `inv (Normal c) * y IN psfis m (\x. inv (Normal c) * g x)` by METIS_TAC [psfis_cmul,extreal_inv_def,REAL_LE_INV]
          ++ `(\x. g x * inv (Normal c)) = (\x. inv (Normal c) * g x)` by RW_TAC std_ss [FUN_EQ_THM,mul_comm]
          ++ RW_TAC std_ss [Once mul_comm])
  ++ Suff `sup {r | ?g. r IN psfis m g /\ !x. g x <= f x} <= y / Normal c`
  >> METIS_TAC [le_rdiv,mul_comm]
  ++ RW_TAC std_ss [sup_le]
  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ Suff `y' * Normal c <= y` >> METIS_TAC [le_rdiv]
  ++ Q.PAT_ASSUM `!z. {r | ?g. r IN psfis m g /\ !x. g x <= Normal c * f x} z ==> z <= y'` MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ Q.EXISTS_TAC `(\x. Normal c * g x)`
  ++ RW_TAC std_ss []
  ++ METIS_TAC [le_lmul_imp,extreal_of_num_def,extreal_le_def,psfis_cmul,mul_comm]);

val pos_fn_integral_indicator = store_thm
  ("pos_fn_integral_indicator",
   ``!m s. measure_space m /\ s IN measurable_sets m ==>
	   (pos_fn_integral m (indicator_fn s) = Normal (measure m s))``,
  METIS_TAC [pos_fn_integral_pos_simple_fn,pos_simple_fn_integral_indicator]);

val pos_fn_integral_cmul_indicator = store_thm
  ("pos_fn_integral_cmul_indicator",
   ``!m s c. measure_space m /\ s IN measurable_sets m /\ 0 <= c ==>
	   (pos_fn_integral m (\x. Normal c * indicator_fn s x) = Normal (c *  measure m s))``,
  RW_TAC std_ss []
  ++ `!x. 0 <= indicator_fn s x` by RW_TAC std_ss [indicator_fn_def,le_refl,le_01]
  ++ RW_TAC std_ss [pos_fn_integral_cmul]
  ++ METIS_TAC [pos_fn_integral_pos_simple_fn,pos_simple_fn_integral_indicator,extreal_mul_def]);

val pos_fn_integral_sum_cmul_indicator = store_thm
("pos_fn_integral_sum_cmul_indicator",
   ``!m s a x. measure_space m /\ FINITE s /\ (!i:num. i IN s ==> 0 <= x i) /\
            (!i:num. i IN s ==> a i IN measurable_sets m)  ==>
	    (pos_fn_integral m (\t. SIGMA (\i:num. Normal (x i) * indicator_fn (a i) t) s) =
            Normal (SIGMA (\i. x i * measure m (a i)) s))``,
  RW_TAC std_ss []
  ++ Cases_on `s = {}`
  >> (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,REAL_SUM_IMAGE_THM,pos_fn_integral_zero]
      ++ RW_TAC std_ss [extreal_of_num_def])
  ++ `!i. i IN s ==> pos_simple_fn m (indicator_fn (a i)) {0:num; 1}
                       (\n. if n = 0 then m_space m DIFF (a i) else (a i))
		       (\n:num. if n = 0 then 0 else 1)`
      by METIS_TAC [pos_simple_fn_indicator_alt]
  ++ `!i. i IN s ==> pos_simple_fn m (\t. Normal (x i) * indicator_fn (a i) t) {0:num; 1}
     	       	       (\n:num. if n = 0 then m_space m DIFF (a i) else (a i))
		       (\n:num. (x i) * (if n = 0 then 0 else 1))`
      by METIS_TAC [pos_simple_fn_cmul_alt]
  ++ (MP_TAC o Q.SPECL [`m`,`(\i. (\t. Normal (x i) * indicator_fn (a i) t))`,`(\i. {0; 1})`,
     	       	        `(\i. (\n. if n = 0 then m_space m DIFF a i else a i))`,
			`(\i. (\n. x i * if n = 0 then 0 else 1))`,`s`] o
		INST_TYPE [beta |-> ``:num``]) pos_simple_fn_integral_sum_alt
  ++ RW_TAC std_ss []
  ++ `{1:num} DELETE 0 = {1}`
      by METIS_TAC [DELETE_NON_ELEMENT,EVAL ``0=1:num``,EXTENSION,IN_DELETE,IN_SING,NOT_IN_EMPTY]
  ++ `FINITE {1:num}` by RW_TAC std_ss [FINITE_SING]
  ++ `!i:num. i IN s ==> (pos_simple_fn_integral m {0:num; 1}
     	      (\n:num. if n = 0 then m_space m DIFF a i else a i)
	      (\n:num. x i * if n = 0 then 0 else 1) = Normal (x i * measure m (a i)))`
       by RW_TAC real_ss [pos_simple_fn_integral_def,REAL_SUM_IMAGE_THM,GSYM extreal_of_num_def,mul_lzero,add_lzero,REAL_SUM_IMAGE_SING]
  ++ (MP_TAC o Q.SPEC `(\i:num. pos_simple_fn_integral m {0:num; 1} (\n:num. if n = 0 then m_space m DIFF a i else a i) (\n:num. x i * if n = 0 then 0 else 1:real))` o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  ++ RW_TAC std_ss []
  ++ `SIGMA (\x'. if x' IN s then Normal (x x' * measure m (a x')) else 0) s = SIGMA (\i. Normal (x i * measure m (a i))) s`
       by METIS_TAC [EXTREAL_SUM_IMAGE_IN_IF]
  ++ FULL_SIMP_TAC std_ss []
  ++ NTAC 5 (POP_ASSUM (K ALL_TAC))
  ++ POP_ASSUM (MP_TAC o GSYM)
  ++ RW_TAC std_ss [pos_fn_integral_def,sup_eq,GSYM EXTREAL_SUM_IMAGE_NORMAL]
  >> (POP_ASSUM  (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
      ++ MATCH_MP_TAC pos_simple_fn_integral_mono
      ++ Q.EXISTS_TAC `g`
      ++ Q.EXISTS_TAC `(\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)`
      ++ RW_TAC std_ss [])
  ++ POP_ASSUM MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
  ++ Q.EXISTS_TAC `(\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)`
  ++ RW_TAC real_ss []
  ++ METIS_TAC [le_refl]);




(************************************************************)
(* LEBESGUE MONOTONE CONVERGENCE                            *)
(************************************************************)

val lebesgue_monotone_convergence_lemma = store_thm
  ("lebesgue_monotone_convergence_lemma",
    ``!m f fi g r'.
	measure_space m /\
	(!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
	(!x. mono_increasing (\i. fi i x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
 	(r' IN psfis m g) /\ (!x. g x <= f x) /\ (!i x. 0 <= fi i x) ==>
	r' <= sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)``,
  REPEAT STRIP_TAC
  ++ Q.ABBREV_TAC `r = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)`
  ++ Q.ABBREV_TAC `ri = (\i. pos_fn_integral m (fi i))`
  ++ MATCH_MP_TAC le_mul_epsilon
  ++ RW_TAC std_ss []
  ++ (Cases_on `z`
      ++ FULL_SIMP_TAC std_ss [le_infty,lt_infty,extreal_not_infty,extreal_of_num_def])
  ++ FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
  ++ Q.ABBREV_TAC `b = \n. {t | Normal r'' * g t <= (fi n) t}`
  ++ `?s a x. pos_simple_fn m g s a x` by METIS_TAC [IN_psfis]
  ++ `!i j. i <= j ==> ri i <= ri j`
      by (Q.UNABBREV_TAC `ri`
          ++ RW_TAC std_ss []
          ++ MATCH_MP_TAC pos_fn_integral_mono
	  ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_def, GSYM extreal_of_num_def])
  ++ `f IN measurable (m_space m, measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
          ++ Q.EXISTS_TAC `fi`
	  ++ RW_TAC std_ss [space_def]
	  >> FULL_SIMP_TAC std_ss [measure_space_def]
	  ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_def,ext_mono_increasing_suc])
  ++ `g IN measurable (m_space m, measurable_sets m) Borel`
       by METIS_TAC [IN_psfis_eq,IN_MEASURABLE_BOREL_POS_SIMPLE_FN]
  ++ `(\t. Normal r'' * g t) IN measurable (m_space m, measurable_sets m) Borel`
	by ( MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
	     ++ Q.EXISTS_TAC `g` ++ Q.EXISTS_TAC `r''`
	     ++ METIS_TAC [measure_space_def])
  ++ `!n:num. {t | Normal r'' * g t <= fi n t} INTER m_space m =
     	      {t | 0 <= (fi n t) - Normal r'' * (g t)} INTER m_space m`
	by (RW_TAC real_ss [EXTENSION,GSPECIFICATION,IN_INTER]
            ++ METIS_TAC [pos_simple_fn_not_infty,mul_not_infty,add_lzero,
	       		  le_sub_eq,num_not_infty])
  ++ `!n. (\t. fi n t - Normal r'' * g t) IN measurable (m_space m, measurable_sets m) Borel`
	by ( RW_TAC std_ss []
      	     ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
	     ++ Q.EXISTS_TAC `fi n`
	     ++ Q.EXISTS_TAC `(\t. Normal r'' * g t)`
             ++ FULL_SIMP_TAC std_ss [space_def,measure_space_def])
  ++ `!n. {t | Normal r'' * g t <= fi n t} INTER m_space m IN measurable_sets m`
	by METIS_TAC [IN_MEASURABLE_BOREL_ALL,m_space_def,space_def,
			subsets_def,measurable_sets_def,measure_space_def,extreal_of_num_def]
  ++ `!n. b n INTER m_space m IN measurable_sets m` by ( Q.UNABBREV_TAC `b` ++ METIS_TAC [])
  ++ Suff  `r' = sup (IMAGE (\n. pos_fn_integral m (\x. g x * indicator_fn (b n INTER m_space m) x)) UNIV )`
  >> (Q.UNABBREV_TAC `r`
      ++ RW_TAC std_ss [le_sup]
      ++ Cases_on `r'' = 0`
      >> (RW_TAC std_ss [mul_lzero,GSYM extreal_of_num_def]
          ++ MATCH_MP_TAC le_trans
	  ++ Q.EXISTS_TAC `ri (1:num)`
	  ++ REVERSE (RW_TAC std_ss [])
	  >> (POP_ASSUM MATCH_MP_TAC
              ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	      ++ METIS_TAC [])
	  ++ Q.UNABBREV_TAC `ri`
	  ++ RW_TAC std_ss []
	  ++ METIS_TAC [pos_fn_integral_pos,extreal_of_num_def])
      ++ `0 < r''` by METIS_TAC [REAL_LT_LE]
      ++ `0 < Normal r''` by METIS_TAC [extreal_lt_eq,extreal_of_num_def,REAL_LE_REFL]
      ++ ONCE_REWRITE_TAC [mul_comm]
      ++ RW_TAC std_ss [le_rdiv]
      ++ RW_TAC std_ss [sup_le]
      ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ RW_TAC std_ss [GSYM le_rdiv]
      ++ ONCE_REWRITE_TAC [mul_comm]
      ++ `!x. 0 <= (\x. g x * indicator_fn (b n INTER m_space m) x) x`
            by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
                ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def])
      ++ FULL_SIMP_TAC std_ss [GSYM pos_fn_integral_cmul]
      ++ `!x. (\x. Normal r'' * (g x * indicator_fn (b n INTER m_space m) x)) x <= fi n x`
            by (Q.UNABBREV_TAC `b`
                ++ RW_TAC real_ss [indicator_fn_def,GSPECIFICATION,IN_INTER,mul_rzero,mul_rone]
		++ METIS_TAC [extreal_of_num_def])
      ++ MATCH_MP_TAC le_trans
      ++ Q.EXISTS_TAC `pos_fn_integral m (fi n)`
      ++ RW_TAC std_ss [] >> (MATCH_MP_TAC pos_fn_integral_mono ++ METIS_TAC [le_mul,lt_le])
      ++ Q.PAT_ASSUM `!z. IMAGE ri UNIV z ==> z <= y'` MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ Q.EXISTS_TAC `n`
      ++ Q.UNABBREV_TAC `ri`
      ++ RW_TAC std_ss [])
  ++ `!n:num. (\x. g x * indicator_fn (b n INTER m_space m) x) =
      (\t. SIGMA (\i. Normal (x i) * indicator_fn (a i INTER (b n INTER m_space m)) t) s)`
        by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ RW_TAC std_ss []
	    ++ Cases_on `~(t IN m_space m)`
	    >> (RW_TAC real_ss [indicator_fn_def,IN_INTER,mul_rone,mul_rzero] ++ METIS_TAC [pos_simple_fn_def,EXTREAL_SUM_IMAGE_ZERO])
	    ++ RW_TAC real_ss [indicator_fn_def,IN_INTER,mul_rone,mul_rzero]
	    >> FULL_SIMP_TAC real_ss [pos_simple_fn_def,indicator_fn_def]
	    ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def,EXTREAL_SUM_IMAGE_ZERO])
  ++ RW_TAC std_ss []
  ++ `!n:num i. i IN s ==> (a i INTER (b n INTER m_space m)) IN measurable_sets m`
         by METIS_TAC [MEASURE_SPACE_INTER,pos_simple_fn_def]
  ++ `FINITE s` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
  ++ `!n:num. (pos_fn_integral m (\t. SIGMA (\i. Normal (x i) * indicator_fn ((\i. a i INTER (b n INTER m_space m)) i) t) s) =
           Normal (SIGMA (\i. x i * measure m ((\i. a i INTER (b n INTER m_space m)) i)) s))`
              by (RW_TAC std_ss []
	          ++ (MP_TAC o Q.SPECL [`m`,`s:num->bool`,`(\i:num. a i INTER (b (n:num) INTER m_space m))`,`(x:num->real)`]) pos_fn_integral_sum_cmul_indicator
		  ++ FULL_SIMP_TAC std_ss [pos_simple_fn_def])
  ++ FULL_SIMP_TAC std_ss []
  ++ Know `!i. i IN s ==> !n.
            (\i n. Normal (x i * measure m (a i INTER (b n INTER m_space m)))) i n <=
	    (\i n. Normal (x i * measure m (a i INTER (b n INTER m_space m)))) i (SUC n)`
  >> (RW_TAC std_ss [extreal_le_def]
      ++ MATCH_MP_TAC REAL_LE_LMUL_IMP
      ++ RW_TAC std_ss []
      >> METIS_TAC [pos_simple_fn_def]
      ++ MATCH_MP_TAC INCREASING
      ++ RW_TAC std_ss [MEASURE_SPACE_INCREASING]
      ++ RW_TAC std_ss [SUBSET_DEF,IN_INTER]
      ++ Q.UNABBREV_TAC `b`
      ++ FULL_SIMP_TAC std_ss [GSPECIFICATION]
      ++ MATCH_MP_TAC le_trans
      ++ Q.EXISTS_TAC `fi n x'`
      ++ RW_TAC real_ss []
      ++ FULL_SIMP_TAC real_ss [ext_mono_increasing_suc])
  ++ `!i. i IN s ==>
       !n. 0 <= (\i n. Normal (x i * measure m (a i INTER (b n INTER m_space m)))) i n`
         by (RW_TAC std_ss []
	     ++ METIS_TAC [REAL_LE_MUL,MEASURE_SPACE_POSITIVE,positive_def,
	     		   MEASURE_SPACE_INTER,pos_simple_fn_def,extreal_le_def,
			   extreal_of_num_def])
  ++ FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_NORMAL, sup_sum_mono]
  ++ RW_TAC std_ss []
  ++ `!i. BIGUNION (IMAGE (\n. a i INTER (b n INTER m_space m)) UNIV) = a i INTER m_space m`
       by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_INTER,IN_UNIV]
           ++ EQ_TAC >> METIS_TAC []
	   ++ RW_TAC std_ss []
	   ++ Q.UNABBREV_TAC `b`
	   ++ RW_TAC real_ss [GSPECIFICATION]
	   ++ `f x' = sup (IMAGE (\i. fi i x') UNIV)` by FULL_SIMP_TAC std_ss []
	   ++ Cases_on `g x' = 0` >> METIS_TAC [mul_rzero,extreal_of_num_def]
           ++ `Normal r'' * g x' < f x'`
                by (Cases_on `g x' = f x'`
                    >> (`0 < f x'` by METIS_TAC [le_lt,pos_simple_fn_def]
                        ++ METIS_TAC [lt_rmul,mul_lone,IN_psfis_eq,pos_simple_fn_not_infty,
			   	      extreal_lt_eq,extreal_of_num_def])
		    ++ `g x' < f x'` by METIS_TAC [le_lt]
		    ++ METIS_TAC [lt_mul2,mul_lone,extreal_not_infty,pos_simple_fn_not_infty,
		       		  extreal_lt_eq,extreal_of_num_def,extreal_le_def,psfis_pos])
	   ++ Suff `?n. Normal r'' * g x' <= (\n. fi n x') n` >> RW_TAC std_ss []
           ++ MATCH_MP_TAC sup_le_mono
	   ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [ext_mono_increasing_def,ext_mono_increasing_suc]
	   ++ METIS_TAC [])
  ++ `!i. i IN s==> (a i INTER m_space m = a i)`
       by METIS_TAC [pos_simple_fn_def,SUBSET_INTER1,MEASURE_SPACE_SUBSET_MSPACE]
  ++ `!i. i IN s ==> (measure m o (\n. a i INTER (b n INTER m_space m))) --> measure m (a i)`
       by (RW_TAC std_ss []
           ++ MATCH_MP_TAC MONOTONE_CONVERGENCE
           ++ RW_TAC std_ss [IN_FUNSET,IN_UNIV]
           ++ RW_TAC std_ss [SUBSET_DEF,IN_INTER]
           ++ Q.UNABBREV_TAC `b`
           ++ FULL_SIMP_TAC std_ss [GSPECIFICATION]
           ++ MATCH_MP_TAC le_trans
           ++ Q.EXISTS_TAC `fi n x'`
           ++ RW_TAC real_ss []
           ++ FULL_SIMP_TAC real_ss [ext_mono_increasing_suc])
  ++ FULL_SIMP_TAC std_ss [o_DEF]
  ++ `r' = SIGMA (\i. Normal (x i * measure m (a i))) s`
       by METIS_TAC [IN_psfis_eq,psfis_unique,pos_simple_fn_integral_def,
       	  	     pos_simple_fn_integral_unique,EXTREAL_SUM_IMAGE_NORMAL]
  ++ POP_ORW
  ++ (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss []
  ++ `sup (IMAGE (\n. Normal (x x' * measure m (a x' INTER (b n INTER m_space m)))) UNIV) =
     Normal (x x') * sup (IMAGE (\n. Normal (measure m (a x' INTER (b n INTER m_space m)))) UNIV)`
        by (RW_TAC std_ss [GSYM extreal_mul_def]
	    ++ METIS_TAC [sup_cmul,pos_simple_fn_def])
  ++ RW_TAC std_ss [GSYM extreal_mul_def]
  ++ FULL_SIMP_TAC std_ss [extreal_le_def]
  ++ Suff `sup (IMAGE (\n. Normal (measure m (a x' INTER (b n INTER m_space m)))) UNIV) =
     	   Normal (measure m (a x'))`
  >> RW_TAC std_ss []
  ++ Suff `mono_increasing (\n. measure m (a x' INTER (b n INTER m_space m)))`
  >> METIS_TAC [sup_seq]
  ++ RW_TAC std_ss [mono_increasing_suc]
  ++  MATCH_MP_TAC INCREASING
  ++ RW_TAC std_ss [MEASURE_SPACE_INCREASING]
  ++ RW_TAC std_ss [SUBSET_DEF,IN_INTER]
  ++ Q.UNABBREV_TAC `b`
  ++ FULL_SIMP_TAC std_ss [GSPECIFICATION]
  ++ MATCH_MP_TAC le_trans
  ++ Q.EXISTS_TAC `fi n x''`
  ++ RW_TAC real_ss []
  ++ FULL_SIMP_TAC real_ss [ext_mono_increasing_suc]);


val lebesgue_monotone_convergence = store_thm
  ("lebesgue_monotone_convergence", ``!m f fi. measure_space m /\
	(!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!i x. 0 <= fi i x) /\ (!x. 0 <= f x) /\
	(!x. mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) ==>
	(pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))``,
  REVERSE (RW_TAC std_ss [GSYM le_antisym])
  >> (RW_TAC std_ss [sup_le]
      ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ MATCH_MP_TAC pos_fn_integral_mono_mspace
      ++ RW_TAC std_ss []
      ++ Q.PAT_ASSUM `!x. x IN m_space m ==> P` (MP_TAC o GSYM o UNDISCH o Q.SPEC `x`)
      ++ RW_TAC std_ss []
      ++ FULL_SIMP_TAC std_ss [sup_le]
      ++ POP_ASSUM (K ALL_TAC)
      ++ POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ Q.ABBREV_TAC `r = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)`
  ++ RW_TAC std_ss [pos_fn_integral_def,sup_le]
  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ METIS_TAC [lebesgue_monotone_convergence_lemma,le_antisym]);

val lebesgue_monotone_convergence_subset = store_thm
  ("lebesgue_monotone_convergence_subset", ``!m f fi A. measure_space m /\
	(!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\ (!i x. 0 <= fi i x) /\ (!x. 0 <= f x) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
	(!x. mono_increasing (\i. fi i x)) /\ (A IN measurable_sets m) ==>
	(pos_fn_integral m (\x. f x * indicator_fn A x) = sup (IMAGE (\i. pos_fn_integral m (\x. fi i x * indicator_fn A x)) UNIV))``,
  RW_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`(\x. f x * indicator_fn A x)`,`(\i. (\x. fi i x * indicator_fn A x))`]) lebesgue_monotone_convergence
  ++ RW_TAC std_ss []
  ++ POP_ASSUM MATCH_MP_TAC
  ++ CONJ_TAC >> METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,measure_space_def,subsets_def,measurable_sets_def]
  ++ CONJ_TAC >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
  ++ CONJ_TAC >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
  ++ CONJ_TAC >> (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl,ext_mono_increasing_def] ++ FULL_SIMP_TAC std_ss [ext_mono_increasing_def])
  ++ RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ Suff `IMAGE (\i:num. 0:extreal) UNIV = (\y. y = 0)` >> RW_TAC std_ss [sup_const]
  ++ RW_TAC std_ss [EXTENSION,IN_ABS,IN_IMAGE,IN_UNIV]);



(**********************************************************)
(*  Existence of Convergent sequence                      *)
(**********************************************************)


(**** Define the sequence ****)
val fn_seq_def = Define `fn_seq m f = (\n.
         (\x. SIGMA (\k. (&k / (2 pow n)) * indicator_fn {x | x IN m_space m /\ (&k / (2 pow n) <= f x) /\ (f x < (&k + 1) /(2 pow n))} x) (count (4 ** n)) +
              2 pow (n) * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} x))`;

(**** Define their integrals ****)
val fn_seq_integral_def = Define `fn_seq_integral m f = (\n. Normal (SIGMA (\k. (&k / (2 pow n)) * measure m {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n}) (count (4 ** n)) + (2 pow n) * measure m {x | x IN m_space m /\ 2 pow n <= f x} ))`;



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
  ("lemma_fn_sup",``!m f x. x IN m_space m /\ 0 <= f x ==>
                      (sup (IMAGE (\n. fn_seq m f n x) UNIV) = f x)``,
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
  ("lemma_fn_in_psfis",``!m f n.  (!x. 0 <= f x) /\ measure_space m /\
  			      f IN measurable (m_space m,measurable_sets m) Borel
			 ==> (fn_seq_integral m f n IN psfis m (fn_seq m f n))``,
  RW_TAC std_ss [IN_psfis_eq,pos_simple_fn_def]
  ++ Q.EXISTS_TAC `count (4 ** n + 1)`
  ++ Q.EXISTS_TAC `(\k. if k IN count (4 ** n) then {x | x IN m_space m /\ &k / 2 pow n <= f x /\
     		  	 f x < (&k + 1) / 2 pow n} else {x | x IN m_space m /\ 2 pow n <= f x} )`
  ++ Q.EXISTS_TAC `(\k. if k IN count (4 ** n) then &k / 2 pow n else 2 pow n )`
  ++ `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  ++ `FINITE (count (4 ** n + 1))` by RW_TAC std_ss [FINITE_COUNT]
  ++ `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  ++ `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  ++ `!n k. &k / 2 pow n = Normal (&k / 2 pow n)`
      by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_div_eq]
  ++ `!n z. Normal z / 2 pow n = Normal (z / 2 pow n)`
      by METIS_TAC [extreal_pow_def,extreal_div_eq,extreal_of_num_def]
  ++ CONJ_TAC
  >> (CONJ_TAC >> RW_TAC std_ss [lemma_fn_5]
      ++ CONJ_TAC
      >> (RW_TAC real_ss [fn_seq_def,IN_COUNT,GSYM ADD1,COUNT_SUC,EXTREAL_SUM_IMAGE_THM]
          ++ `(\i. Normal (if i < 4 ** n then &i / 2 pow n else 2 pow n) *
		   indicator_fn (if i < 4 ** n then
		   {x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\
		      	     	     f x < (&i + 1) / 2 pow n}
                   else {x | x IN m_space m /\ 2 pow n <= f x}) t) =
	      (\i. if i < 4 ** n then &i / 2 pow n  *
                 indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\
		 	      	     f x < (&i + 1) / 2 pow n} t
                   else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t)`
                by (RW_TAC std_ss [FUN_EQ_THM]
                    ++ Cases_on `i < 4 ** n` >> RW_TAC std_ss []
                    ++ RW_TAC std_ss [extreal_of_num_def,extreal_pow_def])
	  ++ POP_ORW
	  ++ `count (4 ** n) DELETE 4 ** n = count (4 ** n)`
	      by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT,LESS_EQ_REFL,NOT_LESS]
          ++ RW_TAC std_ss []
	  ++ `Normal (2 pow n) = 2 pow n` by METIS_TAC [extreal_of_num_def,extreal_pow_def]
	  ++ POP_ORW
	  ++ RW_TAC std_ss [GSYM IN_COUNT]
	  ++ METIS_TAC [add_comm,EXTREAL_SUM_IMAGE_IN_IF_ALT])
      ++ CONJ_TAC
      >> (RW_TAC real_ss []
	  >> (`{x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} =
	       {x | Normal (&i / 2 pow n) <= f x /\ f x < Normal (&(i + 1) / 2 pow n)}
	       	  INTER m_space m`
	         by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM]
                     ++ `(&i + 1:extreal) = &(i + 1)`
		     	 by RW_TAC std_ss [extreal_add_def,extreal_of_num_def,REAL_ADD]
                     ++ METIS_TAC [])
	      ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def, subsets_def, space_def,
	      	 	    m_space_def])
	  ++ `{x | x IN m_space m /\ 2 pow n <= f x} =
	      {x | Normal (2 pow n) <= f x} INTER m_space m`
	        by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, CONJ_COMM,
		   	  	  extreal_of_num_def,extreal_pow_def]
          ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def, subsets_def,
	     	        space_def, m_space_def])
      ++ CONJ_TAC
      >> RW_TAC std_ss []
      ++ CONJ_TAC
      >> RW_TAC real_ss [extreal_of_num_def,extreal_pow_def,extreal_le_def,
      	 		 REAL_LT_IMP_LE,POW_POS,REAL_LE_DIV]
      ++ CONJ_TAC
      >> (RW_TAC real_ss [DISJOINT_DEF, IN_COUNT, IN_INTER, EXTENSION, GSPECIFICATION]
         << [REVERSE EQ_TAC
	     >> RW_TAC std_ss [NOT_IN_EMPTY]
   	     ++ RW_TAC real_ss []
	     ++ RW_TAC std_ss [NOT_IN_EMPTY]
	     ++ Cases_on `i < j`
	     >> (`i + 1 <= j` by RW_TAC real_ss []
	         ++ `&(i + 1) / 2:real pow n <= &j / 2 pow n`
		     by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
                 ++ `&(i + 1) / 2 pow n <= &j / 2 pow n`
		     by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,
		     	       	       extreal_div_eq,extreal_lt_eq,extreal_le_def]
                 ++ `&j / 2 pow n <= f x` by METIS_TAC []
                 ++ `(&i + 1) = &(i + 1)`
		      by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	         ++ METIS_TAC [lte_trans,extreal_lt_def])
	     ++ `j < i` by RW_TAC real_ss [LESS_OR_EQ]
	     ++ `j + 1 <= i` by RW_TAC real_ss []
	     ++ `&(j + 1) / 2 pow n <= &i / 2:real pow n`
	     	 by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
	     ++ `&(j + 1) / 2 pow n <= &i / 2 pow n`
	     	 by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,
		    	   	   extreal_div_eq,extreal_lt_eq,extreal_le_def]
             ++ `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	     ++ METIS_TAC [lte_trans,extreal_lt_def],
	     REVERSE EQ_TAC >> RW_TAC std_ss [NOT_IN_EMPTY]
             ++ RW_TAC std_ss []
	     ++ RW_TAC real_ss [NOT_IN_EMPTY]
	     ++ `&(i + 1) <= &(4 ** n):real` by RW_TAC real_ss []
	     ++ FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
 	     ++ `&(i + 1) / 2 pow n <= 4 pow n / 2:real pow n`
	     	 by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
 	     ++ `&(i + 1) / 2 pow n <= 2:real pow n` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
 	     ++ `&(i + 1) / 2 pow n <= 2 pow n`
	     	 by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,
		    	   	   extreal_div_eq,extreal_lt_eq,extreal_le_def]
             ++ `(&i + 1) = &(i + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	     ++ METIS_TAC [le_trans,extreal_lt_def],
	     REVERSE EQ_TAC >> RW_TAC std_ss [NOT_IN_EMPTY]
	     ++ RW_TAC real_ss []
	     ++ RW_TAC std_ss [NOT_IN_EMPTY]
	     ++ `&(j + 1) <= &(4 ** n):real` by RW_TAC real_ss []
	     ++ FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
 	     ++ `&(j + 1) / 2 pow n <= 4:real pow n / 2 pow n`
                 by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
 	     ++ `&(j + 1) / 2 pow n <= 2:real pow n`
                 by  METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
 	     ++ `&(j + 1) / 2 pow n <= 2 pow n`
                 by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,
		    	   	   extreal_div_eq,extreal_lt_eq,extreal_le_def]
             ++ `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
	     ++ METIS_TAC [lte_trans,extreal_lt_def]])
     ++ RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,GSPECIFICATION]
     ++ EQ_TAC
     >> (RW_TAC std_ss []
	 ++ Cases_on `k IN count (4 ** n)`
	 >> FULL_SIMP_TAC std_ss [GSPECIFICATION,lemma_fn_3]
	 ++ FULL_SIMP_TAC std_ss [GSPECIFICATION,lemma_fn_3])
     ++ RW_TAC real_ss [IN_COUNT]
     ++ `2 pow n <= f x \/ ?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\
         f x < (&k + 1) / 2 pow n` by METIS_TAC [lemma_fn_3]
     >> (Q.EXISTS_TAC `4 ** n`
	 ++ RW_TAC real_ss [GSPECIFICATION])
     ++ Q.EXISTS_TAC `k`
     ++ FULL_SIMP_TAC real_ss [IN_COUNT,GSPECIFICATION]
     ++ METIS_TAC [])
  ++ RW_TAC real_ss [pos_simple_fn_integral_def,fn_seq_integral_def]
  ++ `4 ** n + 1 = SUC (4 ** n)` by RW_TAC real_ss []
  ++ ASM_SIMP_TAC std_ss []
  ++ RW_TAC std_ss [COUNT_SUC,IN_COUNT]
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
  ++ `count (4 ** n) DELETE 4 ** n = count (4 ** n)`
      by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT,LESS_EQ_REFL,NOT_LESS]
  ++ RW_TAC std_ss []
  ++ Suff
     `SIGMA
      (\k.
         &k / 2 pow n *
         measure m
           {x | x IN m_space m /\ Normal (&k / 2 pow n) <= f x /\
            f x < (&k + 1) / 2 pow n}) (count (4 ** n)) =
      SIGMA
      (\k.
         (if k < 4 ** n then &k / 2 pow n else 2 pow n) *
         measure m
           (if k < 4 ** n then
              {x | x IN m_space m /\ Normal (&k / 2 pow n) <= f x /\ f x < (&k + 1) / 2 pow n}
            else
              {x | x IN m_space m /\ 2 pow n <= f x})) (count (4 ** n))`
  >> RW_TAC std_ss [REAL_ADD_COMM]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [IN_COUNT]);

(*****************************************************************)


val integral_sequence = store_thm
  ("integral_sequence",``!m f.  (!x. 0 <= f x) /\ measure_space m /\
                        f IN measurable (m_space m,measurable_sets m) Borel
	==> (pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fn_seq m f i)) UNIV))``,	
  RW_TAC std_ss []
  ++ MATCH_MP_TAC lebesgue_monotone_convergence
  ++ RW_TAC std_ss [lemma_fn_sup,lemma_fn_mono_increasing,lemma_fn_upper_bounded,lemma_fn_5]
  ++ METIS_TAC [lemma_fn_in_psfis,IN_MEASURABLE_BOREL_POS_SIMPLE_FN,IN_psfis_eq]);


val measurable_sequence = store_thm
("measurable_sequence",``!m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel ==> 	
	(?fi ri. (!x. mono_increasing (\i. fi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = fn_plus f x)) /\
	(!i. ri i IN psfis m (fi i)) /\
	(!i x. fi i x <= fn_plus f x) /\
        (!i x. 0 <= fi i x) /\
	(pos_fn_integral m (fn_plus f) = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))) /\

	(?gi vi. (!x. mono_increasing (\i. gi i x)) /\
	(!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) UNIV) = fn_minus f x)) /\
	(!i. vi i IN psfis m (gi i)) /\
	(!i x. (gi i) x <= fn_minus f x) /\
        (!i x. 0 <= gi i x) /\
	(pos_fn_integral m (fn_minus f) = sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV)))``,
  REPEAT STRIP_TAC
  >> (Q.EXISTS_TAC `(\n. fn_seq m (fn_plus f) n)`
      ++ Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_plus f) n)`
      ++ CONJ_TAC
      >> RW_TAC std_ss [FN_PLUS_POS,lemma_fn_mono_increasing]
      ++ CONJ_TAC
      >> RW_TAC std_ss [FN_PLUS_POS,lemma_fn_sup]
      ++ CONJ_TAC
      >> FULL_SIMP_TAC std_ss [FN_PLUS_POS,lemma_fn_in_psfis,IN_MEASURABLE_BOREL_FN_PLUS]
      ++ CONJ_TAC
      >> METIS_TAC [FN_PLUS_POS,lemma_fn_upper_bounded]
      ++ CONJ_TAC
      >> METIS_TAC [FN_PLUS_POS,lemma_fn_5]
      ++ METIS_TAC [FN_PLUS_POS,integral_sequence,IN_MEASURABLE_BOREL_FN_PLUS])
  ++ Q.EXISTS_TAC `(\n. fn_seq m (fn_minus f) n)`
  ++ Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_minus f) n)`
  ++ CONJ_TAC
  >> RW_TAC std_ss [FN_MINUS_POS,lemma_fn_mono_increasing]
  ++ CONJ_TAC
  >> RW_TAC std_ss [FN_MINUS_POS,lemma_fn_sup]
  ++ CONJ_TAC
  >> FULL_SIMP_TAC std_ss [FN_MINUS_POS,lemma_fn_in_psfis,IN_MEASURABLE_BOREL_FN_MINUS]
  ++ CONJ_TAC
  >> METIS_TAC [FN_MINUS_POS,lemma_fn_upper_bounded]
  ++ CONJ_TAC
  >> METIS_TAC [FN_MINUS_POS,lemma_fn_5]
  ++ METIS_TAC [FN_MINUS_POS,integral_sequence,IN_MEASURABLE_BOREL_FN_MINUS]);

val pos_fn_integral_add = store_thm
  ("pos_fn_integral_add",``!m f g. measure_space m /\ (!x. 0 <= f x /\ 0 <= g x) /\
            f IN measurable (m_space m,measurable_sets m) Borel /\
            g IN measurable (m_space m,measurable_sets m) Borel  ==>
            (pos_fn_integral m (\x. f x + g x) = pos_fn_integral m f + pos_fn_integral m g)``,
  RW_TAC std_ss []
  ++ `?fi ui.
       (!x. mono_increasing (\i. fi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
       (!i. ui i IN psfis m (fi i)) /\
       (!i x. fi i x <= f x) /\
       (!i x. 0 <= fi i x) /\
       (pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))`
  	  by METIS_TAC [measurable_sequence,FN_PLUS_POS_ID]
  ++ `?gi vi.
       (!x. mono_increasing (\i. gi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) UNIV) = g x)) /\
       (!i. vi i IN psfis m (gi i)) /\
       (!i x. gi i x <= g x) /\
       (!i x. 0 <= gi i x) /\
       (pos_fn_integral m g = sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV))`
  	  by METIS_TAC [measurable_sequence,FN_PLUS_POS_ID]
  ++ `sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV) + sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV) =
      sup (IMAGE (\i. (\n. pos_fn_integral m (fi n)) i + (\n. pos_fn_integral m (gi n)) i) UNIV)`
       by (MATCH_MP_TAC (GSYM sup_add_mono)
           ++ FULL_SIMP_TAC std_ss [pos_fn_integral_pos,ext_mono_increasing_suc,pos_fn_integral_mono])
  ++ FULL_SIMP_TAC std_ss []
  ++ `!i. (\x. fi i x + gi i x) IN  measurable (m_space m,measurable_sets m) Borel`
		by METIS_TAC [IN_MEASURABLE_BOREL_POS_SIMPLE_FN,IN_psfis_eq,psfis_add]
  ++ `!x. mono_increasing (\i. (\i x. fi i x + gi i x) i x)` by FULL_SIMP_TAC std_ss [ext_mono_increasing_def,le_add2]
  ++ `!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x + gi i x) UNIV) = f x + g x)`
       by (RW_TAC std_ss []
           ++ `f x = sup (IMAGE (\i. fi i x) UNIV)` by FULL_SIMP_TAC std_ss []
           ++ `g x = sup (IMAGE (\i. gi i x) UNIV)` by FULL_SIMP_TAC std_ss []
	   ++ POP_ORW ++ POP_ORW
	   ++ FULL_SIMP_TAC std_ss [pos_fn_integral_pos,sup_add_mono,ext_mono_increasing_suc,pos_fn_integral_mono])
  ++ (MP_TAC o Q.SPECL [`m`,`(\x. f x + g x)`,`(\i. (\x. fi i x + gi i x))`]) lebesgue_monotone_convergence
  ++ RW_TAC std_ss []
  ++ Suff `(\i. pos_fn_integral m (fi i) + pos_fn_integral m (gi i)) = (\i. pos_fn_integral m (\x. fi i x + gi i x))`
  >> RW_TAC std_ss [le_add]
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ METIS_TAC [IN_psfis_eq,psfis_add,pos_fn_integral_pos_simple_fn]);

val pos_fn_integral_sum = store_thm
  ("pos_fn_integral_sum",``!m f s. FINITE s /\ measure_space m /\
                           (!i. i IN s ==> (!x. 0 <= f i x)) /\
	(!i. i IN s ==> f i IN measurable (m_space m,measurable_sets m) Borel)
	    ==> (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) =
                 SIGMA (\i. pos_fn_integral m (f i)) s)``,
  Suff `!s:'b->bool. FINITE s ==> (\s:'b->bool. !m f. measure_space m /\ (!i. i IN s ==> (!x. 0 <= f i x)) /\
	   (!i. i IN s ==> f i IN measurable (m_space m,measurable_sets m) Borel)
   	    ==> (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) =
                 SIGMA (\i. pos_fn_integral m (f i)) s)) s`
  >> METIS_TAC []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,pos_fn_integral_zero,DELETE_NON_ELEMENT]
  ++ `SIGMA (\i. pos_fn_integral m (f i)) s = pos_fn_integral m (\x. SIGMA (\i. f i x) s)`
      by METIS_TAC [IN_INSERT]
  ++ POP_ORW
  ++ `(\x. f e x + SIGMA (\i. f i x) s) = (\x. f e x + (\x. SIGMA (\i. f i x) s) x)`
     by METIS_TAC []
  ++ POP_ORW
  ++ MATCH_MP_TAC pos_fn_integral_add
  ++ FULL_SIMP_TAC std_ss [IN_INSERT]
  ++ RW_TAC std_ss []
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_POS]
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SUM
  ++ Q.EXISTS_TAC `f` ++ Q.EXISTS_TAC `s`
  ++ METIS_TAC [measure_space_def]);

val pos_fn_integral_disjoint_sets = store_thm
  ("pos_fn_integral_disjoint_sets",``!m f s t. measure_space m /\ DISJOINT s t /\ s IN measurable_sets m /\ t IN measurable_sets m /\
		f IN measurable (m_space m,measurable_sets m) Borel /\ (!x. 0 <= f x)
		==> (pos_fn_integral m (\x. f x * indicator_fn (s UNION t) x) =
		     pos_fn_integral m (\x. f x * indicator_fn s x) + pos_fn_integral m (\x. f x * indicator_fn t x))``,
  RW_TAC std_ss []
  ++ `(\x. f x * indicator_fn (s UNION t) x) = (\x. (\x. f x * indicator_fn s x) x + (\x. f x * indicator_fn t x) x)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,IN_DISJOINT,IN_UNION,mul_rone,mul_rzero]
           ++ Cases_on `x IN s` >> (RW_TAC std_ss [mul_rone,mul_rzero,add_rzero] ++ METIS_TAC [EXTENSION,IN_DISJOINT])
	   ++ RW_TAC std_ss [mul_rone,mul_rzero,add_lzero])
  ++ POP_ORW
  ++ `!s. s IN measurable_sets m ==> (\x. f x * indicator_fn s x) IN measurable (m_space m,measurable_sets m) Borel`
      by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,measure_space_def,subsets_def,space_def]
  ++ MATCH_MP_TAC pos_fn_integral_add
  ++ FULL_SIMP_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
  ++ RW_TAC std_ss [le_refl,mul_rzero,mul_rone]);

val pos_fn_integral_disjoint_sets_sum = store_thm
  ("pos_fn_integral_disjoint_sets_sum",``!m f s a. FINITE s /\ measure_space m /\
	(!i. i IN s ==> a i IN measurable_sets m) /\ (!x. 0 <= f x) /\
	(!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
	f IN measurable (m_space m,measurable_sets m) Borel
	==> (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
	     SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s)``,

  Suff `!s:'b->bool. FINITE s ==> (\s:'b->bool. !m f a.  measure_space m /\
       (!i. i IN s ==> a i IN measurable_sets m) /\  (!x. 0 <= f x) /\
	(!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
	f IN measurable (m_space m,measurable_sets m) Borel
	==> (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
	     SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s) ) s`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM,IMAGE_EMPTY,BIGUNION_EMPTY,FINITE_INSERT,DELETE_NON_ELEMENT,IN_INSERT,BIGUNION_INSERT,IMAGE_INSERT]
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
           (!x. 0 <= f x) /\ f IN measurable (m_space m,measurable_sets m) Borel ==>
           (pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn s x) +
                                  pos_fn_integral m  (\x. f x * indicator_fn (m_space m DIFF s) x))``,
  RW_TAC std_ss []
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`s`,`m_space m DIFF s`]) pos_fn_integral_disjoint_sets
  ++ RW_TAC std_ss [DISJOINT_DIFF,MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ `s UNION (m_space m DIFF s) = m_space m` by METIS_TAC [UNION_DIFF,MEASURE_SPACE_SUBSET_MSPACE]
  ++ METIS_TAC [pos_fn_integral_mspace]);

val pos_fn_integral_cmul_infty = store_thm
("pos_fn_integral_cmul_infty",``!m s. measure_space m /\ s IN measurable_sets m ==>
     (pos_fn_integral m (\x. PosInf * indicator_fn s x) = PosInf * Normal (measure m s))``,
  RW_TAC std_ss []
  ++ Q.ABBREV_TAC `fi = (\i:num x. &i)`
  ++ Q.ABBREV_TAC `f = (\x. PosInf)`
  ++ `!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)`
       by (RW_TAC std_ss []
           ++ Q.UNABBREV_TAC `fi`
	   ++ Q.UNABBREV_TAC `f`
	   ++ RW_TAC std_ss []
	   ++ Suff `IMAGE (\i. &i) univ(:num) = (\x. ?n. x = &n)`
	   >> RW_TAC std_ss [sup_num]
	   ++ RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_ABS,IN_UNIV])
  ++ `!x. mono_increasing (\i. fi i x)`
       by (RW_TAC std_ss [ext_mono_increasing_def]
           ++ Q.UNABBREV_TAC `fi`
           ++ RW_TAC real_ss [extreal_of_num_def,extreal_le_def])
  ++ `!i x. 0 <= fi i x` by (Q.UNABBREV_TAC `fi` ++ RW_TAC real_ss [extreal_of_num_def,extreal_le_def])
  ++ `!x. 0 <= f x` by METIS_TAC [le_infty]
  ++ `!i. fi i IN measurable (m_space m, measurable_sets m) Borel`
       by (RW_TAC std_ss []
           ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST
	   ++ METIS_TAC [measure_space_def])
  ++ (MP_TAC o Q.SPECL [`m`,`f`,`fi`,`s`]) lebesgue_monotone_convergence_subset
  ++ RW_TAC std_ss []
  ++ Q.UNABBREV_TAC `f`
  ++ Q.UNABBREV_TAC `fi`
  ++ FULL_SIMP_TAC real_ss []
  ++ RW_TAC real_ss [extreal_of_num_def,pos_fn_integral_cmul_indicator]
  ++ RW_TAC std_ss [Once mul_comm,(Once o GSYM) extreal_mul_def]
  ++ `0 <= measure m s` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_def]
  ++ RW_TAC std_ss [sup_cmul]
  ++ Suff `sup (IMAGE (\i. Normal (&i)) UNIV) = PosInf`
  >> METIS_TAC [mul_comm]
  ++ Suff `IMAGE (\i:num. Normal (&i)) UNIV = (\x. ?n. x = &n)`
  >> RW_TAC std_ss [sup_num]
  ++ RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_ABS,IN_UNIV]
  ++ METIS_TAC [extreal_of_num_def]);

val pos_fn_integral_suminf = store_thm
("pos_fn_integral_suminf", ``!m f. measure_space m /\ (!i x. 0 <= f i x) /\
      (!i. f i IN measurable (m_space m,measurable_sets m) Borel) ==>
      (pos_fn_integral m (\x. suminf (\i. f i x)) = suminf (\i. pos_fn_integral m (f i)))``,
  RW_TAC std_ss [ext_suminf_def]
  ++ RW_TAC std_ss [GSYM pos_fn_integral_sum,FINITE_COUNT]
  ++ `(\n. pos_fn_integral m (\x. SIGMA (\i. f i x) (count n))) =
      (\n. pos_fn_integral m ((\n. (\x. SIGMA (\i. f i x) (count n)))n))` by METIS_TAC []
  ++ POP_ORW
  ++ MATCH_MP_TAC lebesgue_monotone_convergence
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC
  >> (RW_TAC std_ss []
      ++ (MATCH_MP_TAC o INST_TYPE [beta |-> ``:num``]) IN_MEASURABLE_BOREL_SUM
      ++ Q.EXISTS_TAC `f`
      ++ Q.EXISTS_TAC `count i`
      ++ RW_TAC std_ss [FINITE_COUNT]
      >> FULL_SIMP_TAC std_ss [measure_space_def]
      ++ METIS_TAC [lt_infty,lte_trans,num_not_infty])
  ++ CONJ_TAC >> RW_TAC std_ss [FINITE_COUNT,EXTREAL_SUM_IMAGE_POS]
  ++ CONJ_TAC
  >> (RW_TAC std_ss [FINITE_COUNT,EXTREAL_SUM_IMAGE_POS,le_sup]
      ++ MATCH_MP_TAC le_trans
      ++ Q.EXISTS_TAC `SIGMA (\i. f i x) (count 1)`
      ++ RW_TAC std_ss [FINITE_COUNT,EXTREAL_SUM_IMAGE_POS]
      ++ POP_ASSUM MATCH_MP_TAC
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [])
  ++ RW_TAC std_ss [ext_mono_increasing_def]
  ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
  ++ RW_TAC std_ss [FINITE_COUNT,SUBSET_DEF,IN_COUNT]
  ++ DECIDE_TAC);

val integral_pos_fn = store_thm
  ("integral_pos_fn",``!m f. measure_space m /\ (!x. 0 <= f x)
                       ==> (integral m f = pos_fn_integral m f)``,
  RW_TAC std_ss [integral_def]
  ++ Suff `(fn_plus f = f) /\ (fn_minus f = (\x. 0))`
  >> RW_TAC std_ss [pos_fn_integral_zero,sub_rzero]
  ++ RW_TAC std_ss [FN_PLUS_POS_ID,FN_MINUS_POS_ZERO]);


(* ------------------------------------------------------------------------- *)
(* Properties of integrable functions                                        *)
(* ------------------------------------------------------------------------- *)

val integrable_pos = store_thm
("integrable_pos",``!m f. measure_space m /\ (!x. 0 <= f x) ==>
         (integrable m f = f IN measurable (m_space m,measurable_sets m) Borel /\
          pos_fn_integral m f <> PosInf)``,
  RW_TAC std_ss [integrable_def,GSYM fn_plus_def, GSYM fn_minus_def,FN_PLUS_POS_ID,FN_MINUS_POS_ZERO,pos_fn_integral_zero,num_not_infty]);

val integrable_infty = store_thm
("integrable_infty",``!m f s. measure_space m /\ integrable m f /\ s IN measurable_sets m /\
           (!x. x IN s ==> (f x = PosInf)) ==> (measure m s = 0)``,
  RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
  ++ (MP_TAC o Q.SPECL [`m`,`fn_plus f`,`s`]) pos_fn_integral_split
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS,DISJOINT_DIFF,FN_PLUS_POS]
  ++ `(\x. fn_plus f x * indicator_fn s x) = (\x. PosInf * indicator_fn s x)`
      by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,fn_plus_def,mul_rzero,mul_rone]
          ++ METIS_TAC [lt_infty,extreal_mul_def,mul_rone,mul_rzero])
  ++ `pos_fn_integral m (\x. PosInf * indicator_fn s x) = PosInf * Normal (measure m s)`
      by METIS_TAC [pos_fn_integral_cmul_infty]
  ++ FULL_SIMP_TAC std_ss []
  ++ `0 <= pos_fn_integral m (\x. fn_plus f x * indicator_fn (m_space m DIFF s) x)`
      by (MATCH_MP_TAC pos_fn_integral_pos
          ++ RW_TAC std_ss [fn_plus_def,indicator_fn_def,mul_rzero,mul_rone,lt_imp_le,le_refl])
  ++ SPOSE_NOT_THEN ASSUME_TAC
  ++ `0 < measure m s` by METIS_TAC [positive_def,MEASURE_SPACE_POSITIVE,REAL_LT_LE]
  ++ `pos_fn_integral m (\x. fn_plus f x * indicator_fn (m_space m DIFF s) x) <> NegInf`
      by METIS_TAC [lt_infty,lte_trans,num_not_infty]
  ++ FULL_SIMP_TAC std_ss [extreal_mul_def,REAL_LT_IMP_NE,add_infty]);

val integrable_infty_null = store_thm
("integrable_infty_null",``!m f. measure_space m /\ integrable m f ==>
     null_set m {x | x IN m_space m /\ (f x = PosInf)}``,
  RW_TAC std_ss []
  ++ Q.ABBREV_TAC `s = {x | x IN m_space m /\ (f x = PosInf)} `
  ++ Suff `s IN measurable_sets m`
  >> (RW_TAC std_ss [null_set_def]
      ++ MATCH_MP_TAC integrable_infty
      ++ Q.EXISTS_TAC `f`
      ++ RW_TAC std_ss []
      ++ Q.UNABBREV_TAC `s`
      ++ FULL_SIMP_TAC std_ss [GSPECIFICATION])
  ++ `f IN measurable (m_space m, measurable_sets m) Borel`
      by FULL_SIMP_TAC std_ss [integrable_def]
  ++ (MP_TAC o Q.SPEC `PosInf` o CONJUNCT2 o UNDISCH o
      REWRITE_RULE [subsets_def, space_def, IN_FUNSET, IN_UNIV] o
      Q.SPECL [`f`,`(m_space m, measurable_sets m)`]) IN_MEASURABLE_BOREL_ALT8
  ++ Suff `s = {x | f x = PosInf} INTER m_space m`
  >> METIS_TAC []
  ++ Q.UNABBREV_TAC `s`
  ++ RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION]
  ++ METIS_TAC []);

val integrable_bounded = store_thm
("integrable_bounded",``!m f g. measure_space m /\ integrable m f /\ g IN measurable (m_space m,measurable_sets m) Borel /\ (!x. abs (g x) <= f x) ==> integrable m g``,
  RW_TAC std_ss [integrable_def,abs_bounds,GSYM fn_plus_def,GSYM fn_minus_def]
  >> (`!x. fn_plus g x <= fn_plus f x`
       by (RW_TAC real_ss [fn_plus_def,lt_imp_le,le_refl]
           ++ METIS_TAC [extreal_lt_def,lte_trans])
       ++ METIS_TAC [pos_fn_integral_mono,FN_PLUS_POS,lt_infty,let_trans])
  ++ `!x. fn_minus g x <= fn_plus f x`
        by (RW_TAC real_ss [fn_minus_def,fn_plus_def,lt_imp_le,le_refl]
            ++ METIS_TAC [let_trans,lt_neg,le_neg,neg_neg,neg_0])
  ++ METIS_TAC [pos_fn_integral_mono,FN_PLUS_POS,FN_MINUS_POS,lt_infty,let_trans]);

val integrable_fn_plus = store_thm
("integrable_fn_plus",``!m f. measure_space m /\ integrable m f ==> integrable m (fn_plus f)``,
  RW_TAC std_ss [integrable_def,GSYM fn_plus_def,FN_PLUS_POS,FN_PLUS_POS_ID,IN_MEASURABLE_BOREL_FN_PLUS,GSYM fn_minus_def,FN_MINUS_POS_ZERO,pos_fn_integral_zero,num_not_infty]
  ++ METIS_TAC []);

val integrable_fn_minus = store_thm
("integrable_fn_minus",``!m f. measure_space m /\ integrable m f ==> integrable m (fn_minus f)``,
  RW_TAC std_ss [integrable_def,GSYM fn_minus_def,FN_MINUS_POS,FN_PLUS_POS_ID,IN_MEASURABLE_BOREL_FN_MINUS,GSYM fn_plus_def,FN_MINUS_POS_ZERO,pos_fn_integral_zero,num_not_infty]
  ++ METIS_TAC []);

val integrable_const = store_thm
  ("integrable_const", ``!m c. measure_space m ==> integrable m (\x. Normal c)``,
  RW_TAC std_ss []
  ++ `(\x. Normal c) IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST ++  METIS_TAC [measure_space_def])
  ++ RW_TAC real_ss [integrable_def, lt_antisym, pos_fn_integral_zero, fn_plus_def, fn_minus_def,
     	    	     num_not_infty, extreal_ainv_def]
  << [METIS_TAC [lt_antisym],
      METIS_TAC [lt_antisym],
      (MP_TAC o Q.SPECL [`m`,`\x. Normal c`]) pos_fn_integral_mspace
      ++ RW_TAC std_ss [lt_imp_le]
      ++ METIS_TAC [pos_fn_integral_cmul_indicator, MEASURE_SPACE_MSPACE_MEASURABLE,
      	 	   extreal_of_num_def, extreal_lt_eq, REAL_LT_IMP_LE, extreal_not_infty],
      (MP_TAC o Q.SPECL [`m`,`\x. Normal (-c)`]) pos_fn_integral_mspace
      ++ `0 < Normal (-c)` by METIS_TAC [lt_neg,neg_0, extreal_ainv_def]
      ++ RW_TAC std_ss [lt_imp_le]
      ++ METIS_TAC [pos_fn_integral_cmul_indicator, MEASURE_SPACE_MSPACE_MEASURABLE,
      	 	   extreal_of_num_def, extreal_lt_eq, REAL_LT_IMP_LE, extreal_not_infty]]);

val integrable_zero = store_thm
  ("integrable_zero", ``!m c. measure_space m ==> integrable m (\x. 0)``,
  RW_TAC std_ss []
  ++ `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST ++  METIS_TAC [measure_space_def])
  ++ RW_TAC real_ss [integrable_def, fn_plus_def, fn_minus_def, lt_refl, neg_0,
     	    	     pos_fn_integral_zero, num_not_infty]);

val integrable_plus_minus = store_thm
  ("integrable_plus_minus", ``!m f. measure_space m ==>
             (integrable m f = f IN measurable (m_space m, measurable_sets m) Borel /\
		integrable m (fn_plus f) /\ integrable m (fn_minus f))``,
  RW_TAC std_ss [integrable_def,GSYM fn_plus_def,GSYM fn_minus_def]
  ++ `fn_plus (fn_minus f) = fn_minus f` by METIS_TAC [FN_MINUS_POS,FN_PLUS_POS_ID]
  ++ `fn_minus (fn_minus f) = (\x. 0)` by METIS_TAC [FN_MINUS_POS,FN_MINUS_POS_ZERO]
  ++ `fn_plus (fn_plus f) = fn_plus f` by METIS_TAC [FN_PLUS_POS,FN_PLUS_POS_ID]
  ++ `fn_minus (fn_plus f) = (\x. 0)` by METIS_TAC [FN_PLUS_POS,FN_MINUS_POS_ZERO]
  ++ `(\x. fn_minus f x) = fn_minus f` by METIS_TAC []
  ++ `(\x. fn_plus f x) = fn_plus f` by METIS_TAC []
  ++ EQ_TAC
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, IN_MEASURABLE_BOREL_FN_MINUS,
     	    	    pos_fn_integral_zero, num_not_infty]);

val integrable_add_pos = store_thm
  ("integrable_add_pos",``!m f g. measure_space m /\ integrable m f /\
  			     integrable m g /\ (!x. 0 <= f x) /\ (!x. 0 <= g x)
			   ==> integrable m (\x. f x + g x)``,
  RW_TAC std_ss []
  ++ `!x. 0 <= (\x. f x + g x) x` by RW_TAC real_ss [le_add]
  ++ `f IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
  ++ `g IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
  ++ `(\x. f x + g x) IN measurable (m_space m,measurable_sets m) Borel`
	by (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD ++ METIS_TAC [measure_space_def])
            ++ Suff `pos_fn_integral m (\x. f x + g x) <> PosInf`
  >> FULL_SIMP_TAC std_ss [integrable_pos]
  ++ RW_TAC std_ss [pos_fn_integral_add]
  ++ METIS_TAC [lt_add2,integrable_pos,lt_infty]);

val integrable_add_lemma = store_thm
  ("integrable_add_lemma",``!m f g. measure_space m /\ integrable m f /\ integrable m g
	   ==> (integrable m (\x. fn_plus f x + fn_plus g x) /\
	        integrable m (\x. fn_minus f x + fn_minus g x))``,
  RW_TAC std_ss []
  ++ METIS_TAC [integrable_add_pos, integrable_plus_minus, FN_PLUS_POS, FN_MINUS_POS]);

val integrable_add = store_thm
  ("integrable_add",``!m f1 f2. measure_space m /\ integrable m f1 /\ integrable m f2
	   ==> integrable m (\x. f1 x + f2 x)``,
  RW_TAC std_ss []
  ++ `(\x. f1 x + f2 x) IN measurable (m_space m, measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
          ++ Q.EXISTS_TAC `f1`
	  ++ Q.EXISTS_TAC `f2`
	  ++ RW_TAC std_ss []
	  ++ METIS_TAC [measure_space_def, integrable_def])
  ++ RW_TAC std_ss [Once integrable_plus_minus]
  >> (MATCH_MP_TAC integrable_bounded
      ++ Q.EXISTS_TAC `(\x. fn_plus f1 x + fn_plus f2 x)`
      ++ RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, integrable_add_lemma]
      ++ METIS_TAC [abs_refl,FN_PLUS_POS,FN_PLUS_ADD_LE])
  ++ MATCH_MP_TAC integrable_bounded
  ++ Q.EXISTS_TAC `(\x. fn_minus f1 x + fn_minus f2 x)`
  ++ RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_MINUS, integrable_add_lemma]
  ++ METIS_TAC [abs_refl, FN_MINUS_POS, FN_MINUS_ADD_LE]);

val integrable_cmul = store_thm
  ("integrable_cmul",``!m f c. measure_space m /\ integrable m f
	   ==> integrable m (\x. Normal c *  f x)``,
  RW_TAC std_ss []
  ++ Cases_on `c = 0`
  >> RW_TAC std_ss [integrable_zero,mul_lzero,GSYM extreal_of_num_def]
  ++ `(\x. Normal c * f x) IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
	  ++ METIS_TAC [measure_space_def,integrable_def])
  ++ RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
  >> (Cases_on `0 <= c`
      >> (`fn_plus (\x. Normal c * f x) = (\x. Normal c * fn_plus f x)`
           by METIS_TAC [FN_PLUS_CMUL]
          ++ POP_ORW
	  ++ FULL_SIMP_TAC std_ss [pos_fn_integral_cmul, integrable_def, FN_PLUS_POS,
	     		   	   GSYM fn_plus_def]
	  ++ METIS_TAC [mul_not_infty])
      ++ `c < 0` by METIS_TAC [real_lt]
      ++  `fn_plus (\x. Normal c * f x) = (\x. -Normal c * fn_minus f x)`
      	    by METIS_TAC [FN_PLUS_CMUL,REAL_LT_IMP_LE]
      ++ POP_ORW
      ++ RW_TAC std_ss [extreal_ainv_def]
      ++ `0 <= -c` by METIS_TAC [REAL_LT_NEG, REAL_NEG_0, REAL_LT_IMP_LE]
      ++ FULL_SIMP_TAC std_ss [pos_fn_integral_cmul, integrable_def, FN_MINUS_POS,
      	 	       	       GSYM fn_minus_def]
      ++ METIS_TAC [mul_not_infty])
  ++ Cases_on `0 <= c`
  >> (`fn_minus (\x. Normal c * f x) = (\x. Normal c * fn_minus f x)` by METIS_TAC [FN_MINUS_CMUL]
     ++ POP_ORW
     ++ FULL_SIMP_TAC std_ss [pos_fn_integral_cmul, integrable_def, FN_MINUS_POS,
     		      	      GSYM fn_minus_def]
     ++ METIS_TAC [mul_not_infty])
  ++ `c < 0` by METIS_TAC [real_lt]
  ++  `fn_minus (\x. Normal c * f x) = (\x. -Normal c * fn_plus f x)`
        by METIS_TAC [FN_MINUS_CMUL,REAL_LT_IMP_LE]
  ++ POP_ORW
  ++ RW_TAC std_ss [extreal_ainv_def]
  ++ `0 <= -c` by METIS_TAC [REAL_LT_IMP_LE, REAL_LE_NEG, REAL_NEG_0]
  ++ RW_TAC std_ss [pos_fn_integral_cmul, FN_PLUS_POS]
  ++ METIS_TAC [mul_not_infty, integrable_def]);

val integrable_sub = store_thm
  ("integrable_sub",``!m f1 f2. measure_space m /\ integrable m f1 /\ integrable m f2
	   ==> integrable m (\x. f1 x - f2 x)``,
  RW_TAC std_ss []
  ++ `(\x. f1 x - f2 x) = (\x. f1 x + (\x. -f2 x) x)`
      by RW_TAC std_ss [FUN_EQ_THM, extreal_sub_add]
  ++ POP_ORW
  ++ MATCH_MP_TAC integrable_add
  ++ RW_TAC std_ss []
  ++ `(\x. -f2 x) = (\x. Normal (-1) * f2 x)`
      by METIS_TAC [FUN_EQ_THM, neg_minus1, extreal_of_num_def, extreal_ainv_def]
  ++ POP_ORW
  ++ METIS_TAC [integrable_cmul]);

val integrable_indicator = store_thm
("integrable_indicator",``!m s. measure_space m /\ s IN measurable_sets m ==>
   integrable m (indicator_fn s)``,
  RW_TAC std_ss []
  ++ `!x. 0 <= indicator_fn s x` by METIS_TAC [indicator_fn_def,le_refl,le_01]
  ++ RW_TAC std_ss [integrable_pos,pos_fn_integral_indicator]
  ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
  ++ METIS_TAC [measure_space_def,subsets_def,space_def]);

val integrable_not_infty = store_thm
("integrable_not_infty",``!m f. measure_space m /\ integrable m f /\ (!x. 0 <= f x) ==>
		    ?g. integrable m g /\ (!x. 0 <= g x) /\
		       	(!x. x IN m_space m ==> g x <> PosInf) /\
			(integral m f = integral m g)``,
  RW_TAC std_ss [integral_pos_fn,integrable_def,GSYM fn_plus_def,GSYM fn_minus_def]
  ++ Q.ABBREV_TAC `g = (\x. if f x = PosInf then 0 else f x)`
  ++ Q.EXISTS_TAC `g`
  ++ `!x. 0 <= g x` by METIS_TAC [le_refl]
  ++ `!x. g x <= f x` by METIS_TAC [le_refl,le_infty]
  ++ `!x. g x <> PosInf` by METIS_TAC [num_not_infty]
  ++ `g IN measurable (m_space m,measurable_sets m) Borel`
      by (RW_TAC std_ss [IN_MEASURABLE_BOREL, space_def, subsets_def, IN_FUNSET, IN_UNIV]
          >> METIS_TAC [measure_space_def]
   	  ++ Cases_on `c <= 0`
	  >> (`{x | g x < c} = {}`
               by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]
	       	   ++ METIS_TAC [le_trans, extreal_lt_def])
	      ++ METIS_TAC [INTER_EMPTY, MEASURE_SPACE_EMPTY_MEASURABLE])
          ++ `{x | g x < c} = {x | f x < c} UNION {x | f x = PosInf}`
                by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION]
	            ++ Q.UNABBREV_TAC `g`
	  	    ++ RW_TAC std_ss []
		    ++ METIS_TAC [extreal_lt_def])
          ++ RW_TAC std_ss [Once INTER_COMM, UNION_OVER_INTER]
	  ++ MATCH_MP_TAC MEASURE_SPACE_UNION
	  ++ RW_TAC std_ss []
	  ++ METIS_TAC [(REWRITE_RULE [space_def, subsets_def] o
	                Q.SPECL [`f`,`(m_space m, measurable_sets m)`])
				IN_MEASURABLE_BOREL_ALL, integrable_def, INTER_COMM])
  ++ CONJ_TAC
  >> (RW_TAC std_ss []
      >> (`!x. fn_plus g x <= fn_plus f x` by METIS_TAC [FN_PLUS_POS_ID]
          ++ METIS_TAC [pos_fn_integral_mono,lt_infty,let_trans,FN_PLUS_POS])
      ++ RW_TAC std_ss [FN_MINUS_POS_ZERO,pos_fn_integral_zero,num_not_infty])
  ++ RW_TAC std_ss []
  ++ Q.ABBREV_TAC `h = (\x. f x - g x)`
  ++ `h IN measurable (m_space m,measurable_sets m) Borel`
       by (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
           ++ METIS_TAC [space_def,lt_infty,lte_trans,measure_space_def,num_not_infty])
  ++ `!x. f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty]
  ++ `f = (\x. g x + h x)`
       by (RW_TAC std_ss [FUN_EQ_THM]
           ++ Cases_on `f x` ++ Cases_on `g x` ++ Cases_on `h x`
	   ++ RW_TAC std_ss [extreal_add_def,extreal_sub_def]
	   ++ METIS_TAC [lt_infty,num_not_infty, lte_trans, extreal_sub_def, extreal_not_infty,
	      		 extreal_add_def, REAL_EQ_SUB_LADD, REAL_ADD_COMM, extreal_11])
  ++ `!x. 0 <= h x` by  METIS_TAC [extreal_sub_def,le_infty,le_refl,extreal_of_num_def,sub_refl]
  ++ (MP_TAC o Q.SPECL [`m`,`g`,`h`]) pos_fn_integral_add
  ++ RW_TAC std_ss []
  ++ Suff `pos_fn_integral m h = 0`
  >> RW_TAC std_ss [add_rzero,integral_pos_fn]
  ++ Q.ABBREV_TAC `f = (\x. g x + h x)`
  ++ `integrable m f` by RW_TAC std_ss [integrable_def,GSYM fn_plus_def,GSYM fn_minus_def]
  ++ `null_set m {x | x IN m_space m /\ (f x = PosInf)}` by METIS_TAC [integrable_infty_null]
  ++ (MP_TAC o Q.SPECL [`m`,`h`,`{x | x IN m_space m /\ (f x = PosInf)}`]) pos_fn_integral_split
  ++ FULL_SIMP_TAC std_ss [null_set_def]
  ++ RW_TAC std_ss []
  ++ `(\x. h x * indicator_fn {x | x IN m_space m /\ (f x = PosInf)} x) =
      (\x. PosInf * indicator_fn {x | x IN m_space m /\ (f x = PosInf)} x)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,mul_rzero,mul_rone,GSPECIFICATION]
           ++ Q.UNABBREV_TAC `h`
	   ++ RW_TAC std_ss [mul_rzero, mul_rone]
	   ++ METIS_TAC [extreal_sub_def,extreal_cases])
  ++ RW_TAC std_ss [pos_fn_integral_cmul_infty,mul_rzero,add_lzero]
  ++ `(\x. h x * indicator_fn (m_space m DIFF {x | x IN m_space m /\ (f x = PosInf)}) x) =
      (\x. 0)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,mul_rzero,mul_rone,GSPECIFICATION,IN_DIFF]
           ++ Q.UNABBREV_TAC `h`
	   ++ RW_TAC std_ss [mul_rzero, mul_rone]
	   ++ METIS_TAC [sub_refl])
  ++ RW_TAC std_ss [pos_fn_integral_zero, GSYM extreal_of_num_def,mul_rzero,add_rzero]);


val integrable_not_infty_alt = store_thm
("integrable_not_infty_alt",``!m f. measure_space m /\ integrable m f /\ (!x. 0 <= f x) ==>
    			integrable m (\x. if f x = PosInf then 0 else f x) /\
    			(integral m f = integral m (\x. if f x = PosInf then 0 else f x))``,
  NTAC 3 STRIP_TAC
  ++ Q.ABBREV_TAC `g = (\x. if f x = PosInf then 0 else f x)`
  ++ `!x. 0 <= g x` by METIS_TAC [le_refl]
  ++ `!x. g x <= f x` by METIS_TAC [le_refl, le_infty]
  ++ `!x. g x <> PosInf` by METIS_TAC [num_not_infty]
  ++ `!x. g x <> NegInf` by METIS_TAC [lt_infty,lte_trans, num_not_infty]
  ++ `!x. f x <> NegInf` by METIS_TAC [lt_infty,lte_trans, num_not_infty]
  ++ `g IN measurable (m_space m,measurable_sets m) Borel`
      by (RW_TAC std_ss [IN_MEASURABLE_BOREL, space_def, subsets_def, IN_FUNSET, IN_UNIV]
          >> METIS_TAC [measure_space_def]
   	  ++ Cases_on `c <= 0`
	  >> (`{x | g x < c} = {}` by
	        (RW_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY]
	         ++ METIS_TAC [le_trans,extreal_lt_def])
	      ++ METIS_TAC [INTER_EMPTY,MEASURE_SPACE_EMPTY_MEASURABLE])
          ++ `{x | g x < c} = {x | f x < c} UNION {x | f x = PosInf}`
                by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_UNION]
	            ++ Q.UNABBREV_TAC `g`
	  	    ++ RW_TAC std_ss []
		    ++ METIS_TAC [extreal_lt_def])
          ++ RW_TAC std_ss [Once INTER_COMM, UNION_OVER_INTER]
	  ++ MATCH_MP_TAC MEASURE_SPACE_UNION
	  ++ RW_TAC std_ss []
	  ++ METIS_TAC [(REWRITE_RULE [space_def,subsets_def] o
	     	        Q.SPECL [`f`,`(m_space m, measurable_sets m)`])
			    IN_MEASURABLE_BOREL_ALL,integrable_def, INTER_COMM])
  ++ `integrable m g`
      by (RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
          >> (`!x. fn_plus g x <= fn_plus f x` by METIS_TAC [FN_PLUS_POS_ID]
	      ++ FULL_SIMP_TAC std_ss [integrable_def, GSYM fn_plus_def]
              ++ METIS_TAC [pos_fn_integral_mono, lt_infty, let_trans, FN_PLUS_POS])
	  ++ RW_TAC std_ss [FN_MINUS_POS_ZERO, pos_fn_integral_zero, num_not_infty])
  ++ RW_TAC std_ss []
  ++  Q.ABBREV_TAC `h = (\x. f x - g x)`
  ++ `h IN measurable (m_space m,measurable_sets m) Borel`
       by (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
           ++ METIS_TAC [space_def, lt_infty, lte_trans, measure_space_def, num_not_infty,
	      		 integrable_def])
  ++ RW_TAC std_ss [integral_pos_fn]
  ++ `f = (\x. g x + h x)`
       by (RW_TAC std_ss [FUN_EQ_THM]
           ++ Cases_on `f x` ++ Cases_on `g x` ++ Cases_on `h x`
	   ++ RW_TAC std_ss [extreal_add_def, extreal_sub_def]
	   ++ METIS_TAC [lt_infty, num_not_infty, lte_trans, extreal_sub_def, extreal_not_infty,
	      		 extreal_add_def, REAL_EQ_SUB_LADD, REAL_ADD_COMM, extreal_11])
  ++ `!x. 0 <= h x`
      by  METIS_TAC [extreal_sub_def, le_infty, le_refl, extreal_of_num_def, sub_refl]
  ++ (MP_TAC o Q.SPECL [`m`,`g`,`h`]) pos_fn_integral_add
  ++ RW_TAC std_ss []
  ++ Suff `pos_fn_integral m h = 0`
  >> RW_TAC std_ss [add_rzero]
  ++ Q.ABBREV_TAC `f = (\x. g x + h x)`
  ++ `integrable m f` by RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
  ++ `null_set m {x | x IN m_space m /\ (f x = PosInf)}` by METIS_TAC [integrable_infty_null]
  ++ (MP_TAC o Q.SPECL [`m`,`h`,`{x | x IN m_space m /\ (f x = PosInf)}`]) pos_fn_integral_split
  ++ FULL_SIMP_TAC std_ss [null_set_def]
  ++ RW_TAC std_ss []
  ++ `(\x. h x * indicator_fn {x | x IN m_space m /\ (f x = PosInf)} x) =
      (\x. PosInf * indicator_fn {x | x IN m_space m /\ (f x = PosInf)} x)`
       by (RW_TAC std_ss [FUN_EQ_THM, indicator_fn_def, mul_rzero, mul_rone, GSPECIFICATION]
           ++ Q.UNABBREV_TAC `h`
	   ++ RW_TAC std_ss [mul_rzero, mul_rone]
	   ++ METIS_TAC [extreal_sub_def, extreal_cases])
  ++ RW_TAC std_ss [pos_fn_integral_cmul_infty, mul_rzero, add_lzero]
  ++ `(\x. h x * indicator_fn (m_space m DIFF {x | x IN m_space m /\ (f x = PosInf)}) x) =
      (\x. 0)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def, mul_rzero, mul_rone, GSPECIFICATION,
       	  	  	  IN_DIFF]
           ++ Q.UNABBREV_TAC `h`
	   ++ RW_TAC std_ss [mul_rzero, mul_rone]
	   ++ METIS_TAC [sub_refl])
  ++ RW_TAC std_ss [pos_fn_integral_zero, GSYM extreal_of_num_def, mul_rzero, add_rzero]);

val integrable_not_infty_alt2 = store_thm
("integrable_not_infty_alt2",``!m f. measure_space m /\ integrable m f /\ (!x. 0 <= f x) ==>
	integrable m (\x. if f x = PosInf then 0 else f x) /\
	(pos_fn_integral m f = pos_fn_integral m (\x. if f x = PosInf then 0 else f x))``,
  RW_TAC std_ss []
  >> RW_TAC std_ss [integrable_not_infty_alt]
  ++ `!x. 0 <= (\x. if f x = PosInf then 0 else f x) x` by METIS_TAC [le_refl]
  ++ FULL_SIMP_TAC std_ss [GSYM integral_pos_fn]
  ++ METIS_TAC [integrable_not_infty_alt]);

val integrable_not_infty_alt3 = store_thm
("integrable_not_infty_alt3",``!m f. measure_space m /\ integrable m f ==>
    integrable m (\x. if ((f x = NegInf) \/ (f x = PosInf)) then 0 else f x) /\
   (integral m f = integral m (\x. if ((f x = NegInf) \/ (f x = PosInf)) then 0 else f x))``,
  NTAC 3 STRIP_TAC
  ++ `fn_plus (\x. if (f x = NegInf) \/ (f x = PosInf) then 0 else f x) =
      (\x. if fn_plus f x = PosInf then 0 else fn_plus f x)`
      by (RW_TAC std_ss [fn_plus_def,FUN_EQ_THM]
	  ++ Cases_on `f x` ++ METIS_TAC [lt_infty])
  ++ `fn_minus (\x. if (f x = NegInf) \/ (f x = PosInf) then 0 else f x) =
      (\x. if fn_minus f x = PosInf then 0 else fn_minus f x)`	
      by (RW_TAC std_ss [fn_minus_def,FUN_EQ_THM]
          ++ Cases_on `f x`
	  ++ METIS_TAC [lt_infty, lt_refl, extreal_ainv_def, extreal_not_infty])
  ++ `integrable m (fn_plus f)` by RW_TAC std_ss [integrable_fn_plus]
  ++ `integrable m (fn_minus f)` by RW_TAC std_ss [integrable_fn_minus]
  ++ `integrable m (\x. if fn_plus f x = PosInf then 0 else fn_plus f x)`
       by METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS, integrable_pos]
  ++ `integrable m (\x. if fn_minus f x = PosInf then 0 else fn_minus f x)`
       by METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS, integrable_pos]
  ++ REVERSE (RW_TAC std_ss [integral_def, integrable_def, GSYM fn_plus_def, GSYM fn_minus_def])
  << [METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS],
      METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS, integrable_pos],
      METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS, integrable_pos],
      `(\x. if (f x = NegInf) \/ (f x = PosInf) then 0 else f x) =
       (\x. (\x. if fn_plus f x = PosInf then 0 else fn_plus f x) x -
       (\x. if fn_minus f x = PosInf then 0 else fn_minus f x) x)`
         by (RW_TAC std_ss [FUN_EQ_THM,fn_plus_def,fn_minus_def]
	     ++ Cases_on `f x`
	     ++ RW_TAC std_ss [lt_infty, extreal_sub_def, extreal_ainv_def ,extreal_not_infty,
	     	       	       num_not_infty, sub_rzero]
             ++ METIS_TAC [lt_infty, extreal_not_infty, num_not_infty, extreal_ainv_def,
	     		   lt_antisym, sub_lzero, neg_neg, extreal_lt_def, le_antisym])
      ++ POP_ORW
      ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
      ++ Q.EXISTS_TAC `(\x. if fn_plus f x = PosInf then 0 else fn_plus f x)`
      ++ Q.EXISTS_TAC `(\x. if fn_minus f x = PosInf then 0 else fn_minus f x)`
      ++ FULL_SIMP_TAC std_ss [integrable_def,measure_space_def]]);


(* ------------------------------------------------------------------------- *)
(* Properties of Integral                                                    *)
(* ------------------------------------------------------------------------- *)

val integral_indicator = store_thm
("integral_indicator",``!m s. measure_space m /\ s IN measurable_sets m ==>
         (integral m (indicator_fn s) = Normal (measure m s))``,
  RW_TAC std_ss []
  ++ `!x. 0 <= indicator_fn s x`
      by RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_refl, le_01]
  ++ METIS_TAC [pos_fn_integral_indicator, integral_pos_fn]);

val integral_add_lemma = store_thm
  ("integral_add_lemma", ``!m f f1 f2. measure_space m /\
        integrable m f /\ integrable m f1 /\ integrable m f2  /\
	(f = (\x. f1 x - f2 x)) /\ (!x. 0 <= f1 x) /\  (!x. 0 <= f2 x)
	==> (integral m f = pos_fn_integral m f1 -  pos_fn_integral m f2)``,
  REPEAT STRIP_TAC
  ++ REWRITE_TAC [integral_def]
  ++ Q.ABBREV_TAC `h1 = (\x. fn_plus f x + f2 x)`
  ++ Q.ABBREV_TAC `h2 = (\x. fn_minus f x + f1 x)`
  ++ `!x. f1 x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty]
  ++ `!x. f2 x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty]
  ++ `h1 = h2`
      by (Q.UNABBREV_TAC `h1` ++ Q.UNABBREV_TAC `h2`
          ++ RW_TAC real_ss [FUN_EQ_THM, fn_plus_def, fn_minus_def]
  	  ++ Cases_on `0 < f1 x - f2 x`
	  >> (RW_TAC std_ss []
	      ++ Cases_on `f1 x` ++ Cases_on `f2 x`
	      ++ FULL_SIMP_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def,
	      	 	       	       extreal_11,add_lzero]
	      ++ METIS_TAC [lt_antisym,lt_infty,REAL_SUB_ADD])
	  ++ RW_TAC std_ss [add_lzero]
	  ++ Cases_on `f1 x` ++ Cases_on `f2 x`
          ++ FULL_SIMP_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def, extreal_11,
	     		   	   add_lzero]
  	  ++ METIS_TAC [real_sub, REAL_SUB_SUB2, REAL_ADD_COMM, lt_infty, lt_antisym,
	     	        extreal_lt_def, extreal_of_num_def, REAL_LE_ANTISYM, extreal_le_def,
			REAL_SUB_0])
  ++ `pos_fn_integral m h1 = pos_fn_integral m h2` by METIS_TAC []
  ++ `pos_fn_integral m h1 =
      pos_fn_integral m (fn_plus f) + pos_fn_integral m f2`
      by (Q.UNABBREV_TAC `h1`
  	  ++ MATCH_MP_TAC pos_fn_integral_add
	  ++ FULL_SIMP_TAC std_ss [integrable_def]
	  ++ RW_TAC std_ss [le_refl, lt_le, IN_MEASURABLE_BOREL_FN_PLUS,FN_PLUS_POS])
  ++ `pos_fn_integral m h2 =
      pos_fn_integral m (fn_minus f) + pos_fn_integral m f1`
      by (Q.UNABBREV_TAC `h2`
	  ++ MATCH_MP_TAC pos_fn_integral_add
	  ++ METIS_TAC [FN_MINUS_POS,IN_MEASURABLE_BOREL_FN_MINUS,integrable_def])
  ++ `pos_fn_integral m f2 <> PosInf` by METIS_TAC [integrable_pos]
  ++ `pos_fn_integral m (fn_minus f) <> PosInf`
      by METIS_TAC [integrable_def]
  ++ `pos_fn_integral m f2 <> NegInf`
      by METIS_TAC [pos_fn_integral_pos,lt_infty,lte_trans,num_not_infty]
  ++ `0 <= pos_fn_integral m (fn_minus f)`
      by METIS_TAC [pos_fn_integral_pos,FN_MINUS_POS]
  ++ `pos_fn_integral m (fn_minus f) <> NegInf`
      by METIS_TAC [lt_infty, lte_trans, num_not_infty]
  ++ METIS_TAC [eq_add_sub_switch]);

val integral_add = store_thm
  ("integral_add", ``!m f g. measure_space m /\ integrable m f /\ integrable m g
	==> (integral m (\x. f x + g x) = integral m f + integral m g)``,
  RW_TAC std_ss []
  ++ `integral m (\x. f x + g x) = pos_fn_integral m (\x. fn_plus f x + fn_plus g x) -
     	       	      	      	   pos_fn_integral m (\x. fn_minus f x + fn_minus g x)`
      by (MATCH_MP_TAC integral_add_lemma
	  ++ `!x. 0 <= fn_minus f x + fn_minus g x` by METIS_TAC [FN_MINUS_POS,le_add]
	  ++ `!x. 0 <= fn_plus f x + fn_plus g x` by METIS_TAC [FN_PLUS_POS,le_add]
	  ++ RW_TAC std_ss [FUN_EQ_THM, add_rzero, add_lzero, lt_imp_le, le_refl, le_add,
	     	    	    integrable_add]
	  << [METIS_TAC [integrable_fn_plus,integrable_add],
	      METIS_TAC [integrable_fn_minus,integrable_add],
	      RW_TAC std_ss [fn_plus_def, fn_minus_def, add_rzero, sub_rzero, add_lzero, le_refl,
	      	             lt_imp_le, lt_antisym, add_comm, sub_lzero, sub_rneg, neg_neg, neg_0]
	      ++ METIS_TAC [lt_antisym, sub_rneg, extreal_lt_def, le_antisym, add_rzero, add_comm,
	      	 	    extreal_sub_add, sub_lneg, neg_neg,lt_infty,lte_trans,num_not_infty]])
  ++ `pos_fn_integral m (\x. fn_plus f x + fn_plus g x) =
      pos_fn_integral m (fn_plus f) + pos_fn_integral m (fn_plus g)`
      by METIS_TAC [pos_fn_integral_add, IN_MEASURABLE_BOREL_FN_PLUS, FN_PLUS_POS, integrable_def]
  ++ `pos_fn_integral m (\x. fn_minus f x + fn_minus g x) =
      pos_fn_integral m (fn_minus f) + pos_fn_integral m (fn_minus g)`
      by METIS_TAC [pos_fn_integral_add, IN_MEASURABLE_BOREL_FN_MINUS,FN_MINUS_POS,integrable_def]
  ++ RW_TAC std_ss [integral_def, GSYM fn_plus_def, GSYM fn_minus_def]
  ++ MATCH_MP_TAC (GSYM add2_sub2)
  ++ METIS_TAC [integrable_def, FN_PLUS_POS, FN_MINUS_POS, pos_fn_integral_pos, lt_infty,
     	        lte_trans,num_not_infty]);


val integral_cmul = store_thm
("integral_cmul",``!m f c. measure_space m /\ integrable m f ==>
         (integral m (\x. Normal c * f x) = Normal c * integral m f)``,
  RW_TAC std_ss [integral_def,GSYM fn_plus_def,GSYM fn_minus_def]
  ++ `(\x. fn_plus f x) = fn_plus f` by METIS_TAC []
  ++ `(\x. fn_minus f x) = fn_minus f` by METIS_TAC []
  ++ Cases_on `0 <= c`
  >> (RW_TAC std_ss [FN_PLUS_CMUL, FN_MINUS_CMUL, FN_PLUS_POS, FN_MINUS_POS, pos_fn_integral_cmul]
      ++ MATCH_MP_TAC (GSYM sub_ldistrib)
      ++ FULL_SIMP_TAC std_ss [extreal_not_infty, integrable_def, GSYM fn_plus_def,
      	 	       	       GSYM fn_minus_def]
      ++ METIS_TAC [pos_fn_integral_pos, FN_PLUS_POS, FN_MINUS_POS, lt_infty, lte_trans,
      	 	    extreal_of_num_def])
  ++ `c <= 0` by METIS_TAC [REAL_LT_IMP_LE,real_lt]
  ++ `0 <= -c` by METIS_TAC [REAL_LE_NEG,REAL_NEG_0]
  ++ RW_TAC std_ss [FN_PLUS_CMUL, FN_MINUS_CMUL, FN_PLUS_POS, FN_MINUS_POS, pos_fn_integral_cmul,
     	    	    extreal_ainv_def]
  ++ RW_TAC std_ss [Once (GSYM eq_neg), GSYM mul_lneg, extreal_ainv_def]
  ++ FULL_SIMP_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
  ++ `pos_fn_integral m (fn_plus f) <> NegInf`
      by METIS_TAC [pos_fn_integral_pos, FN_PLUS_POS, lt_infty, lte_trans, extreal_of_num_def]
  ++ `pos_fn_integral m (fn_minus f) <> NegInf`
      by METIS_TAC [pos_fn_integral_pos, FN_MINUS_POS, lt_infty, lte_trans, extreal_of_num_def]
  ++ FULL_SIMP_TAC std_ss [GSYM sub_ldistrib, extreal_not_infty, GSYM mul_rneg]
  ++ METIS_TAC [neg_sub]);

val integral_cmul_indicator = store_thm
("integral_cmul_indicator",``!m s c. measure_space m /\ s IN measurable_sets m ==>
         (integral m (\x. Normal c * indicator_fn s x) = Normal (c * measure m s))``,
  METIS_TAC [integral_cmul, integral_indicator, integrable_indicator, extreal_mul_def]);

val integral_zero = store_thm
("integral_zero",``!m. measure_space m ==> (integral m (\x. 0) = 0)``,
  RW_TAC std_ss [integral_def, lt_refl, pos_fn_integral_zero, sub_lzero, neg_0,
  	 	 fn_plus_def, fn_minus_def]);

val integral_mspace = store_thm
  ("integral_mspace", ``!m f. measure_space m ==>
   	       (integral m f = integral m (\x. f x * indicator_fn (m_space m) x))``,
  RW_TAC std_ss [integral_def]
  ++ `(fn_plus (\x. f x * indicator_fn (m_space m) x)) =
      (\x. fn_plus f x * indicator_fn (m_space m) x)`
       by (RW_TAC std_ss [indicator_fn_def, fn_plus_def, FUN_EQ_THM]
	  ++ METIS_TAC [mul_rone, mul_lone, mul_rzero, mul_lzero])
  ++ `fn_minus (\x. f x * indicator_fn (m_space m) x) =
      (\x. fn_minus f x * indicator_fn (m_space m) x)`
       by (RW_TAC std_ss [indicator_fn_def, fn_minus_def, FUN_EQ_THM]
	  ++ METIS_TAC [neg_0, neg_eq0, mul_rone, mul_lone, mul_rzero, mul_lzero])
  ++ RW_TAC std_ss []
  ++ METIS_TAC [pos_fn_integral_mspace, FN_PLUS_POS, FN_MINUS_POS]);

val integral_mono = store_thm
  ("integral_mono",
   ``!m f1 f2. measure_space m /\ (!t. t IN m_space m ==> f1 t <= f2 t) ==>
   	       (integral m f1 <= integral m f2)``, 	
  RW_TAC std_ss []
  ++ ONCE_REWRITE_TAC [(UNDISCH o Q.SPECL [`m`,`f`]) integral_mspace]
  ++ RW_TAC std_ss [integral_def]
  ++ `!x. (fn_plus (\x. f1 x * indicator_fn (m_space m) x)) x <=
          (fn_plus (\x. f2 x * indicator_fn (m_space m) x)) x`
       by (RW_TAC real_ss [fn_plus_def, lt_imp_le, le_refl, indicator_fn_def, mul_rzero, mul_rone]
           ++ METIS_TAC [extreal_lt_def, mul_rone, lt_imp_le, le_trans])
  ++ `!x. (fn_minus (\x. f2 x * indicator_fn (m_space m) x)) x <=
          (fn_minus (\x. f1 x * indicator_fn (m_space m) x)) x`
       by (RW_TAC real_ss [fn_minus_def, lt_imp_le, le_refl, indicator_fn_def, mul_rzero,
       	  	  	   mul_rone, neg_0, neg_eq0, le_neg]
           ++ METIS_TAC [mul_rone, extreal_lt_def, le_trans, lt_neg, lt_imp_le, neg_0])
  ++ METIS_TAC [pos_fn_integral_mono, FN_PLUS_POS, FN_MINUS_POS, le_neg,le_add2,extreal_sub_add]);

val finite_space_integral_reduce = store_thm
  ("finite_space_integral_reduce",
   ``!m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel /\
   	   (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf) /\ FINITE (m_space m)
              ==> (integral m f = finite_space_integral m f)``,
  REPEAT STRIP_TAC
  ++ `?c1 n. BIJ c1 (count n) (IMAGE f (m_space m))`
       by RW_TAC std_ss [GSYM FINITE_BIJ_COUNT, IMAGE_FINITE]
  ++ `?c. !i. (i IN count n ==> (c1 i = Normal (c i)))`
       by (Q.EXISTS_TAC `(\i. @r. c1 i = Normal r)`
	   ++ RW_TAC std_ss []
           ++ SELECT_ELIM_TAC
	   ++ RW_TAC std_ss []
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	   ++ `?t. (c1 i = f t) /\ t IN m_space m` by METIS_TAC []
	   ++ METIS_TAC [extreal_cases])
  ++ `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
  ++ `!i j. (i <> j) /\ (i IN count n) /\ (j IN count n)
        ==> DISJOINT (PREIMAGE f {Normal (c i)})(PREIMAGE f {Normal (c j)})`
        by (RW_TAC std_ss [DISJOINT_DEF,EXTENSION,IN_PREIMAGE,IN_INTER,NOT_IN_EMPTY,IN_SING]
            ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	    ++ METIS_TAC [])
  ++ `!i. PREIMAGE f {Normal (c i)} INTER m_space m IN measurable_sets m`
      by (RW_TAC std_ss []
          ++ `PREIMAGE f {Normal (c i)} = {x | f x = Normal (c i)}`
              by RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION,IN_SING]
          ++ METIS_TAC [IN_MEASURABLE_BOREL_ALL, integrable_def, space_def, m_space_def,
	     	        subsets_def, measurable_sets_def])
  ++ `pos_simple_fn m (fn_plus f)
	(count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m)
	(\i. if 0 <= (c i) then c i else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT,FN_PLUS_POS,FN_MINUS_POS]
   << [REVERSE (RW_TAC real_ss [fn_plus_def])
       >> (FULL_SIMP_TAC std_ss [extreal_lt_def,indicator_fn_def,IN_INTER]
           ++ (MP_TAC o Q.SPEC `(\i. Normal (if 0 <= c i then c i else 0) *
	      	      	            if t IN PREIMAGE f {Normal (c i)} then 1 else 0)` o
               UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IN_IF
	   ++ RW_TAC std_ss []
	   ++ POP_ORW
	   ++ Suff `(\x. if x IN count n then Normal (if 0 <= c x then c x else 0) *
                       if t IN PREIMAGE f {Normal (c x)} then 1 else 0 else 0) =
                    (\x. 0)`
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
	   ++ RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `~(x IN count n)`
	   >> RW_TAC std_ss []
	   ++ REVERSE (RW_TAC std_ss [mul_rone,mul_rzero])
	   >> RW_TAC std_ss [extreal_of_num_def]
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_COUNT, IN_IMAGE,
	      		    	    IN_PREIMAGE, IN_SING]
	   ++ METIS_TAC [le_antisym, extreal_le_def, extreal_of_num_def])
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (f t = Normal (c i))` by METIS_TAC []
       ++ `count n = i INSERT ((count n) DELETE i)`
	    by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ REVERSE (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
       	  	   mul_lzero, DELETE_DELETE, add_lzero])
       >> METIS_TAC [extreal_of_num_def, extreal_lt_eq, lt_antisym, real_lt]
       ++ RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero, add_lzero,
       	  	 	 IN_PREIMAGE, IN_SING, mul_rone]
       ++ Suff `SIGMA (\i'. Normal (if 0 <= c i' then c i' else 0) *
       	       	      	    if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >> RW_TAC std_ss [add_rzero]
       ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       ++ REVERSE (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
       >> RW_TAC std_ss [extreal_of_num_def]
       ++ METIS_TAC [IN_DELETE],
       RW_TAC real_ss [],
       FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, EXTENSION,IN_SING]
       ++ METIS_TAC [],
       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_SING, IN_INTER]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF]
       ++ METIS_TAC [IN_IMAGE]])
  ++ `pos_simple_fn m (fn_minus f)
	(count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m)
	(\i. if c i <= 0 then ~ (c i) else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT,FN_PLUS_POS,FN_MINUS_POS]
   << [REVERSE (RW_TAC real_ss [fn_minus_def])
       >> (FULL_SIMP_TAC std_ss [extreal_lt_def,indicator_fn_def,IN_INTER]
           ++ (MP_TAC o Q.SPEC `(\i. Normal (if c i <= 0 then -c i else 0) *
	      	      	       	     if t IN PREIMAGE f {Normal (c i)} then 1 else 0)` o
               UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IN_IF
	   ++ RW_TAC std_ss []
	   ++ POP_ORW
	   ++ Suff `(\x. if x IN count n then Normal (if c x <= 0 then -c x else 0) *
	      	   	 if t IN PREIMAGE f {Normal (c x)} then 1 else 0 else 0) = (\x. 0)`
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
	   ++ RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `~(x IN count n)`
	   >> RW_TAC std_ss []
	   ++ REVERSE (RW_TAC std_ss [mul_rone,mul_rzero])
	   >> RW_TAC std_ss [extreal_of_num_def]
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_COUNT, IN_IMAGE,
	      		    	    IN_PREIMAGE, IN_SING]
	   ++ METIS_TAC [REAL_LE_ANTISYM, extreal_of_num_def, REAL_NEG_0,extreal_le_def,IN_COUNT])
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (f t = Normal (c i))` by METIS_TAC []
       ++ `count n = i INSERT ((count n) DELETE i)`
	    by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ REVERSE (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
       	  	                  mul_lzero, DELETE_DELETE, add_lzero])
       >> METIS_TAC [extreal_lt_eq, real_lt, extreal_of_num_def, lt_antisym]
       ++ RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero,
       	  	 	 add_lzero, IN_PREIMAGE, IN_SING, mul_rone]
       ++ Suff `SIGMA (\i'. Normal (if c i' <= 0 then -c i' else 0) *
       	       	      	    if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >> METIS_TAC [add_rzero, extreal_ainv_def]
       ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       ++ REVERSE (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
       >> RW_TAC std_ss [extreal_of_num_def]
       ++ METIS_TAC [IN_DELETE],
       RW_TAC real_ss [] ++ METIS_TAC [REAL_LE_NEG, REAL_NEG_0],
       FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE,EXTENSION,IN_SING]
       ++ METIS_TAC [],
       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_SING, IN_INTER]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF]
       ++ METIS_TAC [IN_IMAGE]])
  ++ RW_TAC std_ss [finite_space_integral_def]
  ++ `pos_fn_integral m (fn_plus f) =
      pos_simple_fn_integral m (count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m)
      			       (\i. if 0 <= c i then c i else 0)`
            by METIS_TAC [pos_fn_integral_pos_simple_fn]
  ++ `pos_fn_integral m (fn_minus f) =
      pos_simple_fn_integral m (count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m)
      			       (\i. if c i <= 0 then -c i else 0)`
            by METIS_TAC [pos_fn_integral_pos_simple_fn]
  ++ FULL_SIMP_TAC std_ss [integral_def, pos_simple_fn_integral_def, extreal_sub_def,
     		   	   GSYM REAL_SUM_IMAGE_SUB, GSYM REAL_SUB_RDISTRIB]
  ++ `!x. ((if 0 <= c x then c x else 0) - if c x <= 0 then -c x else 0) = c x`
      by (RW_TAC real_ss []
          ++ METIS_TAC [REAL_LE_ANTISYM,REAL_ADD_RID,real_lt,REAL_LT_ANTISYM])
  ++ POP_ORW
  ++ (MP_TAC o Q.ISPEC `c1:num->extreal` o UNDISCH o Q.ISPEC `count n`)
        EXTREAL_SUM_IMAGE_IMAGE
  ++ Know `INJ c1 (count n) (IMAGE c1 (count n))`
  >> (FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, IN_IMAGE] ++ METIS_TAC [])
  ++ SIMP_TAC std_ss [] ++ STRIP_TAC ++ STRIP_TAC
  ++ POP_ASSUM (MP_TAC o Q.SPEC `(\r. r * Normal (measure m (PREIMAGE f {r} INTER m_space m)))`)
  ++ RW_TAC std_ss [o_DEF]
  ++ `(IMAGE c1 (count n)) = (IMAGE f (m_space m))`
     by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_IMAGE]
	 ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	 ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_NORMAL]
  ++ (MATCH_MP_TAC o UNDISCH o Q.SPEC `count n` o INST_TYPE [``:'a`` |-> ``:num``])
        EXTREAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [GSYM extreal_mul_def]);

val finite_space_POW_integral_reduce = store_thm
  ("finite_space_POW_integral_reduce",
   ``!m f. measure_space m /\ (POW (m_space m) = measurable_sets m) /\ FINITE (m_space m) /\
          (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf) ==>
	  (integral m f = SIGMA (\x. f x * Normal (measure m {x})) (m_space m))``,
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
  ++ `!i. i IN count n ==> {c i } IN measurable_sets m`
       by METIS_TAC [IN_POW,IN_SING,BIJ_DEF,SURJ_DEF,SUBSET_DEF]
  ++ `pos_simple_fn m (fn_plus f)
	(count n) (\i. {c i}) (\i. if 0 <= x i then x i else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT,FN_PLUS_POS,FN_MINUS_POS]
   << [REVERSE (RW_TAC real_ss [fn_plus_def])
       >> (FULL_SIMP_TAC std_ss [extreal_lt_def,indicator_fn_def,IN_INTER]
           ++ RW_TAC std_ss [Once  EXTREAL_SUM_IMAGE_IN_IF]
	   ++ Suff `(\i. if i IN count n then Normal (if 0 <= x i then x i else 0) *
	      	   	 if t IN {c i} then 1 else 0 else 0) = \x. 0`
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
	   ++ RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `~(x' IN count n)`
	   >> RW_TAC std_ss []
	   ++ REVERSE (RW_TAC std_ss [mul_rone,mul_rzero])
	   >> RW_TAC std_ss [extreal_of_num_def]
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_COUNT, IN_IMAGE, IN_PREIMAGE,
	      		    	    IN_SING]
	   ++ METIS_TAC [le_antisym, extreal_le_def, extreal_of_num_def])
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (t = c i)` by METIS_TAC []
       ++ FULL_SIMP_TAC std_ss []
       ++ `count n = i INSERT ((count n) DELETE i)`
	    by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ REVERSE (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
       	  	  	  	  mul_lzero, DELETE_DELETE, add_lzero])
       >> METIS_TAC [extreal_of_num_def, extreal_lt_eq, lt_antisym, real_lt]
       ++ RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero, add_lzero,
       	  	 	 IN_PREIMAGE,IN_SING,mul_rone]
       ++ Suff `SIGMA (\i'. Normal (if 0 <= x i' then x i' else 0) *
       	       	      	    if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >> RW_TAC std_ss [add_rzero]
       ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       ++ REVERSE (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
       >> RW_TAC std_ss [extreal_of_num_def]
       ++ METIS_TAC [IN_DELETE],
       RW_TAC real_ss [],
       FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, EXTENSION,
       		     	     IN_SING, BIJ_DEF, INJ_DEF]
       ++ METIS_TAC [],
       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_SING, IN_INTER]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF]
       ++ METIS_TAC [IN_IMAGE]])
   ++ `pos_simple_fn m (fn_minus f)
	(count n) (\i. {c i}) (\i. if x i <= 0 then -(x i) else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT, FN_MINUS_POS, FN_MINUS_POS]
   << [REVERSE (RW_TAC real_ss [fn_minus_def])
       >> (FULL_SIMP_TAC std_ss [extreal_lt_def, indicator_fn_def, IN_INTER]
           ++ RW_TAC std_ss [Once  EXTREAL_SUM_IMAGE_IN_IF]
	   ++ Suff `(\i. if i IN count n then Normal (if x i <= 0 then -(x i) else 0) *
	      	   	 if t IN {c i} then 1 else 0 else 0) = \x. 0`
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
	   ++ RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `~(x' IN count n)`
	   >> RW_TAC std_ss []
	   ++ REVERSE (RW_TAC std_ss [mul_rone,mul_rzero])
	   >> RW_TAC std_ss [extreal_of_num_def]
	   ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_COUNT, IN_SING]
	   ++ METIS_TAC [IN_COUNT, extreal_le_def, extreal_of_num_def, REAL_LE_ANTISYM,
	      		 REAL_NEG_EQ0])
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       ++ `?i. i IN count n /\ (t = c i)` by METIS_TAC []
       ++ FULL_SIMP_TAC std_ss []
       ++ `count n = i INSERT ((count n) DELETE i)`
	    by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] ++ METIS_TAC [])
       ++ POP_ORW
       ++ REVERSE (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
       	  	  	  	  mul_lzero, DELETE_DELETE, add_lzero])
       >> METIS_TAC [extreal_of_num_def, extreal_lt_eq, lt_antisym, real_lt]
       ++ RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero, add_lzero,
       	  	 	 IN_PREIMAGE, IN_SING, mul_rone]
       ++ Suff `SIGMA (\i'. Normal (if x i' <= 0 then -(x i') else 0) *
       	       	      if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >> RW_TAC std_ss [add_rzero, extreal_ainv_def]
       ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       ++ REVERSE (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
       >> RW_TAC std_ss [extreal_of_num_def]
       ++ METIS_TAC [IN_DELETE],
       METIS_TAC [REAL_LE_REFL, REAL_LE_NEG, REAL_NEG_0],
       FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, EXTENSION,
       		     	     IN_SING, BIJ_DEF, INJ_DEF]
       ++ METIS_TAC [],
       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_SING, IN_INTER]
       ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF]
       ++ METIS_TAC [IN_IMAGE]])
  ++ RW_TAC std_ss [integral_def]
  ++ (MP_TAC o Q.SPECL [`m`,`fn_plus f`,`count n`,`(\i. {c i})`,
     	       	        `(\i. if 0 <= x i then x i else 0)`]) pos_fn_integral_pos_simple_fn
  ++ (MP_TAC o Q.SPECL [`m`,`fn_minus f`,`count n`,`(\i. {c i})`,
     	       	        `(\i. if x i <= 0 then -(x i) else 0)`]) pos_fn_integral_pos_simple_fn
  ++ RW_TAC std_ss [pos_simple_fn_integral_def, extreal_sub_def, GSYM REAL_SUM_IMAGE_SUB,
     	    	    GSYM REAL_SUB_RDISTRIB]
  ++ `!x. ((if 0 <= x i then x i else 0) - if x i <= 0:real then -(x i) else 0) = x i`
      by (RW_TAC real_ss [REAL_SUB_RNEG]
          ++ METIS_TAC [REAL_LE_ANTISYM, REAL_ADD_RID, real_lt, REAL_LT_ANTISYM])
  ++ RW_TAC std_ss []
  ++ (MP_TAC o Q.ISPEC `c:num->'a` o UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IMAGE
  ++ Know `INJ c (count n) (IMAGE c (count n))`
  >> (FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, IN_IMAGE] ++ METIS_TAC [])
  ++ RW_TAC std_ss []
  ++ POP_ASSUM (MP_TAC o Q.SPEC `(\x. f x * Normal (measure m {x}))`)
  ++ RW_TAC std_ss [o_DEF]
  ++ `(IMAGE c (count n)) = (m_space m)`
	by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_IMAGE]
	    ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
	    ++ METIS_TAC [])
  ++ FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_NORMAL]
  ++ (MATCH_MP_TAC o UNDISCH o Q.SPEC `count n` o INST_TYPE [``:'a`` |-> ``:num``])
        EXTREAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [GSYM extreal_mul_def]);

val finite_POW_prod_measure_reduce = store_thm
  ("finite_POW_prod_measure_reduce",
   ``!m0 m1. measure_space m0 /\ measure_space m1 /\
   	     FINITE (m_space m0) /\ FINITE (m_space m1) /\
            (POW (m_space m0) = measurable_sets m0) /\ (POW (m_space m1) = measurable_sets m1)
        ==> (!a0 a1. a0 IN measurable_sets m0 /\ a1 IN measurable_sets m1
               ==> ((prod_measure m0 m1) (a0 CROSS a1) = measure m0 a0 * measure m1 a1))``,
  RW_TAC std_ss [prod_measure_def, measure_def, finite_space_POW_integral_reduce,
  	 	 extreal_not_infty]
  ++ RW_TAC std_ss [extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL, real_normal]
  ++ `!s0 s1 x. PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) SUBSET (m_space m1)`
      by (RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_CROSS]
      	  ++ METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE, SUBSET_DEF])
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
        (\s0. measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)) * measure m0 {s0}) x else 0)) =
      (\x. 0)`
	by (RW_TAC std_ss [FUN_EQ_THM, IN_DIFF]
	    ++ RW_TAC std_ss []
	    ++ `PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) = {}`
		by (ONCE_REWRITE_TAC [EXTENSION]
		    ++ RW_TAC std_ss [NOT_IN_EMPTY, IN_PREIMAGE, IN_CROSS])
	    ++ RW_TAC real_ss [MEASURE_EMPTY])
  ++ RW_TAC real_ss [REAL_SUM_IMAGE_0]
  ++ ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `a0`) REAL_SUM_IMAGE_IN_IF]
  ++ `(\x. (if x IN a0 then (\s0. measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)) *
     	       measure m0 {s0}) x else 0)) =
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
       subsets (sigma (m_space m0 CROSS m_space m1)
	 	      (prod_sets (measurable_sets m0) (measurable_sets m1))),
       prod_measure m0 m1) =
      (space (sigma (m_space m0 CROSS m_space m1)
            (prod_sets (measurable_sets m0) (measurable_sets m1))),
	subsets (sigma (m_space m0 CROSS m_space m1)
                       (prod_sets (measurable_sets m0) (measurable_sets m1))),
        prod_measure m0 m1)`
	by RW_TAC std_ss [sigma_def, space_def]
  ++ POP_ORW
  ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
  ++ `sigma_algebra (sigma (m_space m0 CROSS m_space m1)
                     (prod_sets (measurable_sets m0) (measurable_sets m1)))`
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
			 MEASURE_EMPTY, REAL_MUL_LZERO])
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
      ++ FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce, real_normal,
      	 	       	       extreal_not_infty, extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL]
      ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_LE_MUL
      ++ FULL_SIMP_TAC std_ss [measure_space_def, positive_def]
      ++ METIS_TAC [IN_POW, IN_SING, SUBSET_DEF])
  ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  ++ FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce, extreal_not_infty,
     		   	   extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL, real_normal,
			   GSYM REAL_SUM_IMAGE_ADD, GSYM REAL_ADD_RDISTRIB]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss []
  ++ Suff `measure m1 (PREIMAGE (\s1. (x,s1)) (s UNION t)) =
           measure m1 (PREIMAGE (\s1. (x,s1)) s) + measure m1 (PREIMAGE (\s1. (x,s1)) t)`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC MEASURE_ADDITIVE
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC
  >> (Suff `PREIMAGE (\s1. (x,s1)) s SUBSET (m_space m1)`
      >> METIS_TAC [IN_POW]
      ++ RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
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
  ++ `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
     	 POW (m_space m0 CROSS m_space m1)`
      by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
          ++ Cases_on `x''`
	  ++ FULL_SIMP_TAC std_ss []
	  ++ METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW,IN_CROSS])
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
  ++ `(s UNION t) IN subsets (sigma (m_space m0 CROSS m_space m1)
     	       	     	     	    (prod_sets (measurable_sets m0) (measurable_sets m1)))`
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
  ++ CONJ_TAC >> METIS_TAC [IN_POW]
  ++ CONJ_TAC
  >> (RW_TAC std_ss [EXTENSION,IN_DISJOINT,IN_PREIMAGE]
      ++ SPOSE_NOT_THEN ASSUME_TAC
      ++ METIS_TAC [DISJOINT_DEF, NOT_IN_EMPTY, IN_INTER, EXTENSION])
  ++ RW_TAC std_ss [EXTENSION,IN_PREIMAGE,IN_UNION]);


val measure_space_finite_prod_measure_POW2 = store_thm
  ("measure_space_finite_prod_measure_POW2",
   ``!m0 m1. measure_space m0 /\ measure_space m1 /\
	     FINITE (m_space m0) /\ FINITE (m_space m1) /\
	     (POW (m_space m0) = measurable_sets m0) /\
	     (POW (m_space m1) = measurable_sets m1) ==>
	measure_space (m_space m0 CROSS m_space m1,
		       POW (m_space m0 CROSS m_space m1),
		       prod_measure m0 m1)``,
  REPEAT STRIP_TAC
  ++ `(m_space m0 CROSS m_space m1, POW (m_space m0 CROSS m_space m1), prod_measure m0 m1) =
      (space (m_space m0 CROSS m_space m1, POW (m_space m0 CROSS m_space m1)),
         subsets (m_space m0 CROSS m_space m1, POW (m_space m0 CROSS m_space m1)),
	 	 	  prod_measure m0 m1)`
	by RW_TAC std_ss [space_def, subsets_def]
  ++ POP_ORW
  ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
  ++ RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
  >> (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
      >> (`{} = {} CROSS {}` by RW_TAC std_ss [CROSS_EMPTY]
          ++ POP_ORW
	  ++ METIS_TAC [finite_POW_prod_measure_reduce,
			measure_space_def, SIGMA_ALGEBRA, subsets_def, space_def,
			MEASURE_EMPTY, REAL_MUL_RZERO])
      ++ `!x. (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
	by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	    ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [SND])
      ++ FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce,
      	 	       	       extreal_not_infty, extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL,
			       real_normal]
      ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss [] ++ MATCH_MP_TAC REAL_LE_MUL
      ++ FULL_SIMP_TAC std_ss [measure_space_def, positive_def]
      ++ METIS_TAC [IN_POW, IN_SING, SUBSET_DEF])
  ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  ++ `!x. (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
	by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	    ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [SND])
  ++ `!x. (PREIMAGE (\s1. (x,s1)) t) SUBSET m_space m1`
	by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	    ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [SND])
  ++ `(s UNION t) IN POW (m_space m0 CROSS m_space m1)` by METIS_TAC [IN_POW,UNION_SUBSET]
  ++ `!x. (PREIMAGE (\s1. (x,s1)) (s UNION t)) SUBSET m_space m1`
	by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
	    ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
	    ++ METIS_TAC [SND])
  ++ FULL_SIMP_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce, extreal_not_infty,
     		   	   extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL, real_normal,
			   GSYM REAL_SUM_IMAGE_ADD]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [FUN_EQ_THM, GSYM REAL_ADD_RDISTRIB]
  ++ Suff `measure m1 (PREIMAGE (\s1. (x,s1)) (s UNION t)) =
          (measure m1 (PREIMAGE (\s1. (x,s1)) s) + measure m1 (PREIMAGE (\s1. (x,s1)) t))`
  >> RW_TAC std_ss []
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
  RW_TAC std_ss [prod_measure_space_def, m_space_def, subsets_def, EXTENSION, subsets_def,
  	 	 sigma_def, prod_sets_def, IN_POW, IN_BIGINTER, measurable_sets_def, SUBSET_DEF,
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
  ++ Q.PAT_ASSUM `!x. Q ==> x IN s` MATCH_MP_TAC
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
  	     (!a0 a1 a2. a0 IN measurable_sets m0 /\
	                 a1 IN measurable_sets m1 /\
			 a2 IN measurable_sets m2
             ==> ((prod_measure3 m0 m1 m2) (a0 CROSS (a1 CROSS a2)) =
                  measure m0 a0 * measure m1 a1 * measure m2 a2))``,
  RW_TAC std_ss [prod_measure3_def, measure_def]
  ++ `measure_space (prod_measure_space m1 m2)`
      by METIS_TAC [measure_space_finite_prod_measure_POW1]
  ++ `FINITE (m_space (prod_measure_space m1 m2))`
      by METIS_TAC [prod_measure_space_def,m_space_def,FINITE_CROSS]
  ++ `m_space (prod_measure_space m1 m2) = m_space m1 CROSS (m_space m2)`
         by RW_TAC std_ss [prod_measure_space_def,m_space_def]
  ++ `measurable_sets (prod_measure_space m1 m2) =
      POW (m_space m1 CROSS (m_space m2))`
        by (`m1 = (m_space m1,measurable_sets m1,measure m1)`
	     by RW_TAC std_ss [MEASURE_SPACE_REDUCE]
	    ++ `m2 = (m_space m2, measurable_sets m2, measure m2)`
	     by RW_TAC std_ss [MEASURE_SPACE_REDUCE]
	    ++ METIS_TAC [finite_prod_measure_space_POW, m_space_def, measurable_sets_def])
  ++ `a1 CROSS a2 IN measurable_sets (prod_measure_space m1 m2)`
        by (RW_TAC std_ss [IN_POW,SUBSET_DEF,IN_CROSS]
	    ++ METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF])
  ++ RW_TAC std_ss [finite_POW_prod_measure_reduce]
  ++ RW_TAC std_ss [prod_measure_space_def, measure_def]
  ++ METIS_TAC [finite_POW_prod_measure_reduce, REAL_MUL_ASSOC]);

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
	 	  POW (m_space m0 CROSS (m_space m1 CROSS m_space m2))), prod_measure3 m0 m1 m2)`
	by RW_TAC std_ss [space_def, subsets_def]
   ++ POP_ORW
   ++ `measure_space (prod_measure_space m1 m2)`
       by METIS_TAC [measure_space_finite_prod_measure_POW1]
   ++ `prod_measure_space m1 m2 =
       (m_space m1 CROSS m_space m2, POW (m_space m1 CROSS m_space m2), prod_measure m1 m2)`
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
	  ++ RW_TAC std_ss [finite_POW_prod_measure_reduce3, MEASURE_SPACE_EMPTY_MEASURABLE,
	     	    	    MEASURE_EMPTY, REAL_MUL_LZERO])
      ++ RW_TAC std_ss [Once prod_measure_def,prod_measure3_def, finite_space_POW_integral_reduce,
      	 	        extreal_not_infty, extreal_mul_def, EXTREAL_SUM_IMAGE_NORMAL, real_normal]
      ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss []
      ++ MATCH_MP_TAC REAL_LE_MUL
      ++ REVERSE CONJ_TAC
      >> METIS_TAC [IN_POW, IN_SING, SUBSET_DEF, MEASURE_SPACE_POSITIVE, positive_def]
      ++ RW_TAC std_ss [measure_def,prod_measure_def, finite_space_POW_integral_reduce,
      	 	        extreal_not_infty, EXTREAL_SUM_IMAGE_NORMAL, extreal_mul_def, real_normal]
      ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
      ++ RW_TAC std_ss []
      ++ MATCH_MP_TAC REAL_LE_MUL
      ++ REVERSE CONJ_TAC
      >> METIS_TAC [IN_POW, IN_SING, SUBSET_DEF, MEASURE_SPACE_POSITIVE, positive_def]
      ++ Suff `(PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) s)) SUBSET (m_space m2)`
      >> METIS_TAC [IN_POW, IN_SING, SUBSET_DEF, MEASURE_SPACE_POSITIVE, positive_def]
      ++ RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE]
      ++ METIS_TAC [IN_CROSS,IN_POW,SUBSET_DEF, FST, SND])
  ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  ++ RW_TAC std_ss [prod_measure3_def]
  ++ ONCE_REWRITE_TAC [prod_measure_def]
  ++ RW_TAC std_ss [measure_def]
  ++ RW_TAC std_ss [finite_space_POW_integral_reduce, extreal_not_infty, EXTREAL_SUM_IMAGE_NORMAL,
     	    	    real_normal, extreal_mul_def, GSYM REAL_SUM_IMAGE_ADD]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [GSYM REAL_ADD_RDISTRIB]
  ++ Suff `prod_measure m1 m2 (PREIMAGE (\s1. (x,s1)) (s UNION t)) =
           (prod_measure m1 m2 (PREIMAGE (\s1. (x,s1)) s) +
            prod_measure m1 m2 (PREIMAGE (\s1. (x,s1)) t))`
  >> RW_TAC std_ss []
  ++ RW_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce, extreal_not_infty,
     	    	    EXTREAL_SUM_IMAGE_NORMAL, real_normal, extreal_mul_def,
		    GSYM REAL_SUM_IMAGE_ADD]
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss [GSYM REAL_ADD_RDISTRIB]
  ++ Suff `measure m2 (PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) (s UNION t))) =
           measure m2 (PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) s)) +
     	   measure m2 (PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) t))`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC MEASURE_ADDITIVE
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC
  >> (Suff `PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m2`
      >> METIS_TAC [IN_POW]
      ++ RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE]
      ++ METIS_TAC [IN_POW, IN_CROSS, SUBSET_DEF, FST, SND])
  ++ CONJ_TAC
  >> (Suff `PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) t) SUBSET m_space m2`
      >> METIS_TAC [IN_POW]
      ++ RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE]
      ++ METIS_TAC [IN_POW, IN_CROSS, SUBSET_DEF, FST, SND])
  ++ CONJ_TAC
  >> (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE]
      ++ METIS_TAC [IN_POW, IN_CROSS, SUBSET_DEF, FST, SND, DISJOINT_DEF, EXTENSION,
      	 	    IN_INTER,NOT_IN_EMPTY])
  ++ RW_TAC std_ss [EXTENSION,IN_PREIMAGE,IN_UNION]);

val finite_prod_measure_space_POW3 = store_thm
 ("finite_prod_measure_space_POW3",``!s1 s2 s3 u v w.
         FINITE s1 /\ FINITE s2 /\ FINITE s3 ==>
         (prod_measure_space3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w) =
          (s1 CROSS (s2 CROSS s3),POW (s1 CROSS (s2 CROSS s3)),
           prod_measure3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w)))``,
  RW_TAC std_ss [prod_measure_space3_def,m_space_def, subsets_def, EXTENSION, subsets_def,
  	 	sigma_def, prod_sets3_def, IN_POW, IN_BIGINTER, measurable_sets_def, SUBSET_DEF,
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
    by (ONCE_REWRITE_TAC [EXTENSION]
        ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
  ++ POP_ORW
  ++ FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
  ++ POP_ASSUM MATCH_MP_TAC
  ++ CONJ_TAC
  >> (MATCH_MP_TAC FINITE_COUNTABLE ++ MATCH_MP_TAC IMAGE_FINITE
      ++ (MP_TAC o
          Q.ISPEC `(s1 :'a -> bool) CROSS ((s2 :'b -> bool) CROSS (s3:'c -> bool))`)
  		SUBSET_FINITE
      ++ RW_TAC std_ss [FINITE_CROSS]
      ++ POP_ASSUM MATCH_MP_TAC
      ++ RW_TAC std_ss [SUBSET_DEF, IN_CROSS])
  ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
  ++ Q.PAT_ASSUM `!x. Q ==> x IN s` MATCH_MP_TAC
  ++ Q.EXISTS_TAC `({FST a}, {FST (SND a)}, {SND(SND a)})` ++ RW_TAC std_ss [IN_SING]
  ++ RW_TAC std_ss [IN_SING,EXTENSION,IN_CROSS,PAIR]
  ++ METIS_TAC [PAIR]);

(* ------------------------------------------------------------------------- *)
(* Radon Nikodym Theorem                                                     *)
(* ------------------------------------------------------------------------- *)


val seq_sup_def = Define `(seq_sup P 0 = @r. r IN P /\ sup P < r + 1) /\
       		  	  (seq_sup P (SUC n) = @r. r IN P /\
			  	     	       sup P < r + Normal ((1 / 2) pow (SUC n)) /\
					       (seq_sup P n) < r /\ r < sup P)`;

val EXTREAL_SUP_SEQ = store_thm
  ("EXTREAL_SUP_SEQ",``!P. (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) ==>
                    	   ?x. (!n. x n IN P) /\
		    	       (!n. x n <= x (SUC n)) /\
			       (sup (IMAGE x UNIV) = sup P)``,
  RW_TAC std_ss []
  ++ Cases_on `?z. P z /\ (z = sup P)`
  >> (Q.EXISTS_TAC `(\i. sup P)`
      ++ RW_TAC std_ss [le_refl,SPECIFICATION]
      ++ `IMAGE (\i:num. sup P) UNIV = (\i. i = sup P)`
           by RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_UNIV,IN_ABS]
      ++ RW_TAC std_ss [sup_const])
  ++ Cases_on `!x. P x ==> (x = NegInf)`
  >> (`sup P = NegInf` by METIS_TAC [sup_const_alt]
      ++ Q.EXISTS_TAC `(\n. NegInf)`
      ++ FULL_SIMP_TAC std_ss [le_refl]
      ++ RW_TAC std_ss []
      >> METIS_TAC []
      ++ METIS_TAC [UNIV_NOT_EMPTY,sup_const_over_set])
  ++ FULL_SIMP_TAC std_ss []
  ++ Q.EXISTS_TAC `seq_sup P`
  ++ FULL_SIMP_TAC std_ss []
  ++ `sup P <> PosInf` by METIS_TAC [sup_le,lt_infty,let_trans]
  ++ `!x. P x ==> x < sup P` by METIS_TAC [lt_le,le_sup_imp]
  ++ `!e. 0 < e ==> ?x. P x /\ sup P < x + e`
       by (RW_TAC std_ss [] ++ MATCH_MP_TAC sup_lt_epsilon ++ METIS_TAC [])
  ++ `!n. 0:real < (1 / 2) pow n` by METIS_TAC [HALF_POS,REAL_POW_LT]
  ++ `!n. 0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def]
  ++ `!n. seq_sup P n IN P`
      by (Induct
          >> (RW_TAC std_ss [seq_sup_def]
	      ++ SELECT_ELIM_TAC
	      ++ RW_TAC std_ss []
	      ++ METIS_TAC [lt_01,SPECIFICATION])
          ++ RW_TAC std_ss [seq_sup_def]
          ++ SELECT_ELIM_TAC
          ++ RW_TAC std_ss []
          ++ `?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
          ++ `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
          ++ Q.EXISTS_TAC `max x'' x'''`
          ++ RW_TAC std_ss [extreal_max_def,SPECIFICATION]
          >> (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
              ++ `x''' +  Normal ((1 / 2) pow (SUC n)) <= x'' +  Normal ((1 / 2) pow (SUC n))`
	          by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
              ++ METIS_TAC [lte_trans])
          ++ METIS_TAC [lte_trans])
  ++ `!n. seq_sup P n <= seq_sup P (SUC n)`
      by (RW_TAC std_ss [seq_sup_def]
          ++ SELECT_ELIM_TAC
          ++ RW_TAC std_ss []
          >> (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              ++ `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              ++ Q.EXISTS_TAC `max x'' x'''`
              ++ RW_TAC std_ss [extreal_max_def,SPECIFICATION]
	      >> (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  ++ `x''' + Normal ((1 / 2) pow (SUC n)) <= x'' + Normal ((1 / 2) pow (SUC n))`
		      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  ++ METIS_TAC [lte_trans])
	      ++ METIS_TAC [lte_trans])
	  ++ METIS_TAC [lt_le])
  ++ RW_TAC std_ss []
  ++ `!n. sup P <= seq_sup P n + Normal ((1 / 2) pow n)`
      by (Induct
	  >> (RW_TAC std_ss [seq_sup_def,pow,GSYM extreal_of_num_def]
	      ++ SELECT_ELIM_TAC
	      ++ RW_TAC std_ss []
	      >> METIS_TAC [lt_01,SPECIFICATION]
	      ++ METIS_TAC [lt_le])
	  ++ RW_TAC std_ss [seq_sup_def]
          ++ SELECT_ELIM_TAC
	  ++ RW_TAC std_ss []
	  >> (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              ++ `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              ++ Q.EXISTS_TAC `max x'' x'''`
	      ++ RW_TAC std_ss [extreal_max_def,SPECIFICATION]
	      >> (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  ++ `x''' + Normal ((1 / 2) pow (SUC n)) <= x'' + Normal ((1 / 2) pow (SUC n))`
		      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  ++ METIS_TAC [lte_trans])
	      ++ METIS_TAC [lte_trans])
	  ++ METIS_TAC [lt_le])
  ++ RW_TAC std_ss [sup_eq]
  >> (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [SPECIFICATION,lt_le])
  ++ MATCH_MP_TAC le_epsilon
  ++ RW_TAC std_ss []
  ++ `e <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,lt_trans]
  ++ `?r. e = Normal r` by METIS_TAC [extreal_cases]
  ++ FULL_SIMP_TAC std_ss []
  ++ `?n. Normal ((1 / 2) pow n) < Normal r` by METIS_TAC [EXTREAL_ARCH_POW_INV]
  ++ MATCH_MP_TAC le_trans
  ++ Q.EXISTS_TAC `seq_sup P n + Normal ((1 / 2) pow n)`
  ++ RW_TAC std_ss []
  ++ MATCH_MP_TAC le_add2
  ++ FULL_SIMP_TAC std_ss [lt_le]
  ++ Q.PAT_ASSUM `!z. IMAGE (seq_sup P) UNIV z ==> z <= y` MATCH_MP_TAC
  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  ++ RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  ++ METIS_TAC []);

val EXTREAL_SUP_FUN_SEQ_IMAGE = store_thm
("EXTREAL_SUP_FUN_SEQ_IMAGE", ``!(P:extreal->bool) (P':('a->extreal)->bool) f.
		(?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P')
  	   ==> ?g. (!n:num. g n IN P') /\
	           (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
  REPEAT STRIP_TAC
  ++ `?y. (!n. y n IN P) /\ (!n. y n <= y (SUC n)) /\ (sup (IMAGE y UNIV) = sup P)`
      by METIS_TAC [EXTREAL_SUP_SEQ]
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
	 	     	     (max_fn_seq g (SUC n) x = max (max_fn_seq g n x) (g (SUC n) x))`;

val max_fn_seq_mono = store_thm
  ("max_fn_seq_mono", ``!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x``,
   RW_TAC std_ss [max_fn_seq_def,extreal_max_def,le_refl]);

val EXTREAL_SUP_FUN_SEQ_MONO_IMAGE = store_thm
  ("EXTREAL_SUP_FUN_SEQ_MONO_IMAGE", ``!(P:extreal->bool) (P':('a->extreal)->bool).
		(?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P') /\
  	  	(!g1 g2. (g1 IN P' /\ g2 IN P' /\ (!x. g1 x <= g2 x))  ==> f g1 <= f g2) /\
		(!g1 g2. g1 IN P' /\ g2 IN P' ==> (\x. max (g1 x) (g2 x)) IN P')
          ==> ?g. (!n. g n IN P') /\
	      	  (!x n. g n x <= g (SUC n) x) /\
		  (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
  REPEAT STRIP_TAC
  ++ `?g. (!n:num. g n IN P') /\ (sup (IMAGE (\n. f (g n)) UNIV) = sup P)`
      by METIS_TAC [EXTREAL_SUP_FUN_SEQ_IMAGE]
  ++ Q.EXISTS_TAC `max_fn_seq g`
  ++ `!n. max_fn_seq g n IN P'`
      by (Induct
 	  >> (`max_fn_seq g 0 = g 0` by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
	      ++ METIS_TAC [])
	      ++ `max_fn_seq g (SUC n) = (\x. max (max_fn_seq g n x) (g (SUC n) x))`
                  by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
	      ++ RW_TAC std_ss []
	      ++ METIS_TAC [])
  ++ `!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x`
      by RW_TAC real_ss [max_fn_seq_def,extreal_max_def,le_refl]
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ `!n. (!x. g n x <= max_fn_seq g n x)`
      by (Induct >> RW_TAC std_ss [max_fn_seq_def,le_refl]
	  ++ METIS_TAC [le_max2,max_fn_seq_def])
  ++ `!n. f (g n) <= f (max_fn_seq g n)` by METIS_TAC []
  ++ `sup (IMAGE (\n. f (g n)) UNIV) <= sup (IMAGE (\n. f (max_fn_seq g n)) UNIV)`
      by (MATCH_MP_TAC sup_le_sup_imp
          ++ RW_TAC std_ss []
	  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ Q.EXISTS_TAC `f (max_fn_seq g n)`
	  ++ RW_TAC std_ss []
	  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ METIS_TAC [])
  ++ `sup (IMAGE (\n. f (max_fn_seq g n)) UNIV) <= sup P`
      by (RW_TAC std_ss [sup_le]
          ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ MATCH_MP_TAC le_sup_imp
	  ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	  ++ RW_TAC std_ss [IN_IMAGE]
	  ++ METIS_TAC [])
  ++ METIS_TAC [le_antisym]);

val signed_measure_space_def = Define `
    signed_measure_space m = sigma_algebra (m_space m,measurable_sets m) /\ countably_additive m`;

val negative_set_def = Define `
    negative_set m A = A IN measurable_sets m /\
                      (!s. s IN measurable_sets m /\ s SUBSET A ==> measure m s <= 0)`;


(**********************************************************)
(*  Radon Nikodym Theorem                                 *)
(**********************************************************)

val RADON_F_def = Define `RADON_F m v =
             {f | f IN measurable (m_space m,measurable_sets m) Borel /\
	          (!x. 0 <= f x) /\
	     	  !A. A IN measurable_sets m
                   ==> (pos_fn_integral m (\x. f x * indicator_fn A x) <= Normal (measure v A))}`;

val RADON_F_integrals_def = Define `
	RADON_F_integrals m v = {r | ?f. (r = pos_fn_integral m f) /\ f IN RADON_F m v}`;

val measure_absolutely_continuous_def = Define `
	measure_absolutely_continuous m v = !A. A IN measurable_sets m /\ (measure v A = 0)
                                             ==> (measure m A = 0)`;

val lemma_radon_max_in_F = store_thm
  ("lemma_radon_max_in_F",``!f g m v. (measure_space m /\ measure_space v /\
	(m_space v = m_space m) /\ (measurable_sets v = measurable_sets m) /\
        f IN RADON_F m v /\ g IN RADON_F m v)
	     ==> (\x. max (f x) (g x)) IN RADON_F m v``,
  RW_TAC real_ss [RADON_F_def,GSPECIFICATION,max_le,le_max]
  >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL_MAX,measure_space_def]
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
	   ++ METIS_TAC [IN_MEASURABLE_BOREL_LT, m_space_def, space_def, subsets_def,
	      		 measurable_sets_def])
   ++ `A2 IN measurable_sets m`
       by (ASM_SIMP_TAC std_ss []
	   ++ MATCH_MP_TAC MEASURE_SPACE_INTER
	   ++ RW_TAC std_ss []
	   ++ METIS_TAC [IN_MEASURABLE_BOREL_LE, m_space_def, space_def, subsets_def,
	      		 measurable_sets_def])
   ++ `measure v A = measure v A1 + measure v A2` by METIS_TAC [ADDITIVE]
   ++ Q.PAT_ASSUM `A1 = M` (K ALL_TAC)
   ++ Q.PAT_ASSUM `A2 = M` (K ALL_TAC)
   ++ `!x. max (f x) (g x) * indicator_fn A1 x = f x * indicator_fn A1 x`
       by (Q.UNABBREV_TAC `A1`
	   ++ RW_TAC std_ss [extreal_max_def, indicator_fn_def, GSPECIFICATION, mul_rone,
	      	     	     mul_rzero]
	   ++ METIS_TAC [extreal_lt_def])
   ++ `!x. max (f x) (g x) * indicator_fn A2 x = g x * indicator_fn A2 x`
       by (Q.UNABBREV_TAC `A2`
	   ++ RW_TAC std_ss [extreal_max_def, indicator_fn_def, GSPECIFICATION, mul_rone,
	      	     	     mul_rzero]
	   ++ METIS_TAC [extreal_lt_def])
   ++ ASM_SIMP_TAC std_ss []
   ++ `(\x. f x * indicator_fn A1 x) IN measurable (m_space m, measurable_sets m) Borel`
           by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
	      		 measurable_sets_def, subsets_def]
   ++ `(\x. g x * indicator_fn A2 x) IN  measurable (m_space m, measurable_sets m) Borel`
           by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
	      		 measurable_sets_def, subsets_def]
   ++ `!x. 0 <= (\x. f x * indicator_fn A1 x) x`
        by RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_01, le_refl]
   ++ `!x. 0 <= (\x. g x * indicator_fn A2 x) x`
        by RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_01, le_refl]
   ++ FULL_SIMP_TAC std_ss [le_add2,pos_fn_integral_add, GSYM extreal_add_def]);

val lemma_radon_seq_conv_sup = store_thm
  ("lemma_radon_seq_conv_sup",``!f m v. (measure_space m /\ measure_space v /\
   				        (m_space v = m_space m) /\
					(measurable_sets v = measurable_sets m))
	==> ?f_n. (!n. f_n n IN RADON_F m v) /\
	    	  (!x n. f_n n x <= f_n (SUC n) x) /\
		  (sup (IMAGE (\n. pos_fn_integral m (f_n n)) UNIV) =
		            sup (RADON_F_integrals m v))``,
  RW_TAC std_ss [RADON_F_integrals_def]
  ++ MATCH_MP_TAC EXTREAL_SUP_FUN_SEQ_MONO_IMAGE
  ++ CONJ_TAC
  >> (Q.EXISTS_TAC `0`
      ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      ++ RW_TAC std_ss [GSPECIFICATION]
      ++ Q.EXISTS_TAC `(\x. 0)`
      ++ RW_TAC real_ss [RADON_F_def,GSPECIFICATION,pos_fn_integral_zero,mul_lzero,le_refl]
      >> (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST
          ++ METIS_TAC [space_def,measure_space_def])
      ++ METIS_TAC [measure_space_def, positive_def, extreal_of_num_def, extreal_le_def])
  ++ CONJ_TAC
  >> (Q.EXISTS_TAC `Normal (measure v (m_space v))`
      ++ RW_TAC std_ss [extreal_not_infty]
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
                       (m_space v = m_space m) /\ (measurable_sets v = measurable_sets m)
       ==> (?A. A IN measurable_sets m /\
       	        measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
        	!B. B IN measurable_sets m /\ B SUBSET A
		    ==> -e < measure m B - measure v B)``,
  RW_TAC std_ss []
  ++ Q.ABBREV_TAC `d = (\A. measure m A - measure v A)`
  ++ Q.ABBREV_TAC `h = (\A. if (!B. B IN measurable_sets m /\
     		       	       	    B SUBSET (m_space m DIFF A) ==> -e < d B)
                            then {} else
			       @B. B IN measurable_sets m /\ B
			       	   SUBSET (m_space m DIFF A) /\ d B <= -e )`
  ++ `!A. A IN measurable_sets m ==> h A  IN measurable_sets m`
        by (RW_TAC std_ss []
	    ++ METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE,real_lt])
  ++ Q.ABBREV_TAC `A = SIMP_REC {} (\a. a UNION h a)`
  ++ `A 0 = {}` by METIS_TAC [SIMP_REC_THM]
  ++ `!n. A (SUC n) = (A n) UNION (h (A n))`
      by (Q.UNABBREV_TAC `A` ++ RW_TAC std_ss [SIMP_REC_THM])
  ++ `!n. A n IN measurable_sets m`
        by (Induct >> RW_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE]
	    ++ RW_TAC std_ss [MEASURE_SPACE_UNION])
  ++ `!n. (?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e) ==>
               d (A (SUC n)) <= d (A n) - e`
       by (RW_TAC std_ss []
           ++ `~(!B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) ==> -e < d B)`
                 by METIS_TAC [real_lt]
           ++ `h (A n) = (@B. B IN measurable_sets m /\
	      	       	      B SUBSET m_space m DIFF (A n) /\ d B <= -e)`
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
            >> (`d (A n) <= d (A n) + e` by METIS_TAC [REAL_LE_ADDR, REAL_LT_IMP_LE]
		++ `d (A n) - e <= d (A n)` by METIS_TAC [REAL_LE_SUB_RADD]
		++ METIS_TAC [REAL_LE_TRANS])
	    ++ `!B. B IN measurable_sets m /\ B SUBSET m_space m DIFF A n ==> -e < d B`
                 by METIS_TAC [real_lt]
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
                 ++ RW_TAC std_ss []
		 ++ REAL_ARITH_TAC)
      ++ `d (m_space m DIFF A (SUC n')) = d (m_space m) - d (A (SUC n'))`
             by (Q.UNABBREV_TAC `d`
                 ++ RW_TAC std_ss []
		 ++ REAL_ARITH_TAC)
      ++ FULL_SIMP_TAC std_ss []
      ++ `d (m_space m) - d (A n') <= d (m_space m) - d (A (SUC n'))`
           by METIS_TAC [real_sub, MEASURE_SPACE_MSPACE_MEASURABLE, REAL_LE_LADD, REAL_LE_NEG]
      ++ METIS_TAC [REAL_LE_TRANS])
  ++ `!n. ?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e`
        by METIS_TAC [real_lt]
  ++ `!n. d (A n) <= - &n * e`
       by (Induct
           >> METIS_TAC [REAL_MUL_LZERO, REAL_NEG_0, REAL_LE_REFL, MEASURE_EMPTY, measure_def,
	      		 REAL_SUB_RZERO]
           ++ `d (A (SUC n)) <= d (A n) - e` by METIS_TAC []
	   ++ `-&SUC n * e = -&n * e + -e`
	       by (RW_TAC std_ss [ADD1, GSYM add_ints] ++ REAL_ARITH_TAC)
	   ++ POP_ORW
	   ++ Suff `d (A n) - e <= -&n * e + -e` >> METIS_TAC [REAL_LE_TRANS]
	   ++ METIS_TAC [REAL_NEG_ADD, REAL_LE_ADD2, real_sub, REAL_LE_REFL])
  ++ `!n. - d (A n) <= - d (A (SUC n))` by METIS_TAC [REAL_LE_NEG]
  ++ `!n. A n SUBSET A (SUC n)` by METIS_TAC [SUBSET_UNION]
  ++ `measure m o A --> measure m (BIGUNION (IMAGE A UNIV))`
       by METIS_TAC [MONOTONE_CONVERGENCE2, IN_FUNSET, IN_UNIV, measure_def, measurable_sets_def]
  ++ `measure v o A --> measure v (BIGUNION (IMAGE A UNIV))`
       by METIS_TAC [MONOTONE_CONVERGENCE2, IN_FUNSET, IN_UNIV, measure_def, measurable_sets_def]
  ++ FULL_SIMP_TAC std_ss [o_DEF]
  ++ `BIGUNION (IMAGE A UNIV) IN measurable_sets m`
      by METIS_TAC [SIGMA_ALGEBRA_ENUM, measure_space_def, subsets_def, measurable_sets_def,
      	 	    IN_FUNSET, IN_UNIV]
  ++ `(\n. -d (A n)) --> -d (BIGUNION (IMAGE A UNIV))`
      by (Q.UNABBREV_TAC `d`
          ++ RW_TAC std_ss [SEQ_SUB, REAL_NEG_SUB])
  ++ `?n. - d (BIGUNION (IMAGE A UNIV)) < &n * e` by METIS_TAC [REAL_ARCH]
  ++ `&n * e <= -d (A n)` by METIS_TAC [REAL_LE_NEG, REAL_NEG_NEG, REAL_MUL_LNEG]
  ++ `-d (BIGUNION (IMAGE A univ(:num))) < -d (A n)` by METIS_TAC [REAL_LTE_TRANS]
  ++ `!n. (\n. -d (A n)) n <= (\n. -d (A n)) (n+1)`
           by METIS_TAC [ADD1]
  ++ Suff `(\n. -d (A n)) n <= -d (BIGUNION (IMAGE A univ(:num)))`
  >> RW_TAC real_ss [real_lte]
  ++ MATCH_MP_TAC SEQ_MONO_LE
  ++ RW_TAC std_ss []);

val RN_lemma2 = store_thm
("RN_lemma2",``!m v. measure_space m /\ measure_space v /\
         	     (m_space v = m_space m) /\
         	     (measurable_sets v = measurable_sets m)
   ==> (?A. A IN measurable_sets m /\
            measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
            !B. B IN measurable_sets m /\
	    	B SUBSET A ==> 0 <= measure m B - measure v B)``,
  RW_TAC std_ss []
  ++ Q.ABBREV_TAC `d = (\a. measure m a - measure v a)`
  ++ Q.ABBREV_TAC `p = (\a b n. a IN measurable_sets m /\
     		       	     	a SUBSET b /\
				d b <= d a /\
				(!c. c IN measurable_sets m /\
				     c SUBSET a ==> -((1 / 2) pow n) < d c))`
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
  ++ `!n. 0:real <  ((1 / 2) pow n)` by METIS_TAC [POW_HALF_POS]
  ++ `!s n. s IN measurable_sets m ==> ?A. p A s n`
         by (RW_TAC std_ss []
             ++ `?A. A IN (sts s) /\ measure m s - measure v s <= measure m A - measure v A /\
                (!B. B IN (sts s) /\ B SUBSET A ==>
		            -((1 / 2) pow n) < measure m B - measure v B)`
                 by (RW_TAC std_ss []
                     ++ (MP_TAC o Q.SPECL [`(s,sts s,measure m)`,`(s,sts s,measure v)`,
		     		  	   `(1 / 2) pow n`]) RN_lemma1
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
  ++ `!n c. (c IN measurable_sets m /\ c SUBSET (A (SUC n)) ==> - ((1 / 2) pow n) < d c)`
       by METIS_TAC []
  ++ Q.EXISTS_TAC `BIGINTER (IMAGE A UNIV)`
  ++ CONJ_TAC
  >> METIS_TAC [SIGMA_ALGEBRA_FN_BIGINTER, IN_UNIV, IN_FUNSET, subsets_def, measurable_sets_def,
     	        measure_space_def]
  ++ REVERSE CONJ_TAC
  >> (RW_TAC std_ss []
      ++ SPOSE_NOT_THEN ASSUME_TAC
      ++ FULL_SIMP_TAC std_ss [GSYM real_lt]
      ++ `0 < - (measure m B - measure v B)` by METIS_TAC [REAL_LT_NEG,REAL_NEG_0]
      ++ `?n. measure m B - measure v B < -((1 / 2) pow n)`
          by METIS_TAC [POW_HALF_SMALL, REAL_LT_NEG, REAL_NEG_NEG]
      ++ `d B < -((1 / 2) pow n)` by METIS_TAC []
      ++ `!n. B SUBSET A n` by METIS_TAC [SUBSET_BIGINTER,IN_IMAGE,IN_UNIV]
      ++ METIS_TAC [REAL_LT_ANTISYM])
  ++ `measure m o A --> measure m (BIGINTER (IMAGE A UNIV))`
      by METIS_TAC [MONOTONE_CONVERGENCE_BIGINTER2, IN_UNIV, IN_FUNSET]
  ++ `measure v o A --> measure v (BIGINTER (IMAGE A UNIV))`
      by METIS_TAC [MONOTONE_CONVERGENCE_BIGINTER2, IN_UNIV, IN_FUNSET]
  ++ `BIGINTER (IMAGE A UNIV) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_BIGINTER]
  ++ FULL_SIMP_TAC std_ss [o_DEF]
  ++ `(\n. -d (A n)) --> -d (BIGINTER (IMAGE A UNIV))`
      by (Q.UNABBREV_TAC `d`
          ++ RW_TAC std_ss [SEQ_SUB, REAL_NEG_SUB])
  ++ `!n. -d (A (SUC n)) <= -d (A n)` by METIS_TAC [REAL_LE_NEG]
  ++ `!n. (\n. -d (A n)) (n + 1) <= (\n. -d (A n)) n`
           by METIS_TAC [ADD1]
  ++ `-d (BIGINTER (IMAGE A univ(:num))) <= (\n. -d (A n)) 0`
       by (MATCH_MP_TAC SEQ_LE_MONO
           ++ RW_TAC std_ss [])
  ++ `d (m_space m) <= d (BIGINTER (IMAGE A UNIV))` by METIS_TAC [REAL_LE_NEG]
  ++ METIS_TAC []);

val Radon_Nikodym = store_thm
  ("Radon_Nikodym",``!m v. measure_space m /\ measure_space v /\
  			   (m_space v = m_space m) /\
			   (measurable_sets v = measurable_sets m) /\
			   measure_absolutely_continuous v m
            ==> (?f. f IN measurable (m_space m, measurable_sets m) Borel /\ (!x. 0 <= f x) /\
                (!A. A IN measurable_sets m ==>
		     (pos_fn_integral m (\x. f x * indicator_fn A x) = Normal (measure v A))))``,
  RW_TAC std_ss []
  ++ `?f_n. (!n. f_n n IN RADON_F m v) /\ (!x n. f_n n x <= f_n (SUC n) x) /\
           (sup (IMAGE (\n. pos_fn_integral m (f_n n)) univ(:num)) =
	    sup (RADON_F_integrals m v))`
       by RW_TAC std_ss [lemma_radon_seq_conv_sup]
  ++ Q.ABBREV_TAC `g = (\x. sup (IMAGE (\n. f_n n x) UNIV))`
  ++ Q.EXISTS_TAC `g`
  ++ `g IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
          ++ Q.EXISTS_TAC `f_n`
          ++ FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, measure_space_def, space_def]
          ++ Q.UNABBREV_TAC `g`
          ++ RW_TAC std_ss [])
  ++ `!x. 0 <= g x`
       by (Q.UNABBREV_TAC `g`
           ++ RW_TAC std_ss [le_sup]
           ++ MATCH_MP_TAC le_trans
	   ++ Q.EXISTS_TAC `f_n 0 x`
	   ++ RW_TAC std_ss []
	   >> FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION]
	   ++ POP_ASSUM MATCH_MP_TAC
	   ++ ONCE_REWRITE_TAC [GSYM SPECIFICATION]
	   ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
	   ++ METIS_TAC [])
  ++ RW_TAC std_ss []
  ++ `!A. A IN measurable_sets m ==>
     	  (pos_fn_integral m (\x. g x * indicator_fn A x) =
	   sup (IMAGE (\n. pos_fn_integral m (\x. f_n n x * indicator_fn A x)) UNIV))`
       by (RW_TAC std_ss []
	   ++ MATCH_MP_TAC lebesgue_monotone_convergence_subset
           ++ FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, ext_mono_increasing_suc]
	   ++ RW_TAC std_ss []
	   ++ Q.UNABBREV_TAC `g`
	   ++ METIS_TAC [])
  ++ `g IN RADON_F m v`
      by (FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, sup_le]
          ++ RW_TAC std_ss []
	  ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
	  ++ RW_TAC std_ss [IN_IMAGE,IN_UNIV]
	  ++ METIS_TAC [])
  ++ `pos_fn_integral m g = sup (IMAGE (\n:num. pos_fn_integral m (f_n n)) UNIV)`
       by (MATCH_MP_TAC lebesgue_monotone_convergence
           ++ FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, ext_mono_increasing_suc]
	   ++ Q.UNABBREV_TAC `g`
	   ++ METIS_TAC [])
  ++ `pos_fn_integral m g = sup (RADON_F_integrals m v)` by FULL_SIMP_TAC std_ss []
  ++ `!A. A IN measurable_sets m ==>
     	  pos_fn_integral m (\x. g x * indicator_fn A x) <= Normal (measure v A)`
       by FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION]
  ++ `!A x. 0 <= (\x. g x * indicator_fn A x) x`
       by RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone, le_01, le_refl]
  ++ `!A. A IN measurable_sets m ==> 0 <= pos_fn_integral m (\x. g x * indicator_fn A x)`
          by (REPEAT STRIP_TAC ++ MATCH_MP_TAC pos_fn_integral_pos ++ METIS_TAC [])
  ++ `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g x * indicator_fn A x) <> NegInf`
       by METIS_TAC [lt_infty,extreal_of_num_def,extreal_not_infty,lte_trans]
  ++ `!A. A IN measurable_sets m ==> pos_fn_integral m (\x. g x * indicator_fn A x) <> PosInf`
       by METIS_TAC [let_trans,lt_infty]
  ++ `?Ig. !A. A IN measurable_sets m ==>
      (pos_fn_integral m (\x. g x * indicator_fn A x) = Normal (Ig A))`
      by (Q.EXISTS_TAC `(\A. @Ig. pos_fn_integral m (\x. g x * indicator_fn A x) = Normal (Ig))`
           ++ RW_TAC std_ss []
	   ++ METIS_TAC [extreal_cases])
  ++ RW_TAC std_ss []
  ++ Q.ABBREV_TAC `nu = (\A. measure v A - Ig A)`
  ++ `!A. A IN measurable_sets m ==> 0 <= nu A`
       by (RW_TAC std_ss []
           ++ FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION]
	   ++ METIS_TAC [extreal_le_def, sub_zero_le, extreal_of_num_def, extreal_sub_def])
  ++ `positive (m_space m, measurable_sets m, nu)`
       by (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
	   ++ Q.UNABBREV_TAC `nu`
	   ++ RW_TAC std_ss [MEASURE_EMPTY]
	   ++ Q.PAT_ASSUM `!A. A IN measurable_sets m ==> (Q = Normal P)`
	      		(MP_TAC o GSYM o Q.SPEC `{}`)
	   ++ RW_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE, indicator_fn_def, NOT_IN_EMPTY,
	      	     	     pos_fn_integral_zero, mul_rzero,mul_rone]
           ++ `IMAGE (\n. 0) univ(:num) = (\y. y = 0)`
	       by RW_TAC std_ss [EXTENSION, IN_IMAGE, IN_UNIV, IN_ABS]
	   ++ FULL_SIMP_TAC real_ss [sup_const, extreal_of_num_def, extreal_11])
  ++ Q.PAT_ASSUM `!A. A IN measurable_sets m
     ==> (pos_fn_integral m (\x. g x * indicator_fn A x) = sup Q)` (K ALL_TAC)
  ++ RW_TAC std_ss []
  ++ `measure_space (m_space m, measurable_sets m, nu)`
      by (FULL_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def,
      	 		        countably_additive_def,measure_def]
          ++ Q.UNABBREV_TAC `nu`
          ++ RW_TAC std_ss [o_DEF]
	  ++ `(\x. measure v (f x)) sums measure v (BIGUNION (IMAGE f univ(:num)))`
               by METIS_TAC [o_DEF,countably_additive_def]
	  ++ Suff `(\x. Ig (f x)) sums Ig (BIGUNION (IMAGE f univ(:num)))`
	  >> METIS_TAC [SER_SUB]
	  ++ `measure_space m` by METIS_TAC [measure_space_def, countably_additive_def]
	  ++ RW_TAC std_ss [sums]
	  ++ Know `mono_increasing (\n. sum (0,n) (\x. Ig (f x)))`
	  >> (RW_TAC std_ss [mono_increasing_def, GSYM extreal_le_def, GSYM REAL_SUM_IMAGE_COUNT]
	      ++ RW_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_NORMAL, FINITE_COUNT]
	      ++ MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
	      ++ RW_TAC std_ss [FINITE_COUNT, SUBSET_DEF, IN_COUNT]
	      >> METIS_TAC [LESS_LESS_EQ_TRANS]
	      ++ METIS_TAC [IN_UNIV, IN_FUNSET])
	  ++ RW_TAC std_ss [sup_seq, GSYM REAL_SUM_IMAGE_COUNT, GSYM EXTREAL_SUM_IMAGE_NORMAL,
	     	     	    FINITE_COUNT]
          ++ RW_TAC std_ss [GSYM ext_suminf_def]
	  ++ FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV]
	  ++ Q.PAT_ASSUM `!A. A IN measurable_sets m ==>
                   (pos_fn_integral m (\x. g x * indicator_fn A x) = Normal (Ig A))`
		     (MP_TAC o GSYM)
	  ++ RW_TAC std_ss []
	  ++ `!i x. 0 <= (\i x. g x * indicator_fn (f i) x) i x`
	      by RW_TAC std_ss [mul_rzero, mul_rone, indicator_fn_def, le_refl]
	  ++ `!i. (\i x. g x * indicator_fn (f i) x) i
	     	      IN measurable (m_space m,measurable_sets m) Borel`
               by (RW_TAC std_ss []
		   ++ METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, IN_FUNSET, IN_UNIV,
		      		 measurable_sets_def,subsets_def])
	  ++ (MP_TAC o Q.SPECL [`m`,`(\i:num. (\x. g x * indicator_fn (f i) x))`] o GSYM)
	     	     pos_fn_integral_suminf
	  ++ RW_TAC std_ss []
	  ++ Suff `(\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x) =
                   (\x'. suminf (\x. g x' * indicator_fn (f x) x'))`
          >> RW_TAC std_ss []
	  ++ RW_TAC std_ss [FUN_EQ_THM]
	  ++ `suminf (\x. g x' * (\x. indicator_fn (f x) x') x) =
	      g x' * suminf (\x. indicator_fn (f x) x')`
              by (MATCH_MP_TAC ext_suminf_cmul
                  ++ RW_TAC std_ss [mul_rone, mul_rzero, le_refl, indicator_fn_def, le_01])
          ++ FULL_SIMP_TAC std_ss []
	  ++ Suff `suminf (\i. indicator_fn (f i) x') =
	     	   indicator_fn (BIGUNION (IMAGE f univ(:num))) x'`
          >> RW_TAC std_ss []
	  ++ FULL_SIMP_TAC std_ss [indicator_fn_suminf])
  ++ `!A. A IN measurable_sets m ==> nu A <= nu (m_space m)`
      by METIS_TAC [MEASURE_SPACE_INCREASING, INCREASING, MEASURE_SPACE_SUBSET_MSPACE,
      	 	    measure_def, measurable_sets_def, m_space_def,
		    MEASURE_SPACE_MSPACE_MEASURABLE]

  ++ Cases_on `nu A = 0` >> METIS_TAC [REAL_SUB_0]
  ++ `0 < nu A` by METIS_TAC [REAL_LT_LE, MEASURE_SPACE_POSITIVE, positive_def]
  ++ `0 < nu (m_space m)` by METIS_TAC [REAL_LTE_TRANS]
  ++ `0 <> measure m (m_space m)`
       by (SPOSE_NOT_THEN ASSUME_TAC
           ++ `measure v (m_space m) = 0`
	       by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_absolutely_continuous_def]
           ++ `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) <= 0`
	       by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, extreal_of_num_def]
           ++ `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) =  0`
	       by METIS_TAC [le_antisym, MEASURE_SPACE_MSPACE_MEASURABLE]
	   ++ `Ig (m_space m) = 0` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,
	      	  	      	      		 extreal_of_num_def, extreal_11]
           ++ `nu (m_space m) = 0` by (Q.UNABBREV_TAC `nu` ++ METIS_TAC [REAL_SUB_RZERO])
           ++ METIS_TAC [REAL_LT_IMP_NE])
  ++ `0 < measure m (m_space m)` by METIS_TAC [REAL_LT_LE, MEASURE_SPACE_POSITIVE, positive_def,
     	  	    	     	    	       MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ Q.ABBREV_TAC `e = nu (m_space m) / (2 * measure m (m_space m))`
  ++ `0 < e` by METIS_TAC [REAL_LT_DIV, REAL_LT_MUL, EVAL ``0 < 2:real``]
  ++ Q.ABBREV_TAC `snu = (\A. nu A - e * (measure m A))`
  ++ `?A'. A' IN measurable_sets m /\ snu (m_space m) <= snu (A') /\
       (!B. B IN measurable_sets m /\ B SUBSET A' ==> 0 <= snu (B))`
        by (Q.UNABBREV_TAC `snu`
            ++ RW_TAC std_ss []
	    ++ (MP_TAC o Q.SPECL [`(m_space m, measurable_sets m, nu)`,
	       	       `(m_space m, measurable_sets m, (\A. e * measure m A))`]) RN_lemma2
	    ++ RW_TAC std_ss [m_space_def,measurable_sets_def,measure_def]
	    ++ METIS_TAC [MEASURE_SPACE_CMUL,REAL_LT_IMP_LE])
  ++ Q.ABBREV_TAC `g' = (\x. g x + Normal e * indicator_fn (A') x)`
  ++ `!A. A IN measurable_sets m ==>
          (pos_fn_integral m (\x. g' x * indicator_fn A x) =
           pos_fn_integral m (\x. g x * indicator_fn A x) + Normal (e * measure m (A INTER A')))`
       by (REPEAT STRIP_TAC
           ++ `Normal (e * measure m (A'' INTER A')) =
	       Normal e * pos_fn_integral m (indicator_fn (A'' INTER A'))`
                by METIS_TAC [pos_fn_integral_indicator,MEASURE_SPACE_INTER, extreal_mul_def]
           ++ POP_ORW
	   ++ `Normal e * pos_fn_integral m (indicator_fn (A'' INTER A')) =
               pos_fn_integral m (\x. Normal e * indicator_fn (A'' INTER A') x)`
                by ((MATCH_MP_TAC o GSYM) pos_fn_integral_cmul
                    ++ RW_TAC real_ss [REAL_LT_IMP_LE,indicator_fn_def,le_01,le_refl])
           ++ POP_ORW
	   ++ Q.UNABBREV_TAC `g'`
	   ++ `(\x. (\x. g x + Normal e * indicator_fn A' x) x * indicator_fn A'' x) =
               (\x. (\x. g x * indicator_fn A'' x) x +
	           (\x. Normal e * indicator_fn (A'' INTER A') x) x)`
                by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,IN_INTER]
                    ++ METIS_TAC [mul_rone,mul_rzero,add_rzero,indicator_fn_def,IN_INTER])
           ++ POP_ORW
	   ++ MATCH_MP_TAC pos_fn_integral_add
	   ++ FULL_SIMP_TAC std_ss []
	   ++ CONJ_TAC
	   >> (RW_TAC std_ss [indicator_fn_def, le_01, le_refl, mul_rone, mul_rzero]
               ++ FULL_SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def, REAL_LT_IMP_LE])
           ++ RW_TAC std_ss []
	   >> METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
	      		 measurable_sets_def, subsets_def]
	   ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
	   ++ RW_TAC std_ss []
	   ++ Q.EXISTS_TAC `indicator_fn (A'' INTER A')`
	   ++ Q.EXISTS_TAC `e`
	   ++ RW_TAC std_ss []
	   >> FULL_SIMP_TAC std_ss [measure_space_def]
	   ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
	   ++ METIS_TAC [measure_space_def, measurable_sets_def, subsets_def, MEASURE_SPACE_INTER,
	      		 space_def])
  ++ `!A. A IN measurable_sets m ==> ((A INTER A') IN measurable_sets m /\
     	  (A INTER A') SUBSET A')`
         by METIS_TAC [INTER_SUBSET, MEASURE_SPACE_INTER]
  ++ `!A. A IN measurable_sets m ==> 0 <= nu (A INTER A') - e * measure m (A INTER A')`
         by (Q.UNABBREV_TAC `snu` ++ METIS_TAC [])
  ++ `!A. A IN measurable_sets m ==> e * measure m (A INTER A') <= nu (A INTER A')`
         by (RW_TAC std_ss []
             ++ METIS_TAC [REAL_SUB_LE])
  ++ `!A. A IN measurable_sets m ==>
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal (e * measure m (A INTER A')) <=
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal (nu (A INTER A'))`
         by METIS_TAC [le_ladd_imp, extreal_le_def]
  ++ `!A. A IN measurable_sets m ==> nu (A INTER A') <= nu A`
         by (RW_TAC std_ss []
             ++ (MATCH_MP_TAC o REWRITE_RULE [measurable_sets_def, measure_def] o
	     	 Q.SPEC `(m_space m,measurable_sets m,nu)`) INCREASING
	     ++ METIS_TAC [MEASURE_SPACE_INCREASING, MEASURE_SPACE_INTER, INTER_SUBSET])
  ++ `!A. A IN measurable_sets m ==>
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal (e * measure m (A INTER A')) <=
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal (nu (A))`
           by METIS_TAC [le_ladd_imp,le_trans, extreal_le_def]
  ++ `!A. A IN measurable_sets m ==>
          pos_fn_integral m (\x. g x * indicator_fn A x) + Normal (e * measure m (A INTER A')) <=
	  Normal (measure v A)`
           by (Q.UNABBREV_TAC `nu`
               ++ FULL_SIMP_TAC std_ss []
               ++ RW_TAC std_ss []
               ++ METIS_TAC [sub_add2, extreal_not_infty, extreal_sub_def])
  ++ `!A. A IN measurable_sets m  ==>
     	  pos_fn_integral m (\x. g' x * indicator_fn A x) <= Normal (measure v A)`
        by METIS_TAC []
  ++ `g' IN RADON_F m v`
         by (RW_TAC std_ss [RADON_F_def,GSPECIFICATION]
             >> (Q.UNABBREV_TAC `g'`
                 ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
                 ++ Q.EXISTS_TAC `g`
		 ++ Q.EXISTS_TAC `(\x. Normal e * indicator_fn A' x)`
		 ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [measure_space_def]
		 ++ FULL_SIMP_TAC std_ss []
                 ++ MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
		 ++ METIS_TAC [measure_space_def, subsets_def, measurable_sets_def,
		    	       IN_MEASURABLE_BOREL_INDICATOR])
	     ++ Q.UNABBREV_TAC `g'`
	     ++ RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, add_rzero]
	     ++ METIS_TAC [le_add2, add_rzero, le_trans, lt_imp_le, extreal_lt_eq,
	     		   extreal_of_num_def])
  ++ `pos_fn_integral m g' IN RADON_F_integrals m v`
       by (FULL_SIMP_TAC std_ss [RADON_F_integrals_def, GSPECIFICATION]
           ++ METIS_TAC [])
  ++ `pos_fn_integral m (\x. g' x * indicator_fn (m_space m) x) =
      pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) +
      Normal (e * measure m A')`
         by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, MEASURE_SPACE_SUBSET_MSPACE,SUBSET_INTER2]
  ++ `!x. 0 <= g' x`
      by (Q.UNABBREV_TAC `g'`
          ++ RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, add_rzero]
	  ++ METIS_TAC [le_add2,add_rzero, le_trans, lt_imp_le, extreal_lt_eq,extreal_of_num_def])
  ++ `pos_fn_integral m g' = pos_fn_integral m g + Normal (e * measure m A')`
       by METIS_TAC [pos_fn_integral_mspace]
  ++ `0 < snu (m_space m)`
       by (Q.UNABBREV_TAC `snu`
           ++ Q.UNABBREV_TAC `e`
	   ++ RW_TAC real_ss [real_div,REAL_INV_MUL,REAL_LT_IMP_NE,REAL_MUL_ASSOC]
	   ++ `inv 2 * inv (measure m (m_space m)) * measure m (m_space m) = inv 2`
                by METIS_TAC [REAL_LT_IMP_NE,REAL_MUL_LINV,REAL_MUL_ASSOC,REAL_MUL_RID]
	   ++ `nu (m_space m) - nu (m_space m) * inv 2 *
	      	  	        inv (measure m (m_space m)) * measure m (m_space m) =
	       nu (m_space m) / 2`
                by METIS_TAC [REAL_NEG_HALF,real_div,REAL_MUL_ASSOC]
 	   ++ FULL_SIMP_TAC real_ss [REAL_LT_DIV])
  ++ `0 < snu A'` by METIS_TAC [REAL_LTE_TRANS]
  ++ `e * measure m A' < nu (A')` by METIS_TAC [REAL_SUB_LT]
  ++ `0 <= e * measure m A'` by METIS_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, MEASURE_SPACE_POSITIVE,positive_def]
  ++ `0 < nu A'` by METIS_TAC [REAL_LET_TRANS]
  ++ `0 <> measure m A'`
        by (SPOSE_NOT_THEN ASSUME_TAC
            ++ `measure v A' = 0` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,
	       		       	     	        measure_absolutely_continuous_def]
            ++ `pos_fn_integral m (\x. g x * indicator_fn A' x) <= 0`
	        by METIS_TAC [extreal_of_num_def]
            ++ `pos_fn_integral m (\x. g x * indicator_fn A' x) =  0`
	        by METIS_TAC [REAL_LE_ANTISYM, extreal_of_num_def, extreal_le_def]
	    ++  `Ig A' = 0` by METIS_TAC [extreal_of_num_def, extreal_11]
            ++ `nu A' = 0` by (Q.UNABBREV_TAC `nu` ++ RW_TAC real_ss [])
            ++ METIS_TAC [REAL_LT_IMP_NE])
  ++ `0 < measure m A'` by METIS_TAC [REAL_LT_LE, MEASURE_SPACE_POSITIVE, positive_def,
     	  	    	   	      MEASURE_SPACE_MSPACE_MEASURABLE]
  ++ `0 < e * measure m A'` by METIS_TAC [REAL_LT_MUL]
  ++ `0 < Normal (e * measure m A')` by METIS_TAC [extreal_of_num_def, extreal_lt_eq]
  ++ `pos_fn_integral m g <> NegInf`
      by METIS_TAC [pos_fn_integral_pos,lt_infty,num_not_infty,lte_trans]
  ++ `pos_fn_integral m g <> PosInf`
      by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,pos_fn_integral_mspace]
  ++ `pos_fn_integral m g < pos_fn_integral m g'` by METIS_TAC [let_add2,le_refl,add_rzero]
  ++ `pos_fn_integral m g' <= pos_fn_integral m g` by METIS_TAC [le_sup_imp,SPECIFICATION]
  ++ METIS_TAC [extreal_lt_def]);

val Radon_Nikodym2 = store_thm
  ("Radon_Nikodym2",``!m v. measure_space m /\ measure_space v /\ (m_space v = m_space m) /\
         (measurable_sets v = measurable_sets m) /\ measure_absolutely_continuous v m
            ==> (?f. f IN measurable (m_space m,measurable_sets m) Borel /\
	    	(!x. 0 <= f x) /\  (!x. f x <> PosInf) /\
                (!A. A IN measurable_sets m ==>
		     (pos_fn_integral m (\x. f x * indicator_fn A x) = Normal (measure v A))))``,
  RW_TAC std_ss []
  ++ `?g. g IN measurable (m_space m,measurable_sets m) Borel /\
     	  (!x. 0 <= g x) /\
          (!A. A IN measurable_sets m ==>
	       (pos_fn_integral m (\x. g x * indicator_fn A x) = Normal (measure v A)))`
      by METIS_TAC [Radon_Nikodym]
  ++ Q.EXISTS_TAC `\x. if g x = PosInf then 0 else g x`
  ++ RW_TAC std_ss [le_refl,num_not_infty]
  >> (`integrable m g` by METIS_TAC [integrable_pos, pos_fn_integral_mspace,
     		       	  	     MEASURE_SPACE_MSPACE_MEASURABLE, extreal_not_infty]
      ++ METIS_TAC [integrable_not_infty_alt2, integrable_def])
  ++ `pos_fn_integral m (\x. g x * indicator_fn A x) = Normal (measure v A)` by METIS_TAC []
  ++ `!x. 0 <= g x * indicator_fn A x` by METIS_TAC [indicator_fn_def,mul_rzero,le_refl,mul_rone]
  ++ `integrable m (\x. g x * indicator_fn A x)`
      by (MATCH_MP_TAC integrable_bounded
          ++ Q.EXISTS_TAC `g`
	  ++ RW_TAC std_ss []
	  <<[METIS_TAC [integrable_pos,pos_fn_integral_mspace,MEASURE_SPACE_MSPACE_MEASURABLE,
		        extreal_not_infty],
	     METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measurable_sets_def, measure_space_def,
	     	        subsets_def],
	     METIS_TAC [abs_refl, mul_rone, mul_rzero, le_refl, indicator_fn_def]])
  ++ (MP_TAC o Q.SPECL [`m`,`(\x. g x * indicator_fn A x)`]) integrable_not_infty_alt2
  ++ Suff `(\x. (if g x = PosInf then 0 else g x) * indicator_fn A x) =
           (\x. if g x * indicator_fn A x = PosInf then 0 else g x * indicator_fn A x)`
  >> RW_TAC std_ss []
  ++ RW_TAC std_ss [FUN_EQ_THM]
  ++ METIS_TAC [mul_lzero,mul_rzero,mul_lone,mul_rone,num_not_infty,indicator_fn_def]);

val _ = export_theory();