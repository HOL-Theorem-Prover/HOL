
open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory;


val _ = new_theory "set_sep";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val PAIR_EQ = pairTheory.PAIR_EQ;


(* ----------------------------------------------------------------------------- *)
(* Definitions                                                                   *)
(* ----------------------------------------------------------------------------- *)

val emp_def = Define `emp = \s. (s = {})`;
val one_def = Define `one x = \s. ({x} = s)`;
val cond_def = Define `cond c = \s. (s = {}) /\ c`;

val mute_def = Define `mute (x:'a set -> bool) = (x,emp)`;
val immute_def = Define `immute (x:'a set -> bool) = (emp,x)`;
val cond2_def = Define `cond2 c = (cond c,emp)`;

val SPLIT_def = Define `SPLIT (s:'a set) (u,v) = (u UNION v = s) /\ DISJOINT u v`;
val STAR_def = Define `STAR P Q = (\s. ?u v. SPLIT s (u,v) /\ P u /\ Q v)`;
val SEP_HIDE_def = Define `SEP_HIDE P = \s. ?x. P x s`;

val _ = overload_on ("*",Term`STAR`);
val _ = overload_on ("~",Term`SEP_HIDE`);

val SEP_T_def = Define `SEP_T s = T`;
val SEP_F_def = Define `SEP_F s = F`;

val SEP_CONJ_def = Define `SEP_CONJ P Q = (\s. P s /\ Q s)`;
val SEP_DISJ_def = Define `SEP_DISJ P Q = (\s. P s \/ Q s)`;
val SEP_NOT_def  = Define `SEP_NOT P = (\s. ~((P s):bool))`;
val SEP_ADD_def = Define `SEP_ADD P Q = SEP_CONJ (STAR P SEP_T) (STAR Q SEP_T)`;

val SEP_IMP_def  = Define `SEP_IMP P Q = !s. P s ==> Q s`;
val SEP_IMP2_def  = Define `SEP_IMP2 (P,P') (Q,Q') = SEP_IMP P Q /\ SEP_IMP Q Q'`;

val _ = overload_on ("/\\",Term`SEP_CONJ`);
val _ = overload_on ("\\/",Term`SEP_DISJ`);

val SEP_EXISTS = new_binder_definition("SEP_EXISTS",
   ``($SEP_EXISTS) = \f s:'a set. $? (\y. f y s)``);

val SEP_FORALL = new_binder_definition("SEP_FORALL",
   ``($SEP_FORALL) = \f s:'a set. $! (\y. f y s)``);

val SEP_BIGDISJ_def = Define `
  SEP_BIGDISJ Z s = ?P. P IN Z /\ P s`;

val SEP_BIGCONJ_def = Define `
  SEP_BIGCONJ Z s = !P. P IN Z ==> P s`;

val ALL_DISJOINT_def = Define `
  ALL_DISJOINT Z = !z z'. z IN Z /\ z' IN Z ==> DISJOINT z z' \/ (z = z')`;

val BIGSPLIT_def = Define `
  BIGSPLIT s Z = (BIGUNION Z = s) /\ ALL_DISJOINT Z`;

val bijection'_def = Define `
  bijection' f Z Q = (!z::Z. ?q::Q. (f z = q)) /\ 
                    (!q::Q. ?z::Z. (f z = q)) /\ 
                    (!z z'::Z. (f z = f z') ==> (z = z') \/ (f z = {}))`;

val BIGSTAR_def = Define `
  BIGSTAR Z = \s. ?Q f. BIGSPLIT s Q /\ bijection' f Z Q /\ !z::Z. z (f z)`;

val STAR2_def = Define `
  STAR2 (P,P') (Q,Q') = (P * Q, SEP_ADD P' Q')`;

val SEP_JOIN_def = Define `
  SEP_JOIN (P,Q) = P * Q * SEP_T`;

val _ = overload_on ("**",Term`STAR2`);


(* ----------------------------------------------------------------------------- *)
(* Lemmas about SPLIT                                                            *)
(* ----------------------------------------------------------------------------- *)

val SPLIT_ss = rewrites [SPLIT_def,SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,IN_INSERT,
                         EXTENSION,NOT_IN_EMPTY,IN_DEF,IN_UNION,IN_INTER,IN_DIFF];

val SPLIT_TAC = SIMP_TAC (pure_ss++SPLIT_ss) [] \\ METIS_TAC [];

fun SPLIT_PROVE tm = prove(tm,SPLIT_TAC);

val SPLIT_SPLIT = SPLIT_PROVE
  ``!x y z z1 z2. 
      SPLIT x (z,y) /\ SPLIT z (z1,z2) ==> 
      (x = y UNION z1 UNION z2) /\ DISJOINT y z1 /\ DISJOINT y z2 /\ DISJOINT z1 z2``;

val SPLIT_UNION = SPLIT_PROVE
  ``!u v. DISJOINT v u ==> SPLIT (v UNION u) (v,u)``;

val SPLIT_SYM = SPLIT_PROVE
  ``!x u v. SPLIT x (u,v) = SPLIT x (v,u)``;

val SPLIT_NOT_IN = SPLIT_PROVE
  ``!x y u v. SPLIT x (u,v) /\ ~(y IN v) /\ y IN x ==> y IN u``;

val SUBSET_DISJOINT = SPLIT_PROVE
  ``x SUBSET x' /\ DISJOINT x' y ==> DISJOINT x y``;

val SUBSET_UNION = SPLIT_PROVE
  ``!x y z. (x UNION y = z) ==> x SUBSET z``;

val SPLIT_SPLIT_UNION = SPLIT_PROVE
  ``!x y z1 z2. SPLIT x (z,y) /\ SPLIT z (z1,z2) ==> SPLIT x (z1,z2 UNION y)``;

val SPLIT_EMPTY_LEMMA = SPLIT_PROVE
  ``!x s. SPLIT s (x,{}) = (s=x)``;

val SPLIT_EMPTY = SPLIT_PROVE
  ``!x s. (SPLIT s (x,{}) = (s=x)) /\ (SPLIT s ({},x) = (s=x))``;

val SPLIT_SUBSET = SPLIT_PROVE
  ``!x u v. SPLIT x (u,v) ==> u SUBSET x /\ v SUBSET x``;

val SPLIT_SWITCH = SPLIT_PROVE
  ``!s u v x. ~(x IN v) /\ SPLIT s (u,v UNION {x}) ==> SPLIT s (u UNION {x},v)``;

val SPLIT_SWITCH_EQ = SPLIT_PROVE
  ``!x u v s. 
      ~(x IN u) /\ ~(x IN v) ==>
      (SPLIT s (u UNION {x},v) = SPLIT s (u,{x} UNION v))``;

val SPLIT_EQ_DIFF_LEMMA = SPLIT_PROVE
  ``!s u v. SPLIT s (u,v) ==> (u = s DIFF v)``;

val SPLIT_EQ_DIFF = SPLIT_PROVE
  ``!s u v. SPLIT s (u,v) ==> (u = s DIFF v) /\ (v = s DIFF u)``;

val SPLIT_SUBSET_DIFF = SPLIT_PROVE
  ``!s u. u SUBSET s ==> SPLIT s (u,s DIFF u)``;

val DISJOINT_DIFF = SPLIT_PROVE
  ``!x y. DISJOINT x (y DIFF x)``;

val SPLIT_SUBSET_DIFF = SPLIT_PROVE
  ``!t s. t SUBSET s ==> SPLIT s (t,s DIFF t)``;

val SPLIT_DIFF = SPLIT_PROVE
  ``!x s. x IN s ==> SPLIT s ({x},s DIFF {x})``;

val SUBSET_SPLIT_DIFF = SPLIT_PROVE
  ``!x y. y SUBSET x ==> SPLIT x (y,x DIFF y)``;

val SPLIT_SEPARATE = SPLIT_PROVE
  ``!s u v x. SPLIT s (u,v) /\ x IN u ==> ~(x IN v)``;

val SUBSET_SPLIT = SPLIT_PROVE
  ``!s t. t SUBSET s ==> SPLIT s (t,s DIFF t) /\ SPLIT s (s DIFF t,t)``;

val SPLIT_NOT_SUBSET = SPLIT_PROVE
  ``!x u v. ~(u = {}) /\ SPLIT x (u,v) ==> ~(u SUBSET v)``;


(* ----------------------------------------------------------------------------- *)
(* Lemmas about BIGSPLIT                                                         *)
(* ----------------------------------------------------------------------------- *)

val BIGSPLIT_EMPTY = prove(
  ``!s. (BIGSPLIT s {} = (s = {})) /\ (BIGSPLIT s {{}} = (s = {}))``,
  SRW_TAC [] [BIGSPLIT_def,ALL_DISJOINT_def] \\ METIS_TAC []);

val BIGSPLIT_SUBSET = prove(
  ``!Q s q. BIGSPLIT s Q /\ q IN Q ==> q SUBSET s``,
  SRW_TAC [] [BIGSPLIT_def,SUBSET_DEF]
  \\ `Q = q INSERT Q` by METIS_TAC [IN_INSERT,EXTENSION]
  \\ ONCE_ASM_REWRITE_TAC []
  \\ REWRITE_TAC [BIGUNION_INSERT,IN_UNION]
  \\ METIS_TAC []);

val BIGSPLIT_DIFF = prove(
  ``!s Q q. BIGSPLIT s Q /\ q IN Q ==> BIGSPLIT (s DIFF q) (Q DELETE q)``,
  SRW_TAC [] [BIGSPLIT_def,ALL_DISJOINT_def]
  \\ REWRITE_TAC [DELETE_DEF] 
  \\ REWRITE_TAC [BIGUNION] 
  \\ REWRITE_TAC [IN_DIFF,IN_INSERT,NOT_IN_EMPTY,EXTENSION] 
  \\ SIMP_TAC bool_ss [GSPECIFICATION]
  \\ REPEAT STRIP_TAC
  \\ SIMP_TAC bool_ss [PAIR_EQ]
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `s` \\ ASM_REWRITE_TAC [], 
    `~(s = q)` by METIS_TAC []
    \\ `DISJOINT s q` by METIS_TAC []
    \\ METIS_TAC [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY],
    Q.EXISTS_TAC `s`
    \\ ASM_REWRITE_TAC []    
    \\ Q.EXISTS_TAC `x`
    \\ ASM_REWRITE_TAC []]);

val ALL_DISJOINT_INSERT = prove(
  ``DISJOINT u (BIGUNION Q) /\ ALL_DISJOINT Q ==> ALL_DISJOINT (u INSERT Q)``,
  REWRITE_TAC [DISJOINT_DEF,ALL_DISJOINT_def,EXTENSION,IN_INTER,
               IN_INSERT,NOT_IN_EMPTY,IN_BIGUNION]
  \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC []
  THEN1 METIS_TAC []
  THEN1 METIS_TAC []
  \\ PAT_ASSUM ``!x:'a y:'b. b`` 
      (STRIP_ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o SPEC_ALL)
  \\ ASM_REWRITE_TAC []);
 
val BIGSPLIT_INSERT = prove(
  ``!x u v Q. SPLIT x (u,v) /\ BIGSPLIT v Q ==> BIGSPLIT x (u INSERT Q)``,
  SRW_TAC [] [BIGSPLIT_def,SPLIT_def] \\ METIS_TAC [ALL_DISJOINT_INSERT]);
  
val BIGSPLIT_DELETE_EMPTY = prove(
  ``!s Q. BIGSPLIT s Q ==> BIGSPLIT s (Q DELETE {})``,
  SRW_TAC [] [BIGSPLIT_def]
  \\ FULL_SIMP_TAC bool_ss [ALL_DISJOINT_def,BIGUNION,IN_DELETE]
  \\ SIMP_TAC bool_ss [EXTENSION,GSPECIFICATION,PAIR_EQ]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `s` \\ ASM_REWRITE_TAC [],
    Q.EXISTS_TAC `s` \\ ASM_REWRITE_TAC [NOT_IN_EMPTY] \\ METIS_TAC []]);

val SPLIT_BIGSPLIT_NOT_IN = prove(
  ``!x u v Q. ~(u = {}) /\ SPLIT x (u,v) /\ BIGSPLIT v Q ==> ~(u IN Q)``,
  METIS_TAC [SPLIT_NOT_SUBSET,BIGSPLIT_SUBSET]);

val SPLIT_BIGSPLIT_NOT_EQ = prove(
  ``!x u v Q q. ~(q = {}) /\ q IN Q /\ SPLIT x (u,v) /\ BIGSPLIT v Q ==> ~(u = q)``,
  METIS_TAC [SPLIT_BIGSPLIT_NOT_IN]);

val BIGSPLIT_BIGUNION = prove(
  ``!Z. ALL_DISJOINT Z ==> BIGSPLIT (BIGUNION Z) Z``,
  SRW_TAC [] [BIGSPLIT_def,BIGUNION]);  


(* ----------------------------------------------------------------------------- *)
(* Main theorems                                                                 *)
(* ----------------------------------------------------------------------------- *)

val STAR_ABS = let 
  val access = QUANT_CONV o QUANT_CONV o RHS_CONV o ABS_CONV o QUANT_CONV
  val step1 = UNBETA_CONV ``u:'a set``
  val step2 = UNBETA_CONV ``v:'a set``
  val trans = RATOR_CONV o ABS_CONV o QUANT_CONV
  in CONV_RULE (access (step1 THENC trans step2)) STAR_def end;

val STAR_SYM = save_thm("STAR_COMM",store_thm("STAR_SYM",
  ``!P:'a set->bool Q. P * Q = Q * P``,
  REWRITE_TAC [STAR_def,SPLIT_def,DISJOINT_DEF]
  \\ METIS_TAC [UNION_COMM,INTER_COMM,CONJ_SYM,CONJ_ASSOC]));

val STAR_ASSOC = store_thm("STAR_ASSOC",
  ``!P:'a set->bool Q R. P * (Q * R) = (P * Q) * R``,
  ONCE_REWRITE_TAC [EXTENSION]
  \\ REPEAT STRIP_TAC
  \\ REWRITE_TAC [STAR_def]
  \\ CONV_TAC (BINOP_CONV (RAND_CONV 
         (ABS_CONV (REWRITE_CONV [GSYM STAR_def] THENC REWRITE_CONV [STAR_ABS]))))
  \\ SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM,GSYM LEFT_EXISTS_AND_THM]
  \\ REWRITE_TAC [IN_DEF] \\ BETA_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `u UNION u'` \\ Q.EXISTS_TAC `v'`
    \\ Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `u'`
    \\ `DISJOINT u u'` by METIS_TAC [SPLIT_SPLIT,SPLIT_SYM]
    \\ `SPLIT (u UNION u') (u,u')` by METIS_TAC [SPLIT_UNION,DISJOINT_SYM]
    \\ ASM_SIMP_TAC std_ss [SPLIT_SPLIT]
    \\ `SPLIT x (v,u)` by METIS_TAC [SPLIT_SYM]
    \\ METIS_TAC [SPLIT_SPLIT_UNION,SPLIT_SYM,UNION_COMM],
    Q.EXISTS_TAC `u'` \\ Q.EXISTS_TAC `v' UNION v` 
    \\ Q.EXISTS_TAC `v'` \\ Q.EXISTS_TAC `v`
    \\ `DISJOINT v v'` by METIS_TAC [SPLIT_SPLIT,SPLIT_SYM]
    \\ `SPLIT (v' UNION v) (v',v)` by METIS_TAC [SPLIT_UNION,DISJOINT_SYM]
    \\ ASM_SIMP_TAC std_ss [SPLIT_SPLIT]
    \\ METIS_TAC [SPLIT_SPLIT_UNION]]);

val STAR_emp_LEMMA = prove(
  ``!P. P * emp = P``,
  REWRITE_TAC [EXTENSION,IN_DEF] \\ BETA_TAC \\ REPEAT STRIP_TAC
  \\ REWRITE_TAC [STAR_def,emp_def] \\ BETA_TAC
  \\ EQ_TAC THEN1 METIS_TAC [SPLIT_EMPTY]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `{}`    
  \\ METIS_TAC [SPLIT_EMPTY]);

val emp_STAR = store_thm("emp_STAR",
  ``!P. (emp * P = P) /\ (P * emp = P)``,
  METIS_TAC [STAR_SYM,STAR_emp_LEMMA]);

val one_STAR = store_thm("one_STAR",
  ``!x s P. (one x * P) s = x IN s /\ P (s DELETE x)``,
  REWRITE_TAC [STAR_def,one_def] \\ BETA_TAC
  \\ REPEAT STRIP_TAC
  \\ EQ_TAC << [
    METIS_TAC [SPLIT_def,IN_UNION,IN_INSERT,SPLIT_EQ_DIFF,DELETE_DEF],
    REWRITE_TAC [DELETE_DEF]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `{x}`
    \\ Q.EXISTS_TAC `s DIFF {x}`
    \\ METIS_TAC [SPLIT_DIFF]]);

val cond_STAR = store_thm("cond_STAR",
  ``!c s P. ((cond c * P) s = c /\ P s) /\ ((P * cond c) s = c /\ P s)``,
  SRW_TAC [] [cond_def,STAR_def,SPLIT_EMPTY] \\ SRW_TAC [] [Once CONJ_SYM]);

val F_STAR = store_thm("F_STAR",
  ``!P. (SEP_F * P = SEP_F) /\ (P * SEP_F = SEP_F)``,
  SRW_TAC [] [STAR_def,SEP_F_def,FUN_EQ_THM]);

val SEP_IMP_REFL = store_thm("SEP_IMP_REFL",
  ``!P. SEP_IMP P P``,
  SRW_TAC [] [SEP_IMP_def]);

val SEP_IMP_TRANS = store_thm("SEP_IMP_TRANS",
  ``!P M Q. SEP_IMP P M /\ SEP_IMP M Q ==> SEP_IMP P Q``,
  SRW_TAC [] [SEP_IMP_def]);

val SEP_IMP_FRAME = store_thm("SEP_IMP_FRAME",
  ``!P Q. SEP_IMP P Q ==> !R. SEP_IMP (P * R) (Q * R)``,
  REWRITE_TAC [STAR_def,SEP_IMP_def] \\ BETA_TAC
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `u`
  \\ Q.EXISTS_TAC `v`
  \\ METIS_TAC []);
    
val SEP_IMP_MONO_DISJ = store_thm("SEP_IMP_MONO_DISJ",
  ``!P Q. SEP_IMP P Q ==> !R. SEP_IMP (P \/ R) (Q \/ R)``,
  SRW_TAC [] [SEP_DISJ_def,SEP_IMP_def] \\ METIS_TAC []);

val SEP_IMP_MONO_CONJ = store_thm("SEP_IMP_MONO_CONJ",
  ``!P Q. SEP_IMP P Q ==> !R. SEP_IMP (P /\ R) (Q /\ R)``,
  SRW_TAC [] [SEP_CONJ_def,SEP_IMP_def] \\ METIS_TAC []);

val SEP_IMP_MOVE_COND = store_thm("SEP_IMP_MOVE_COND",
  ``!c P Q. SEP_IMP (P * cond c) Q = c ==> SEP_IMP P Q``,
  ONCE_REWRITE_TAC [STAR_SYM]
  \\ REWRITE_TAC [SEP_IMP_def,cond_STAR]
  \\ METIS_TAC []);

val SEP_DISJ_ASSOC = store_thm("SEP_DISJ_ASSOC",
  ``!P Q R. P \/ Q \/ R = (P \/ Q) \/ (R:'a set->bool)``,
  SRW_TAC [] [FUN_EQ_THM,SEP_DISJ_def,DISJ_ASSOC]);

val SEP_DISJ_SYM = store_thm("SEP_DISJ_SYM",
  ``!P Q. P \/ Q = Q \/ (P:'a set->bool)``,
  SRW_TAC [] [FUN_EQ_THM,SEP_DISJ_def] \\ METIS_TAC [DISJ_SYM]);

val SEP_CONJ_ASSOC = store_thm("SEP_CONJ_ASSOC",
  ``!P Q R. P /\ Q /\ R = (P /\ Q) /\ (R:'a set->bool)``,
  SRW_TAC [] [FUN_EQ_THM,SEP_CONJ_def,CONJ_ASSOC]);

val SEP_CONJ_SYM = store_thm("SEP_CONJ_SYM",
  ``!P Q. P /\ Q = Q /\ (P:'a set->bool)``,
  SRW_TAC [] [FUN_EQ_THM,SEP_CONJ_def] \\ METIS_TAC [CONJ_SYM]);

val STAR_OVER_DISJ = store_thm("STAR_OVER_DISJ",
  ``!P Q Q'. ((P * Q) \/ (P * Q') = P * (Q \/ Q')) /\ 
             ((Q * P) \/ (Q' * P) = (Q \/ Q') * P)``,
  SRW_TAC [] [STAR_def,EXTENSION,IN_DEF,SEP_DISJ_def] \\ METIS_TAC []);

val STAR_OVER_CONJ = store_thm("STAR_OVER_CONJ",
  ``!P Q Q' s. SEP_IMP (P * (Q /\ Q')) ((P * Q) /\ (P * Q')) /\ 
               SEP_IMP ((Q /\ Q') * P) ((Q * P) /\ (Q' * P))``,
  SRW_TAC [] [SEP_IMP_def,STAR_def,EXTENSION,IN_DEF,SEP_CONJ_def] \\ METIS_TAC []);

val SEP_DISJ_CLAUSES = store_thm("SEP_DISJ_CLAUSES",
  ``!P. (SEP_F \/ P = P) /\ (P \/ SEP_F = P) /\ 
        (SEP_T \/ P = SEP_T) /\ (P \/ SEP_T = SEP_T) /\ 
        (P \/ P = P)``,
  SRW_TAC [] [FUN_EQ_THM,SEP_DISJ_def,SEP_T_def,SEP_F_def]);

val SEP_CONJ_CLAUSES = store_thm("SEP_CONJ_CLAUSES",
  ``!P. (SEP_F /\ P = SEP_F) /\ (P /\ SEP_F = SEP_F) /\ 
        (SEP_T /\ P = P) /\ (P /\ SEP_T = P) /\ 
        (P /\ P = P)``,
  SRW_TAC [] [FUN_EQ_THM,SEP_CONJ_def,SEP_T_def,SEP_F_def]);
  
val SEP_cond_CLAUSES = store_thm("SEP_cond_CLAUSES",
  ``!c c'. (cond c \/ cond c' = cond (c \/ c')) /\ 
           (cond c /\ cond c' = cond (c /\ c')) /\
           (cond c * cond c' = cond (c /\ c')) /\
           (cond T = emp) /\ (cond F = SEP_F)``,
  SRW_TAC [] [EXTENSION,IN_DEF]
  \\ SRW_TAC [] [cond_def,STAR_def,SEP_DISJ_def,SEP_CONJ_def,
         IN_DEF,SPLIT_def,DISJOINT_DEF,EMPTY_DEF,emp_def,SEP_F_def]
  \\ SIMP_TAC bool_ss [] \\ METIS_TAC [NOT_IN_EMPTY]);

val T_STAR_T = store_thm("T_STAR_T",
  ``SEP_T * SEP_T = SEP_T``,
  SIMP_TAC std_ss [SEP_T_def,STAR_def,FUN_EQ_THM] 
  \\ STRIP_TAC \\ Q.EXISTS_TAC `{}` \\ Q.EXISTS_TAC `x DIFF {}`
  \\ MATCH_MP_TAC SPLIT_SUBSET_DIFF \\ REWRITE_TAC [EMPTY_SUBSET]);

val MOVE_IN_LEMMA = prove(
  ``((\s. ?v. P v s) * Q) = (\s. ?v. (P v * Q) s)``,
  SRW_TAC [] [FUN_EQ_THM,STAR_def]  
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `v'` \\ Q.EXISTS_TAC `s'` \\ Q.EXISTS_TAC `v` \\ ASM_REWRITE_TAC [],
    Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `v'` \\ ASM_REWRITE_TAC []
    \\ Q.EXISTS_TAC `v` \\ ASM_REWRITE_TAC []]);

val SEP_FORALL_THM = store_thm("SEP_FORALL_THM",
  ``!P:'b->'a set->bool s. (SEP_FORALL v. P v) s = !v. P v s``,
  SRW_TAC [] [SEP_FORALL]);

val SEP_FORALL_IGNORE = store_thm("SEP_FORALL_IGNORE",
  ``!P. (SEP_FORALL v. P) = P``,
  SRW_TAC [] [SEP_FORALL,FUN_EQ_THM]);

val SEP_EXISTS_THM = store_thm("SEP_EXISTS_THM",
  ``!P s. (SEP_EXISTS v. P v) s = ?v. P v s``,
  REWRITE_TAC [SEP_EXISTS] \\ BETA_TAC 
  \\ SIMP_TAC std_ss [MOVE_IN_LEMMA]);

val SEP_EXISTS_SYM = store_thm("SEP_EXISTS_SYM",
  ``!P. (SEP_EXISTS v v'. P v v') = (SEP_EXISTS v' v. P v v')``,	
  SRW_TAC [] [FUN_EQ_THM,SEP_EXISTS_THM] \\ METIS_TAC []);

val SEP_EXISTS_ABSORB_STAR = store_thm("SEP_EXISTS_ABSORB_STAR",
  ``!P Q. ((SEP_EXISTS v. P v) * Q) = (SEP_EXISTS v. P v * Q)``, 
  SRW_TAC [] [SEP_EXISTS,FUN_EQ_THM,MOVE_IN_LEMMA]);

val SEP_EXISTS_ABSORB_DISJ = store_thm("SEP_EXISTS_ABSORB_DISJ",
  ``!P Q. ((SEP_EXISTS v. P v) \/ Q) = (SEP_EXISTS v. P v \/ Q)``, 
  SRW_TAC [] [SEP_EXISTS,FUN_EQ_THM,SEP_DISJ_def] \\ METIS_TAC []);

val SEP_EXISTS_ABSORB_CONJ = store_thm("SEP_EXISTS_ABSORB_CONJ",
  ``!P Q. ((SEP_EXISTS v. P v) /\ Q) = (SEP_EXISTS v. P v /\ Q)``, 
  SRW_TAC [] [SEP_EXISTS,FUN_EQ_THM,SEP_CONJ_def] \\ METIS_TAC []);

val SEP_EXISTS_IGNORE = store_thm("SEP_EXISTS_IGNORE",
  ``!P Q. (SEP_EXISTS v. P) = P``,
  SRW_TAC [] [SEP_EXISTS,FUN_EQ_THM]);

val SEP_EXISTS_ONE = store_thm("SEP_EXISTS_ONE",
  ``!x. (SEP_EXISTS v. P v * cond (v = x)) = P x``,
  SRW_TAC [] [FUN_EQ_THM,SEP_EXISTS_THM,cond_STAR]);

val SEP_HIDE_THM = store_thm("SEP_HIDE_THM",
  ``!P. ~P = SEP_EXISTS x. P x``,
  SIMP_TAC std_ss [FUN_EQ_THM,SEP_HIDE_def,SEP_EXISTS_THM]);

val SEP_BIGDISJ_UNION = prove(
  ``!Z Z'. SEP_BIGDISJ (Z UNION Z') = SEP_BIGDISJ Z \/ SEP_BIGDISJ Z'``,
  SRW_TAC [] [FUN_EQ_THM,SEP_BIGDISJ_def,SEP_DISJ_def]
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    DISJ1_TAC \\ Q.EXISTS_TAC `P` \\ ASM_REWRITE_TAC [],
    DISJ2_TAC \\ Q.EXISTS_TAC `P` \\ ASM_REWRITE_TAC [],
    Q.EXISTS_TAC `P` \\ ASM_REWRITE_TAC [],    
    Q.EXISTS_TAC `P` \\ ASM_REWRITE_TAC []]);

val SEP_BIGDISJ_CLAUSES = store_thm("SEP_BIGDISJ_CLAUSES",
  ``!P Z Z'. (SEP_BIGDISJ {} = SEP_F) /\ 
             (SEP_BIGDISJ (P INSERT Z) = P \/ SEP_BIGDISJ Z) /\ 
             (SEP_BIGDISJ (Z UNION Z') = SEP_BIGDISJ Z \/ SEP_BIGDISJ Z')``,
  REWRITE_TAC [SEP_BIGDISJ_UNION]
  \\ SRW_TAC [] [FUN_EQ_THM,SEP_BIGDISJ_def,SEP_F_def,SEP_DISJ_def]
  \\ METIS_TAC []);

val STAR_OVER_BIGDISJ = store_thm("STAR_OVER_BIGDISJ",
  ``!Z R. (SEP_BIGDISJ Z * R = SEP_BIGDISJ { P * R | P IN Z }) /\ 
          (R * SEP_BIGDISJ Z = SEP_BIGDISJ { R * P | P IN Z })``,
  `!Z R. SEP_BIGDISJ Z * R = SEP_BIGDISJ { P * R | P IN Z }` by ALL_TAC << [  
    SRW_TAC [] [FUN_EQ_THM] \\ EQ_TAC
    << [
      SRW_TAC [] [FUN_EQ_THM]
      \\ POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE bool_ss [STAR_def,SEP_BIGDISJ_def])  
      \\ SRW_TAC [] [SEP_BIGDISJ_def]
      \\ Q.EXISTS_TAC `P * R` 
      \\ SRW_TAC [] [STAR_def,FUN_EQ_THM] << [
        Q.EXISTS_TAC `P` \\ ASM_REWRITE_TAC [],
        METIS_TAC []],
      SRW_TAC [] [FUN_EQ_THM]
      \\ POP_ASSUM 
      (STRIP_ASSUME_TAC o SIMP_RULE bool_ss [STAR_def,SEP_BIGDISJ_def,GSPECIFICATION,PAIR_EQ])  
      \\ `?u v. SPLIT x (u,v) /\ P' u /\ R v` by METIS_TAC [ABS_SIMP]
      \\ SRW_TAC [] [SEP_BIGDISJ_def,STAR_def]
      \\ METIS_TAC []],
    ASM_REWRITE_TAC [] \\ ONCE_REWRITE_TAC [STAR_SYM] \\ ASM_REWRITE_TAC []]);

val SEP_BIGCONJ_UNION = prove(
  ``!Z Z'. SEP_BIGCONJ (Z UNION Z') = SEP_BIGCONJ Z /\ SEP_BIGCONJ Z'``,
  SRW_TAC [] [FUN_EQ_THM,SEP_BIGCONJ_def,SEP_CONJ_def] \\ METIS_TAC []);

val SEP_BIGCONJ_CLAUSES = store_thm("SEP_BIGCONJ_CLAUSES",
  ``!P Z Z'. (SEP_BIGCONJ {} = SEP_T) /\ 
             (SEP_BIGCONJ (P INSERT Z) = P /\ SEP_BIGCONJ Z) /\
             (SEP_BIGCONJ (Z UNION Z') = SEP_BIGCONJ Z /\ SEP_BIGCONJ Z')``,
  REWRITE_TAC [SEP_BIGCONJ_UNION]
  \\ SRW_TAC [] [FUN_EQ_THM,SEP_BIGCONJ_def,SEP_T_def,SEP_CONJ_def]
  \\ METIS_TAC []);
  
val STAR_OVER_BIGCONJ_RIGHT = store_thm("STAR_OVER_BIGCONJ_RIGHT",
  ``!Z R s. (SEP_BIGCONJ Z * R) s ==> (SEP_BIGCONJ { P * R | P IN Z }) s``,
  SRW_TAC [] [FUN_EQ_THM]
  \\ POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE bool_ss [STAR_def,SEP_BIGCONJ_def])  
  \\ SIMP_TAC bool_ss [SEP_BIGCONJ_def,GSPECIFICATION,PAIR_EQ]
  \\ REPEAT STRIP_TAC
  \\ METIS_TAC [STAR_def]);

val STAR_OVER_BIGCONJ_LEFT = store_thm("STAR_OVER_BIGCONJ_LEFT",
  ``!Z R s. (R * SEP_BIGCONJ Z) s ==> (SEP_BIGCONJ { R * P | P IN Z }) s``,
  ONCE_REWRITE_TAC [STAR_SYM]
  \\ REWRITE_TAC [STAR_OVER_BIGCONJ_RIGHT]);

val SEP_HIDE_INTRO = store_thm("SEP_HIDE_INTRO",
  ``!P Q x s. SEP_IMP (P * Q x) (P * ~ Q)``,
  SRW_TAC [] [STAR_def,SEP_HIDE_def,SEP_IMP_def] \\ METIS_TAC []); 


(* ----------------------------------------------------------------------------- *)
(* Theorems about SEP_ADD and STAR2                                              *)
(* ----------------------------------------------------------------------------- *)

val STAR_T_THM = prove(
  ``(P * SEP_T) s = ?u. u SUBSET s /\ P u``,
  SIMP_TAC std_ss [STAR_def,SEP_T_def] \\ EQ_TAC \\ REPEAT STRIP_TAC << [ 
    Q.EXISTS_TAC `u` \\ IMP_RES_TAC SPLIT_SUBSET \\ ASM_REWRITE_TAC [],    
    Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `s DIFF u` 
    \\ ASM_SIMP_TAC bool_ss [SPLIT_SUBSET_DIFF]]);

val SEP_ADD_THM = store_thm("SEP_ADD_thm",
  ``!P Q. SEP_ADD P Q = \s. ?u v. P u /\ Q v /\ u SUBSET s /\ v SUBSET s``,
  SIMP_TAC std_ss [SEP_ADD_def,FUN_EQ_THM,SEP_CONJ_def,STAR_T_THM] \\ METIS_TAC []);
  
val SEP_ADD_STAR_T = store_thm("SEP_ADD_STAR_T",
  ``!P Q. (SEP_ADD P (Q * SEP_T) = SEP_ADD P Q) /\ ((SEP_ADD P Q) * SEP_T = SEP_ADD P Q)``,
  REPEAT STRIP_TAC THEN1 REWRITE_TAC [SEP_ADD_def,GSYM STAR_ASSOC,T_STAR_T]
  \\ SIMP_TAC std_ss [FUN_EQ_THM,STAR_def,SEP_ADD_THM] 
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [ 
    IMP_RES_TAC SPLIT_SUBSET \\ IMP_RES_TAC SUBSET_TRANS
    \\ Q.EXISTS_TAC `u'` \\ Q.EXISTS_TAC `v'` \\ ASM_REWRITE_TAC [],
    Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `{}`
    \\ REWRITE_TAC [SPLIT_EMPTY,SEP_T_def]
    \\ Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `v` \\ ASM_REWRITE_TAC []]);

val SEP_ADD_IDEMPOT = store_thm("SEP_ADD_IDEMPOT",
  ``!P. SEP_ADD P P = P * SEP_T``,
  SIMP_TAC std_ss [FUN_EQ_THM,SEP_ADD_def,SEP_CONJ_def]);
    
val SEP_ADD_COMM = store_thm("SEP_ADD_COMM",
  ``!P:'a set->bool Q. SEP_ADD P Q = SEP_ADD Q P``,
  REWRITE_TAC [SEP_ADD_def,SEP_CONJ_def,Once CONJ_COMM]);

val SEP_ADD_ASSOC = store_thm("SEP_ADD_ASSOC",
  ``!P:'a set->bool Q R. SEP_ADD P (SEP_ADD Q R) = SEP_ADD (SEP_ADD P Q) R``,
  REWRITE_TAC [FUN_EQ_THM]
  \\ ONCE_REWRITE_TAC [SEP_ADD_def]
  \\ REWRITE_TAC [SEP_ADD_STAR_T]
  \\ SIMP_TAC std_ss [SEP_ADD_def,SEP_CONJ_def,CONJ_ASSOC]);

val STAR2_COMM = store_thm("STAR2_COMM",
  ``!P:(('a -> bool) -> bool) # (('b -> bool) -> bool) Q. 
      P ** Q = Q ** P``,
  Cases \\ Cases \\ REWRITE_TAC [STAR2_def,Once STAR_SYM,Once SEP_ADD_COMM]);
  
val STAR2_ASSOC = store_thm("STAR2_ASSOC",
  ``!P:(('a -> bool) -> bool) # (('b -> bool) -> bool) Q R. 
      P ** (Q ** R) = (P ** Q) ** R``,
  NTAC 3 Cases \\ REWRITE_TAC [STAR2_def,STAR_ASSOC,SEP_ADD_ASSOC]);

val STAR_IMP_ADD = store_thm("STAR_IMP_ADD",
  ``!F P Q. SEP_IMP (P * Q * F) (SEP_ADD P Q)``,
  SIMP_TAC std_ss [SEP_IMP_def,STAR_def,SEP_ADD_THM] \\ REPEAT STRIP_TAC 
  \\ IMP_RES_TAC SPLIT_SUBSET \\ IMP_RES_TAC SUBSET_TRANS
  \\ Q.EXISTS_TAC `u'` \\ Q.EXISTS_TAC `v'` \\ ASM_REWRITE_TAC []);  

val emp_ADD = store_thm("emp_ADD",
  ``!P. (SEP_ADD emp P = P * SEP_T) /\ (SEP_ADD P emp = P * SEP_T)``,
  SIMP_TAC std_ss [STAR_T_THM,FUN_EQ_THM,SEP_ADD_def,SEP_CONJ_def]
  \\ SIMP_TAC std_ss [emp_def,EMPTY_SUBSET]);

val immute_DUP = store_thm("immute_DUP",
  ``!P x. immute x ** P = immute x ** immute x ** P``,
  Cases \\ REWRITE_TAC [immute_def,STAR2_def,emp_STAR,SEP_ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [SEP_ADD_COMM]
  \\ REWRITE_TAC [SEP_ADD_IDEMPOT,SEP_ADD_STAR_T]);

val mute_IMP_immute = store_thm("mute_IMP_immute",
  ``!P x. SEP_IMP (SEP_JOIN (mute x ** P)) (SEP_JOIN (immute x ** P))``,
  Cases \\ REWRITE_TAC [mute_def,immute_def,STAR2_def,emp_STAR,SEP_JOIN_def]
  \\ REWRITE_TAC [emp_ADD,GSYM STAR_ASSOC,T_STAR_T] \\ REWRITE_TAC [STAR_ASSOC]
  \\ REWRITE_TAC [METIS_PROVE [STAR_SYM,STAR_ASSOC] ``x*q*r*t = (x*r)*(q*t):'a set -> bool``] 
  \\ REWRITE_TAC [METIS_PROVE [STAR_SYM,STAR_ASSOC] ``q*(SEP_ADD x r)*t = (SEP_ADD x r)*(q*t):'a set -> bool``] 
  \\ STRIP_TAC \\ MATCH_MP_TAC SEP_IMP_FRAME
  \\ REWRITE_TAC [REWRITE_RULE [emp_STAR] (Q.SPEC `emp` STAR_IMP_ADD)]);


(* ----------------------------------------------------------------------------- *)
(* Theorems about BIGSTAR                                                        *)
(* ----------------------------------------------------------------------------- *)

val SPLIT_BIGSPLIT_LEMMA = prove(
  ``!z z' Q Q'. 
      z IN Q /\ z' IN Q' /\ DISJOINT (BIGUNION Q) (BIGUNION Q') ==> DISJOINT z z'``,
  SRW_TAC [] [DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_BIGUNION,IN_INTER]);

val SPLIT_BIGSPLIT = prove(
  ``!x u v Q Q'. SPLIT x (u,v) /\ BIGSPLIT u Q /\ BIGSPLIT v Q' ==> 
                 BIGSPLIT x (Q UNION Q')``,
  SRW_TAC [] [BIGSPLIT_def,SPLIT_def]
  \\ FULL_SIMP_TAC bool_ss [ALL_DISJOINT_def,IN_UNION]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `z = z'` 
  \\ ASM_REWRITE_TAC []
  \\ METIS_TAC [SPLIT_BIGSPLIT_LEMMA,DISJOINT_SYM]);

val SPLIT_BIGSPLIT_XOR = prove(
  ``!x u v Q Q'. SPLIT x (u,v) /\ BIGSPLIT u Q /\ BIGSPLIT v Q' ==> 
                 ~(q = {}) /\ q IN Q ==> ~(q IN Q')``,
  REPEAT STRIP_TAC  
  \\ `q SUBSET v /\ q SUBSET u` by METIS_TAC [BIGSPLIT_SUBSET]
  \\ FULL_SIMP_TAC bool_ss [EXTENSION,NOT_IN_EMPTY]
  \\ `x' IN u /\ x' IN v` by METIS_TAC [SUBSET_DEF]  
  \\ METIS_TAC [SPLIT_def,DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]);

val BIGSTAR_ONE_LEMMA = prove(
  ``!Q z. (!q. q IN Q ==> (z = q)) ==> ((Q = {z}) \/ (Q = {}))``,
  REWRITE_TAC [EXTENSION,IN_INSERT,NOT_IN_EMPTY]
  \\ METIS_TAC []);

val BIGSTAR_ONE = store_thm("BIGSTAR_ONE",
  ``!P. BIGSTAR {P} = P``,
  SIMP_TAC bool_ss [BIGSTAR_def,Once FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss
       [RES_FORALL,RES_EXISTS,RES_EXISTS_UNIQUE,IN_INSERT,NOT_IN_EMPTY,
        BIGSPLIT_def,bijection'_def] << [
    `!x y. (BIGUNION {y} = x) ==> (x = y)` by SRW_TAC [] [BIGUNION]
    \\ `(Q = {}) \/ (Q = {f P})` by METIS_TAC [BIGSTAR_ONE_LEMMA]
    \\ METIS_TAC [NOT_IN_EMPTY],
    Q.EXISTS_TAC `{x}` \\ Q.EXISTS_TAC `\z. x`
    \\ ASM_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY,ALL_DISJOINT_def,BIGUNION]
    \\ SIMP_TAC bool_ss [EXTENSION,GSPECIFICATION,PAIR_EQ]]);

val BIGSTAR_UNION_LEMMA = prove(
  ``!x Q Q'. (!q q'. q IN Q /\ q' IN Q' ==> DISJOINT q q') /\ 
             (BIGUNION (Q UNION Q') = x) ==> 
             SPLIT x (BIGUNION Q,BIGUNION Q')``,
  SRW_TAC [] [SPLIT_def]);

val BIGSTAR_UNION = store_thm("BIGSTAR_UNION",
  ``!Z Z'. DISJOINT Z Z' ==> (BIGSTAR (Z UNION Z') = BIGSTAR Z * BIGSTAR Z')``,
  REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o REWRITE_RULE [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY])
  \\ REWRITE_TAC [FUN_EQ_THM]
  \\ REPEAT STRIP_TAC
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    FULL_SIMP_TAC bool_ss 
         [BIGSTAR_def,STAR_def,RES_EXISTS,RES_FORALL,IN_INSERT,IN_UNION,bijection'_def]
    \\ Q.EXISTS_TAC `BIGUNION { f z |z| z IN Z }`        
    \\ Q.EXISTS_TAC `BIGUNION { f z |z| z IN Z' }`        
    \\ REPEAT STRIP_TAC << [
      MATCH_MP_TAC BIGSTAR_UNION_LEMMA
      \\ SIMP_TAC bool_ss [GSPECIFICATION,PAIR_EQ,BIGSPLIT_def,ALL_DISJOINT_def]
      \\ FULL_SIMP_TAC bool_ss [BIGSPLIT_def,ALL_DISJOINT_def]
      \\ REPEAT STRIP_TAC
      THEN1 METIS_TAC [DISJOINT_EMPTY]
      \\ FULL_SIMP_TAC bool_ss [BIGUNION]        
      \\ FULL_SIMP_TAC bool_ss [EXTENSION,IN_UNION,GSPECIFICATION,PAIR_EQ]
      \\ REPEAT STRIP_TAC      
      \\ EQ_TAC \\ REPEAT STRIP_TAC
      THEN1 METIS_TAC []
      THEN1 METIS_TAC []
      \\ FULL_SIMP_TAC bool_ss [GSYM EXTENSION]
      \\ `?q. q IN Q /\ x' IN q` by METIS_TAC []
      \\ Q.EXISTS_TAC `q` \\ ASM_REWRITE_TAC []
      \\ `~(q = {})` by METIS_TAC [EXTENSION,NOT_IN_EMPTY]
      \\ METIS_TAC [],
      Q.EXISTS_TAC `{f z |z| z IN Z}`
      \\ Q.EXISTS_TAC `f`
      \\ REPEAT STRIP_TAC << [
        MATCH_MP_TAC BIGSPLIT_BIGUNION
        \\ FULL_SIMP_TAC bool_ss [BIGSPLIT_def,ALL_DISJOINT_def,GSPECIFICATION]
        \\ REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [],
        FULL_SIMP_TAC bool_ss [GSPECIFICATION,PAIR_EQ]
        \\ Q.EXISTS_TAC `z` \\ ASM_REWRITE_TAC [] \\ METIS_TAC [],
        FULL_SIMP_TAC bool_ss [GSPECIFICATION,PAIR_EQ]
        \\ Q.EXISTS_TAC `z` \\ ASM_REWRITE_TAC [] \\ METIS_TAC [],
        METIS_TAC [],
        METIS_TAC []],
      Q.EXISTS_TAC `{f z |z| z IN Z'}`
      \\ Q.EXISTS_TAC `f`
      \\ REPEAT STRIP_TAC << [
        MATCH_MP_TAC BIGSPLIT_BIGUNION
        \\ FULL_SIMP_TAC bool_ss [BIGSPLIT_def,ALL_DISJOINT_def,GSPECIFICATION]
        \\ REWRITE_TAC [PAIR_EQ]
        \\ REPEAT STRIP_TAC
        \\ METIS_TAC [],
        FULL_SIMP_TAC bool_ss [GSPECIFICATION,PAIR_EQ]
        \\ Q.EXISTS_TAC `z` \\ ASM_REWRITE_TAC [] \\ METIS_TAC [],
        FULL_SIMP_TAC bool_ss [GSPECIFICATION,PAIR_EQ]
        \\ Q.EXISTS_TAC `z` \\ ASM_REWRITE_TAC [] \\ METIS_TAC [],
        METIS_TAC [],
        METIS_TAC []]],
    FULL_SIMP_TAC bool_ss [BIGSTAR_def,STAR_def,RES_EXISTS,RES_FORALL,bijection'_def]
    \\ FULL_SIMP_TAC bool_ss [DISJOINT_DEF,IN_UNION,IN_INSERT]
    \\ Q.EXISTS_TAC `Q UNION Q'`
    \\ Q.EXISTS_TAC `\z. if z IN Z then f z else f' z`
    \\ FULL_SIMP_TAC bool_ss [IN_UNION] 
    \\ METIS_TAC [SPLIT_BIGSPLIT_XOR,SPLIT_BIGSPLIT]]);

val BIGSTAR_DIFF_EXTEND_LEMMA = prove(
  ``!x z. x SUBSET z ==> (x UNION (z DIFF x) = z)``,
  SRW_TAC [] [EXTENSION,IN_UNION,IN_DIFF,SUBSET_DEF] \\ METIS_TAC []);

val BIGSTAR_DIFF_EXTEND = prove(
  ``!Z X. X SUBSET Z ==> (BIGSTAR X * BIGSTAR (Z DIFF X) = BIGSTAR Z)``,
  REPEAT STRIP_TAC
  \\ `DISJOINT X (Z DIFF X)` by METIS_TAC [DISJOINT_DIFF]
  \\ ASM_SIMP_TAC bool_ss [GSYM BIGSTAR_UNION,BIGSTAR_DIFF_EXTEND_LEMMA]);
  
val BIGSTAR_EXTEND = store_thm("BIGSTAR_EXTEND",
  ``!Z Y. Y SUBSET Z ==> ?X. BIGSTAR Z = BIGSTAR Y * X``,
  METIS_TAC [BIGSTAR_DIFF_EXTEND]);
  
val BIGSTAR_EMPTY = store_thm("BIGSTAR_EMPTY",
  ``BIGSTAR {} = emp``,
  REWRITE_TAC [FUN_EQ_THM] \\ STRIP_TAC
  \\ SIMP_TAC bool_ss [BIGSTAR_def,RES_FORALL,RES_EXISTS,NOT_IN_EMPTY,emp_def,bijection'_def]    
  \\ SIMP_TAC bool_ss [BIGSPLIT_def,BIGUNION,ALL_DISJOINT_def]
  \\ EQ_TAC \\ STRIP_TAC << [
    FULL_SIMP_TAC bool_ss [EXTENSION,GSPECIFICATION,PAIR_EQ,NOT_IN_EMPTY],
    Q.EXISTS_TAC `{}`
    \\ FULL_SIMP_TAC bool_ss [EXTENSION,GSPECIFICATION,PAIR_EQ,NOT_IN_EMPTY]]);

val BIGSTAR_INSERT_LEMMA1 = prove(
  ``!P Z. P INSERT Z = {P} UNION Z``,
  SRW_TAC [] [EXTENSION,IN_INSERT,NOT_IN_EMPTY,IN_UNION]);

val BIGSTAR_INSERT_LEMMA2 = prove(
  ``!P Z. ~(P IN Z) ==> DISJOINT {P} Z``,
  SRW_TAC [] [DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY,IN_INSERT,EXTENSION]);

val BIGSTAR_INSERT = store_thm("BIGSTAR_INSERT",
  ``!P Z. ~(P IN Z) ==> (BIGSTAR (P INSERT Z) = P * BIGSTAR Z)``,
  REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [BIGSTAR_INSERT_LEMMA1]
  \\ `DISJOINT {P} Z` by METIS_TAC [BIGSTAR_INSERT_LEMMA2]
  \\ ASM_SIMP_TAC bool_ss [BIGSTAR_UNION]
  \\ REWRITE_TAC [BIGSTAR_ONE]);


val _ = export_theory();

