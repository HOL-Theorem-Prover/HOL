
open HolKernel boolLib bossLib Parse;
open pred_setTheory arithmeticTheory set_sepTheory tailrecTheory;

val _ = new_theory "prog";

infix \\ 
val op \\ = op THEN;


(* ---- definitions ----- *)

val _ = type_abbrev("processor",``: ('a->'b set) # ('a->'a->bool) # ('c->'b set) ``);

val rel_sequence_def = Define `
  rel_sequence R seq state =
    (seq 0 = state) /\ 
    !n. if (?x. R (seq n) x) then R (seq n) (seq (SUC n)) else (seq (SUC n) = seq n)`;

val RUN_def = Define `
  RUN ((to_set,next,instr):('a,'b,'c)processor) p q = 
    !state r. (p * r) (to_set state) ==> 
              !seq. rel_sequence next seq state ==> ?i. (q * r) (to_set (seq i))`;

val CODE_POOL_def = Define `
  CODE_POOL instr c = \s. s = BIGUNION (IMAGE instr c)`;

val SPEC_def = Define `
  SPEC ((to_set,next,instr):('a,'b,'c)processor) p c q =
    RUN (to_set,next,instr) (CODE_POOL instr c * p) (CODE_POOL instr c * q)`;


(* ---- theorems ---- *)

val INIT_TAC = Cases \\ Cases_on `r` ;
val RW = REWRITE_RULE;

val RUN_EQ_SPEC = store_thm("RUN_EQ_SPEC",
  ``!x. RUN x p q = SPEC x p {} q``,
  INIT_TAC \\ `CODE_POOL r' {} = emp` by ALL_TAC \\ ASM_REWRITE_TAC [SEP_CLAUSES,SPEC_def] 
  \\ REWRITE_TAC [FUN_EQ_THM,CODE_POOL_def,IMAGE_EMPTY,BIGUNION_EMPTY,emp_def]);

val SPEC_FRAME = store_thm("SPEC_FRAME",
  ``!x p c q. SPEC x p c q ==> !r. SPEC x (p * r) c (q * r)``,
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_def,GSYM STAR_ASSOC,SPEC_def]
  \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val SPEC_FALSE_PRE = store_thm("SPEC_FALSE_PRE",
  ``!x c q. SPEC x SEP_F c q``,
  INIT_TAC \\ REWRITE_TAC [RUN_def,SPEC_def,SEP_CLAUSES] \\ SIMP_TAC std_ss [SEP_F_def]);

val SPEC_STRENGTHEN = store_thm("SPEC_STRENGTHEN",
  ``!x p c q. SPEC x p c q ==> !r. SEP_IMP r p ==> SPEC x r c q``,
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_def,SPEC_def,GSYM STAR_ASSOC]
  \\ METIS_TAC [SEP_IMP_def,SEP_IMP_REFL,SEP_IMP_STAR]);

val SPEC_WEAKEN = store_thm("SPEC_WEAKEN",
  ``!x p c q. SPEC x p c q ==> !r. SEP_IMP q r ==> SPEC x p c r``,
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_def,SPEC_def,GSYM STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ METIS_TAC [SEP_IMP_def,SEP_IMP_REFL,SEP_IMP_STAR]);

val CODE_POOL_LEMMA = prove(
  ``!c c' i. ?r. CODE_POOL i (c UNION c') = CODE_POOL i c * r``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [CODE_POOL_def,IMAGE_UNION,BIGUNION_UNION,STAR_def]
  \\ Q.EXISTS_TAC `\s. s = BIGUNION (IMAGE i c') DIFF BIGUNION (IMAGE i c)`
  \\ ONCE_REWRITE_TAC [FUN_EQ_THM] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,EXTENSION,IN_BIGUNION,IN_DIFF,
       IN_UNION,DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY] \\ METIS_TAC []); 

val SPEC_CODE = store_thm("SPEC_CODE",
  ``!x p c q. SPEC x (CODE_POOL (SND (SND x)) c * p) {} (CODE_POOL (SND (SND x)) c * q) = 
              SPEC x p c q``,
  INIT_TAC \\ REWRITE_TAC [pairTheory.SND]
  \\ REWRITE_TAC [SPEC_def,CODE_POOL_def,IMAGE_EMPTY,BIGUNION_EMPTY,GSYM emp_def,SEP_CLAUSES]);
  
val SPEC_ADD_CODE = store_thm("SPEC_ADD_CODE",
  ``!x p c q. SPEC x p c q ==> !c'. SPEC x p (c UNION c') q``,
  INIT_TAC \\ REWRITE_TAC [ONCE_REWRITE_RULE [STAR_COMM] SPEC_def,RUN_def]
  \\ REWRITE_TAC [GSYM STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ `?t. CODE_POOL r' (c UNION c') = CODE_POOL r' c * t` by 
        METIS_TAC [CODE_POOL_LEMMA] \\ FULL_SIMP_TAC bool_ss [GSYM STAR_ASSOC]
  \\ METIS_TAC []);

val SPEC_SUBSET_CODE = store_thm("SPEC_SUBSET_CODE",
  ``!x p c q. SPEC x p c q ==> !c'. c SUBSET c' ==> SPEC x p c' q``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [SUBSET_DEF]
  \\ `c' = c UNION c'` by FULL_SIMP_TAC bool_ss [EXTENSION,IN_UNION]
  \\ METIS_TAC [SPEC_ADD_CODE]);

val rel_sequence_shift = prove(
  ``!n seq s. rel_sequence n seq s ==> !i. rel_sequence n (\j. seq (i + j)) (seq i)``,
  REWRITE_TAC [rel_sequence_def] \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss []
  \\ Cases_on `?s. n (seq (i + n')) s` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [ADD1,ADD_ASSOC] \\ METIS_TAC []);

val SPEC_COMPOSE_LEMMA = prove(
  ``!x c p1 p2 m q1 q2. 
      SPEC x p1 c (q1 \/ m) /\ SPEC x (m \/ p2) c q2 ==> SPEC x (p1 \/ p2) c (q1 \/ q2)``,
  INIT_TAC \\ FULL_SIMP_TAC std_ss [SPEC_def,RUN_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [SEP_CLAUSES]  
  \\ REVERSE (FULL_SIMP_TAC bool_ss [SEP_DISJ_def]) THEN1 METIS_TAC []
  \\ `?i. (CODE_POOL r' c * q1 * r) (q (seq i)) \/ 
          (CODE_POOL r' c * m * r) (q (seq i))` by METIS_TAC [] THEN1 METIS_TAC []
  \\ `rel_sequence q' (\j. seq (i + j)) (seq i)` by METIS_TAC [rel_sequence_shift]
  \\ Q.ABBREV_TAC `nn = \j. seq (i + j)`
  \\ `?j. (CODE_POOL r' c * q2 * r) (q (nn j))` by METIS_TAC []
  \\ Q.UNABBREV_TAC `nn` \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `i + j` \\ METIS_TAC []);

val SPEC_MERGE = store_thm("SPEC_MERGE",
  ``!x p1 p2 c1 m c2 q1 q2. 
      SPEC x p1 c1 (q1 \/ m) /\ SPEC x (m \/ p2) c2 q2 ==> 
      SPEC x (p1 \/ p2) (c1 UNION c2) (q1 \/ q2)``,
  METIS_TAC [SPEC_ADD_CODE,SPEC_COMPOSE_LEMMA,UNION_COMM]);

val SPEC_COMPOSE = store_thm("SPEC_COMPOSE",
  ``!x p c1 m c2 q. SPEC x p c1 m /\ SPEC x m c2 q ==> SPEC x p (c1 UNION c2) q``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC (REWRITE_RULE [SEP_CLAUSES] 
  (Q.SPECL [`x`,`p`,`SEP_F`,`c1`,`m`,`c2`,`SEP_F`,`q`] SPEC_MERGE))
  \\ ASM_SIMP_TAC bool_ss []);

val SPEC_COMPOSE_I = store_thm("SPEC_COMPOSE_I",    
  ``!x p c q1 q2 q3 q4.
      SPEC x (q1 * q3) c q2 ==> SPEC x p c (q1 * q4) ==>
      SEP_IMP q4 q3 ==> SPEC x p c q2``,
  REPEAT STRIP_TAC
  \\ `SEP_IMP (q1 * q4) (q1 * q3)` by METIS_TAC [SEP_IMP_REFL,SEP_IMP_STAR]
  \\ IMP_RES_TAC SPEC_WEAKEN \\ METIS_TAC [SPEC_COMPOSE,UNION_IDEMPOT]);

val SPEC_FRAME_COMPOSE = store_thm("SPEC_FRAME_COMPOSE",
  ``!x p p' c1 m c2 q q' b1 b2.
       (b1 ==> SPEC x (m * q') c2 q) ==> 
       (b2 ==> SPEC x p c1 (m * p')) ==> 
       (b1 /\ b2) ==> SPEC x (p * q') (c1 UNION c2) (q * p')``,  
  REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_COMPOSE
  \\ Q.EXISTS_TAC `m * p' * q'` \\ REPEAT STRIP_TAC \\ RES_TAC
  THEN1 (MATCH_MP_TAC SPEC_FRAME \\ ASM_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC SPEC_FRAME \\ METIS_TAC [STAR_ASSOC,STAR_COMM]);

val SPEC_HIDE_PRE = store_thm("SPEC_HIDE_PRE",
  ``!x p p' c q. (!y:'var. SPEC x (p * p' y) c q) = SPEC x (p * ~ p') c q``,
  INIT_TAC \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ REWRITE_TAC [ONCE_REWRITE_RULE [STAR_COMM] SPEC_def,RUN_def,GSYM STAR_ASSOC]
  \\ REWRITE_TAC [SEP_CLAUSES,SEP_HIDE_def]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC []);

val SPEC_PRE_EXISTS = store_thm("SPEC_PRE_EXISTS",
  ``!x p c q. (!y:'var. SPEC x (p y) c q) = SPEC x (SEP_EXISTS y. p y) c q``,
  INIT_TAC \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [SEP_CLAUSES,SEP_HIDE_def,SPEC_def,RUN_def,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC []);

val SEP_HIDE_INTRO = prove(
  ``!p q x s. SEP_IMP (p * q x) (p * ~ q)``,
  SIMP_TAC std_ss [STAR_def,SEP_HIDE_def,SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC []);

val SPEC_HIDE_POST = store_thm("SPEC_HIDE_POST",
  ``!x p c q q' y:'var. SPEC x p c (q * q' y) ==> SPEC x p c (q * ~ q')``,
  METIS_TAC [SPEC_WEAKEN,SEP_HIDE_INTRO]);

val SPEC_MOVE_COND = store_thm("SPEC_MOVE_COND",
  ``!x p c q g. SPEC x (p * cond g) c q = g ==> SPEC x p c q``,
  INIT_TAC \\ Cases_on `g` 
  \\ REWRITE_TAC [SPEC_def,RUN_def,SEP_CLAUSES] \\ REWRITE_TAC [SEP_F_def]);

val SPEC_DUPLICATE_COND = store_thm("SPEC_DUPLICATE_COND",
  ``!x p c q g. SPEC x (p * cond g) c q ==> SPEC x (p * cond g) c (q * cond g)``,
  SIMP_TAC std_ss [SPEC_MOVE_COND,SEP_CLAUSES]);

val SPEC_MERGE_COND = store_thm("SPEC_MERGE_COND",
  ``!x p c1 c2 q b1 b2.
       SPEC x (p * cond b1) c1 q ==> 
       SPEC x (p * cond b2) c2 q ==> 
       SPEC x (p * cond (b1 \/ b2)) (c1 UNION c2) q``,  
  Cases_on `b1` \\ Cases_on `b2` 
  \\ SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]
  \\ METIS_TAC [SPEC_ADD_CODE,SPEC_MERGE,SEP_CLAUSES,UNION_COMM]);    

val SPEC_REFL = store_thm("SPEC_REFL",
  ``!x:('a,'b,'c)processor p c. SPEC x p c p``,
  INIT_TAC \\ SIMP_TAC std_ss [RUN_def,SPEC_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC bool_ss [rel_sequence_def]);

val SPEC_TAILREC = store_thm("SPEC_TAILREC",
  ``!f1 (f2:'a->'b) g p res res' c m.
      (!x. TAILREC_PRE f1 g p x /\ p x /\ g x ==> 
           SPEC m (res x) c (res (f1 x))) /\
      (!x. TAILREC_PRE f1 g p x /\ p x /\ ~g x ==> 
           SPEC m (res x) c (res' (f2 x))) ==>
      (!x. TAILREC_PRE f1 g p x ==> 
           SPEC m (res x) c (res' (TAILREC f1 f2 g x)))``,
  NTAC 9 STRIP_TAC THEN HO_MATCH_MP_TAC TAILREC_PRE_INDUCT
  THEN METIS_TAC [TAILREC_THM,UNION_IDEMPOT,SPEC_COMPOSE]);


val _ = export_theory();
