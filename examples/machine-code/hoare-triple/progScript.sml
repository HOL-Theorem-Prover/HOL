
Theory prog
Ancestors
  pred_set arithmetic set_sep tailrec

val _ = ParseExtras.temp_loose_equality()


(* ---- definitions ----- *)

val _ = type_abbrev("processor",
  ``: ('a->'b set) # ('a->'a->bool) # ('c->'b set) # ('a->'a->bool) # ('a->bool)``);

Definition rel_sequence_def:
  rel_sequence R seq state =
    (seq 0 = state) /\
    !n. if (?x. R (seq n) x) then R (seq n) (seq (SUC n)) else (seq (SUC n) = seq n)
End

Definition SEP_REFINE_def:
  SEP_REFINE p less to_set state = ?s. less s state /\ p (to_set s)
End

Definition RUN_def:
  RUN ((to_set,next,instr,less,allow):('a,'b,'c)processor) p q =
    !state r. SEP_REFINE (p * r) less to_set state \/ allow state ==>
              !seq. rel_sequence next seq state ==>
                    ?i. SEP_REFINE (q * r) less to_set (seq i) \/ allow (seq i)
End

Definition CODE_POOL_def:
  CODE_POOL instr c = \s. s = BIGUNION (IMAGE instr c)
End

Definition SPEC_def:
  SPEC ((to_set,next,instr,less,allow):('a,'b,'c)processor) p c q =
    RUN (to_set,next,instr,less,allow) (CODE_POOL instr c * p)
                                       (CODE_POOL instr c * q)
End


(* ---- theorems ---- *)

val INIT_LEMMA = prove(
  ``(!to_set next instr less allow. P (to_set,next,instr,less,allow)) ==>
    (!x:('a,'b,'c)processor. P x)``,
  SIMP_TAC std_ss [pairTheory.FORALL_PROD]);

val INIT_TAC = HO_MATCH_MP_TAC INIT_LEMMA THEN NTAC 5 STRIP_TAC;
val RW = REWRITE_RULE;

Theorem RUN_thm:
    RUN ((to_set,next,instr,less,allow):('a,'b,'c)processor) p q =
    !state r. SEP_REFINE (p * r) less to_set state /\ ~allow state ==>
              !seq. rel_sequence next seq state ==>
                    ?i. SEP_REFINE (q * r) less to_set (seq i) \/ allow (seq i)
Proof
  SIMP_TAC std_ss [RUN_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1 (METIS_TAC [])
  \\ Cases_on `allow state`
  \\ TRY (Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC std_ss [rel_sequence_def] \\ NO_TAC)
  \\ METIS_TAC []
QED

Theorem RUN_EQ_SPEC:
    !x. RUN x p q = SPEC x p {} q
Proof
  INIT_TAC \\ sg `CODE_POOL instr {} = emp`
  \\ ASM_REWRITE_TAC [SEP_CLAUSES,SPEC_def]
  \\ REWRITE_TAC [FUN_EQ_THM,CODE_POOL_def,IMAGE_EMPTY,BIGUNION_EMPTY,emp_def]
QED

Theorem SPEC_FRAME:
    !x p c q. SPEC x p c q ==> !r. SPEC x (p * r) c (q * r)
Proof
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_def,GSYM STAR_ASSOC,SPEC_def]
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!state r. bbb` (ASSUME_TAC o Q.SPECL [`state`,`r * r'`])
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC] \\ METIS_TAC []
QED

Theorem SPEC_FALSE_PRE:
    !x c q. SPEC x SEP_F c q
Proof
  INIT_TAC \\ REWRITE_TAC [RUN_def,SPEC_def,SEP_CLAUSES,SEP_REFINE_def]
  \\ SIMP_TAC std_ss [SEP_F_def]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `0`
  \\ FULL_SIMP_TAC std_ss [rel_sequence_def]
QED

Theorem SPEC_STRENGTHEN:
    !x p c q. SPEC x p c q ==> !r. SEP_IMP r p ==> SPEC x r c q
Proof
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_thm,SPEC_def,GSYM STAR_ASSOC,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC
  \\ `(CODE_POOL instr c * (p * r')) (to_set s)` by
       METIS_TAC [SEP_IMP_def,SEP_IMP_REFL,SEP_IMP_STAR]
  \\ METIS_TAC []
QED

Theorem SPEC_WEAKEN:
    !x p c q. SPEC x p c q ==> !r. SEP_IMP q r ==> SPEC x p c r
Proof
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_thm,SPEC_def,GSYM STAR_ASSOC,PULL_FORALL]
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o Q.SPECL [`state`,`r'`,`seq`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ FULL_SIMP_TAC std_ss []
  \\ DISJ1_TAC \\ FULL_SIMP_TAC std_ss [SEP_REFINE_def]
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `s'` \\ ASM_SIMP_TAC std_ss []
  \\ METIS_TAC [SEP_IMP_def,SEP_IMP_REFL,SEP_IMP_STAR,SEP_REFINE_def]
QED

Theorem SPEC_STRENGTHEN_WEAKEN:
    !x p c q. SPEC x p c q ==> !r1 r2. SEP_IMP r1 p /\ SEP_IMP q r2 ==> SPEC x r1 c r2
Proof
  METIS_TAC [SPEC_STRENGTHEN,SPEC_WEAKEN]
QED

val CODE_POOL_LEMMA = prove(
  ``!c c' i. ?r. CODE_POOL i (c UNION c') = CODE_POOL i c * r``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [CODE_POOL_def,IMAGE_UNION,BIGUNION_UNION,STAR_def]
  \\ Q.EXISTS_TAC `\s. s = BIGUNION (IMAGE i c') DIFF BIGUNION (IMAGE i c)`
  \\ ONCE_REWRITE_TAC [FUN_EQ_THM] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,EXTENSION,IN_BIGUNION,IN_DIFF,
       IN_UNION,DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY] \\ METIS_TAC []);

Theorem SPEC_CODE:
    !x p c q. SPEC x (CODE_POOL (FST (SND (SND x))) c * p) {}
                     (CODE_POOL (FST (SND (SND x))) c * q) =
              SPEC x p c q
Proof
  INIT_TAC \\ REWRITE_TAC [pairTheory.SND] \\ REWRITE_TAC [SPEC_def,
    CODE_POOL_def,IMAGE_EMPTY,BIGUNION_EMPTY,GSYM emp_def,SEP_CLAUSES]
QED

Theorem SPEC_ADD_CODE:
    !x p c q. SPEC x p c q ==> !c'. SPEC x p (c UNION c') q
Proof
  INIT_TAC \\ REWRITE_TAC [ONCE_REWRITE_RULE [STAR_COMM] SPEC_def,RUN_def]
  \\ REWRITE_TAC [GSYM STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ `?t. CODE_POOL instr (c UNION c') = CODE_POOL instr c * t` by
        METIS_TAC [CODE_POOL_LEMMA] \\ FULL_SIMP_TAC bool_ss [GSYM STAR_ASSOC]
  \\ RES_TAC \\ FULL_SIMP_TAC bool_ss [GSYM STAR_ASSOC] \\ METIS_TAC []
QED

Theorem SPEC_COMBINE:
    !x i j p c1 c2 q b.
       (b /\ i ==> SPEC x p c1 q) ==> (~b /\ j ==> SPEC x p c2 q) ==>
       ((if b then i else j) ==> SPEC x p (c1 UNION c2) q)
Proof
  Cases_on `b` THEN REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN IMP_RES_TAC SPEC_ADD_CODE
  THEN ASM_REWRITE_TAC []
  THEN ONCE_REWRITE_TAC [UNION_COMM]
  THEN ASM_REWRITE_TAC []
QED

Theorem SPEC_SUBSET_CODE:
    !x p c q. SPEC x p c q ==> !c'. c SUBSET c' ==> SPEC x p c' q
Proof
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [SUBSET_DEF]
  \\ `c' = c UNION c'`
       by (FULL_SIMP_TAC bool_ss [EXTENSION,IN_UNION] \\ METIS_TAC[])
  \\ METIS_TAC [SPEC_ADD_CODE]
QED

Theorem SPEC_REFL:
    !x:('a,'b,'c)processor p c. SPEC x p c p
Proof
  INIT_TAC \\ SIMP_TAC std_ss [RUN_def,SPEC_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC bool_ss [rel_sequence_def]
QED

val rel_sequence_shift = prove(
  ``!n seq s. rel_sequence n seq s ==> !i. rel_sequence n (\j. seq (i + j)) (seq i)``,
  REWRITE_TAC [rel_sequence_def] \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss []
  \\ Cases_on `?s. n (seq (i + n')) s` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [ADD1,ADD_ASSOC] \\ METIS_TAC []);

val SEP_REFINE_DISJ = prove(
  ``SEP_REFINE (p \/ q) less to_set state =
    SEP_REFINE p less to_set state \/ SEP_REFINE q less to_set state``,
  SIMP_TAC std_ss [SEP_REFINE_def,SEP_DISJ_def] \\ METIS_TAC []);

val SPEC_COMPOSE_LEMMA = prove(
  ``!x c p1 p2 m q1 q2.
      SPEC x p1 c (q1 \/ m) /\ SPEC x (m \/ p2) c q2 ==>
      SPEC x (p1 \/ p2) c (q1 \/ q2)``,
  INIT_TAC \\ FULL_SIMP_TAC std_ss [SPEC_def,RUN_def]
  \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 (Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC std_ss [rel_sequence_def])
  \\ REVERSE (FULL_SIMP_TAC bool_ss [SEP_CLAUSES,SEP_REFINE_DISJ]) THEN1 METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ Q.PAT_X_ASSUM `!x.bbb` MP_TAC
  \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o Q.SPECL [`state`,`r`,`seq`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ TRY (Q.EXISTS_TAC `i` \\ FULL_SIMP_TAC std_ss [] \\ NO_TAC)
  \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o Q.SPECL [`seq (i:num)`,`r`,`(\j. seq (i + j))`])
  \\ `rel_sequence next (\j. seq (i + j)) (seq i)` by METIS_TAC [rel_sequence_shift]
  \\ FULL_SIMP_TAC std_ss [] \\ REVERSE STRIP_TAC \\ METIS_TAC [])

Theorem SPEC_MERGE:
    !x p1 p2 c1 m c2 q1 q2.
      SPEC x p1 c1 (q1 \/ m) /\ SPEC x (m \/ p2) c2 q2 ==>
      SPEC x (p1 \/ p2) (c1 UNION c2) (q1 \/ q2)
Proof
  METIS_TAC [SPEC_ADD_CODE,SPEC_COMPOSE_LEMMA,UNION_COMM]
QED

Theorem SPEC_COMPOSE:
    !x p c1 m c2 q. SPEC x p c1 m /\ SPEC x m c2 q ==> SPEC x p (c1 UNION c2) q
Proof
  REPEAT STRIP_TAC \\ MATCH_MP_TAC (REWRITE_RULE [SEP_CLAUSES]
  (Q.SPECL [`x`,`p`,`SEP_F`,`c1`,`m`,`c2`,`SEP_F`,`q`] SPEC_MERGE))
  \\ ASM_SIMP_TAC bool_ss []
QED

Theorem SPEC_COMPOSE_I:
    !x p c q1 q2 q3 q4.
      SPEC x (q1 * q3) c q2 ==> SPEC x p c (q1 * q4) ==>
      SEP_IMP q4 q3 ==> SPEC x p c q2
Proof
  REPEAT STRIP_TAC
  \\ `SEP_IMP (q1 * q4) (q1 * q3)` by METIS_TAC [SEP_IMP_REFL,SEP_IMP_STAR]
  \\ IMP_RES_TAC SPEC_WEAKEN \\ METIS_TAC [SPEC_COMPOSE,UNION_IDEMPOT]
QED

Theorem SPEC_FRAME_COMPOSE:
    !x p p' c1 m c2 q q' b1 b2.
       (b1 ==> SPEC x (m * q') c2 q) ==>
       (b2 ==> SPEC x p c1 (m * p')) ==>
       (b1 /\ b2) ==> SPEC x (p * q') (c1 UNION c2) (q * p')
Proof
  REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_COMPOSE
  \\ Q.EXISTS_TAC `m * p' * q'` \\ REPEAT STRIP_TAC \\ RES_TAC
  THEN1 (MATCH_MP_TAC SPEC_FRAME \\ ASM_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC SPEC_FRAME \\ METIS_TAC [STAR_ASSOC,STAR_COMM]
QED

Theorem SPEC_FRAME_COMPOSE_DISJ:
    !x p p' c1 m c2 q q' b1 b2 d.
       (b1 ==> SPEC x (m * q') c2 q) ==>
       (b2 ==> SPEC x p c1 (m * p' \/ d)) ==>
       (b1 /\ b2) ==> SPEC x (p * q') (c1 UNION c2) (q * p' \/ d * q')
Proof
  REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_COMPOSE \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `m * p' * q' \/ d * q'` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC SPEC_FRAME \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ MATCH_MP_TAC (RW [SEP_CLAUSES,UNION_IDEMPOT]
       (Q.SPECL [`x`,`p1`,`p2`,`c`,`SEP_F`,`c`] SPEC_MERGE))
  \\ POP_ASSUM (MP_TAC o Q.SPEC `p'`)
  \\ FULL_SIMP_TAC std_ss [SPEC_REFL, AC STAR_ASSOC STAR_COMM]
QED

val SEP_REFINE_HIDE = prove(
  ``SEP_REFINE (~p * q) less to_set state =
    ?x. SEP_REFINE (p x * q) less to_set state``,
  SIMP_TAC std_ss [SEP_REFINE_def,SEP_HIDE_def,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC []);

Theorem SPEC_HIDE_PRE:
    !x p p' c q. (!y:'var. SPEC x (p * p' y) c q) = SPEC x (p * ~ p') c q
Proof
  INIT_TAC \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ REWRITE_TAC [ONCE_REWRITE_RULE [STAR_COMM] SPEC_def,RUN_def,GSYM STAR_ASSOC]
  \\ SIMP_TAC std_ss [SEP_REFINE_HIDE] \\ METIS_TAC []
QED

Theorem SPEC_PRE_EXISTS:
    !x p c q. (!y:'var. SPEC x (p y) c q) = SPEC x (SEP_EXISTS y. p y) c q
Proof
  INIT_TAC \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [GSYM (RW [SEP_CLAUSES,SEP_HIDE_def] (Q.SPECL [`x`,`emp`] SPEC_HIDE_PRE))]
QED

val SEP_HIDE_INTRO = prove(
  ``!p q x s. SEP_IMP (p * q x) (p * ~ q)``,
  SIMP_TAC std_ss [STAR_def,SEP_HIDE_def,SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC []);

Theorem SPEC_HIDE_POST:
    !x p c q q' y:'var. SPEC x p c (q * q' y) ==> SPEC x p c (q * ~ q')
Proof
  METIS_TAC [SPEC_WEAKEN,SEP_HIDE_INTRO]
QED

Theorem SPEC_MOVE_COND:
    !x p c q g. SPEC x (p * cond g) c q = g ==> SPEC x p c q
Proof
  INIT_TAC \\ Cases_on `g`
  \\ REWRITE_TAC [SPEC_def,RUN_thm,SEP_CLAUSES,SEP_REFINE_def]
  \\ REWRITE_TAC [SEP_F_def]
QED

Theorem SPEC_DUPLICATE_COND:
    !x p c q g. SPEC x (p * cond g) c q ==> SPEC x (p * cond g) c (q * cond g)
Proof
  SIMP_TAC std_ss [SPEC_MOVE_COND,SEP_CLAUSES]
QED

Theorem SPEC_MERGE_COND:
    !x p c1 c2 q b1 b2.
       SPEC x (p * cond b1) c1 q ==>
       SPEC x (p * cond b2) c2 q ==>
       SPEC x (p * cond (b1 \/ b2)) (c1 UNION c2) q
Proof
  Cases_on `b1` \\ Cases_on `b2`
  \\ SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]
  \\ METIS_TAC [SPEC_ADD_CODE,SPEC_MERGE,SEP_CLAUSES,UNION_COMM]
QED

Theorem SPEC_MOVE_COND_POST:
    SPEC m (p * cond b) c q = SPEC m (p * cond b) c (q * cond b)
Proof
  SIMP_TAC std_ss [SPEC_MOVE_COND,SEP_CLAUSES]
QED

Theorem SPEC_ADD_DISJ:
    !x p c q. SPEC x p c q ==> !r. SPEC x p c (q \/ r)
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC SPEC_WEAKEN
  \\ POP_ASSUM (MATCH_MP_TAC o Q.SPEC `q \/ r`)
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]
QED

Theorem SPEC_PRE_DISJ:
    !x p1 p2 c q. SPEC x (p1 \/ p2) c q = SPEC x p1 c q /\ SPEC x p2 c q
Proof
  INIT_TAC \\ SIMP_TAC std_ss [SPEC_def,SEP_CLAUSES,RUN_def,
                SEP_REFINE_DISJ] \\ METIS_TAC []
QED

Theorem SPEC_PRE_DISJ_INTRO:
    !x p c q r. SPEC x p c (q \/ r) ==> SPEC x (p \/ r) c (q \/ r)
Proof
  SIMP_TAC std_ss [SPEC_PRE_DISJ] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (SPEC_ALL SPEC_REFL))
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]
QED

Theorem SPEC_EXISTS_EXISTS:
    (!x. SPEC m (P x) c (Q x)) ==> SPEC m (SEP_EXISTS x. P x) c (SEP_EXISTS x. Q x)
Proof
  SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `x`)
  \\ IMP_RES_TAC SPEC_WEAKEN \\ POP_ASSUM MATCH_MP_TAC
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ METIS_TAC []
QED

Theorem SPEC_TAILREC:
    !f1 (f2:'a->'b) g p res res' c m.
      (!x y. g x /\ p x /\ (y = f1 x) ==> SPEC m (res x) c (res y)) /\
      (!x y. ~g x /\ p x /\ (y = f2 x) ==> SPEC m (res x) c (res' y)) ==>
      (!x. TAILREC_PRE f1 g p x ==> SPEC m (res x) c (res' (TAILREC f1 f2 g x)))
Proof
  NTAC 9 STRIP_TAC THEN HO_MATCH_MP_TAC TAILREC_PRE_INDUCT
  THEN METIS_TAC [TAILREC_THM,UNION_IDEMPOT,SPEC_COMPOSE]
QED

Theorem SPEC_TAILREC_NEW:
    !f1 (f2:'a->'b) g p res res' c m.
      (!z x y. g x /\ p x /\ (y = f1 x) ==> SPEC m (res z x) c (res z y)) /\
      (!z x y. ~g x /\ p x /\ (y = f2 x) ==> SPEC m (res z x) c (res' z y)) ==>
      (!z x. TAILREC_PRE f1 g p x ==> SPEC m (res z x) c (res' z (TAILREC f1 f2 g x)))
Proof
  NTAC 10 STRIP_TAC THEN HO_MATCH_MP_TAC TAILREC_PRE_INDUCT
  THEN METIS_TAC [TAILREC_THM,UNION_IDEMPOT,SPEC_COMPOSE]
QED

Theorem SPEC_SHORT_TAILREC:
    !(f:'a -> ('a + 'b) # bool) res res' c m.
      (!x y. ISL (FST (f x)) /\ SND (f x) /\ (y = OUTL (FST (f x))) ==> SPEC m (res x) c (res y)) /\
      (!x y. ~ISL (FST (f x)) /\ SND (f x) /\ (y = OUTR (FST (f x))) ==> SPEC m (res x) c (res' y)) ==>
      (!x. SHORT_TAILREC_PRE f x ==> SPEC m (res x) c (res' (SHORT_TAILREC f x)))
Proof
  SIMP_TAC std_ss [SHORT_TAILREC_PRE_def,SHORT_TAILREC_def] \\ NTAC 6 STRIP_TAC
  \\ MATCH_MP_TAC SPEC_TAILREC \\ ASM_SIMP_TAC std_ss []
QED

Theorem SPEC_SHORT_TAILREC_NEW:
    !(f:'a -> ('a + 'b) # bool) res res' c m.
      (!z x y. ISL (FST (f x)) /\ SND (f x) /\ (y = OUTL (FST (f x))) ==> SPEC m (res z x) c (res z y)) /\
      (!z x y. ~ISL (FST (f x)) /\ SND (f x) /\ (y = OUTR (FST (f x))) ==> SPEC m (res z x) c (res' z y)) ==>
      (!z x. SHORT_TAILREC_PRE f x ==> SPEC m (res z x) c (res' z (SHORT_TAILREC f x)))
Proof
  SIMP_TAC std_ss [SHORT_TAILREC_PRE_def,SHORT_TAILREC_def] \\ NTAC 6 STRIP_TAC
  \\ MATCH_MP_TAC SPEC_TAILREC_NEW \\ ASM_SIMP_TAC std_ss []
QED


