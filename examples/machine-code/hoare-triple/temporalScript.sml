Theory temporal
Ancestors
  prog pair set_sep arithmetic

val _ = ParseExtras.temp_loose_equality()


(* --- definitions --- *)

Definition TEMPORAL_def:
  TEMPORAL ((to_set,next,instr,less,allow): ('a,'b,'c) processor) c exp =
   !state seq r.
     rel_sequence next seq state ==>
     let f p state = SEP_REFINE (p * CODE_POOL instr c * r) less to_set state
                     \/ allow state in
        exp f seq
End

val f = ``f: 'a set set -> 'b set``
val seq = ``seq: num -> 'b``

Definition NOW_def:          NOW p ^f seq        = f p (seq 0)
End
Definition NEXT_def:         NEXT p ^f seq       = p f (\n. seq (n + 1:num))
End
Definition EVENTUALLY_def:   EVENTUALLY p ^f seq = ?k. p f (\n. seq (n + k:num))
End
Definition ALWAYS_def:       ALWAYS p ^f seq      = !k. p f (\n. seq (n + k:num))
End

Definition T_AND_def:       T_AND p q ^f ^seq = p ^f ^seq /\ q ^f ^seq
End
Definition T_IMPLIES_def:   T_IMPLIES p q ^f ^seq = p f seq ==> q f seq
End

Definition T_OR_F_def:      T_OR_F p post ^f ^seq = p ^f ^seq \/
                                (EVENTUALLY (NOW post)) ^f ^seq
End

Definition SPEC_1_def:
  SPEC_1 model pre code post err <=>
    TEMPORAL model code
      (T_IMPLIES (NOW pre)
                 (T_OR_F (NEXT (EVENTUALLY (NOW post))) err))
End

(* --- theorems --- *)

val INIT = `?to_set next instr less allow. model = (to_set,next,instr,less,allow)`
           by METIS_TAC [PAIR]

Theorem SPEC_EQ_TEMPORAL:
    SPEC model pre code post <=>
    TEMPORAL model code (T_IMPLIES (NOW pre) (EVENTUALLY (NOW post)))
Proof
   INIT
   \\ ASM_SIMP_TAC std_ss
        [SPEC_def, TEMPORAL_def, RUN_def, LET_DEF, PULL_FORALL, T_IMPLIES_def,
         NOW_def, EVENTUALLY_def, rel_sequence_def]
   \\ SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM, GSYM rel_sequence_def]
   \\ METIS_TAC []
QED

Theorem TEMPORAL_ALWAYS:
    TEMPORAL model code (ALWAYS p) <=> TEMPORAL model code p
Proof
   INIT
   \\ ASM_SIMP_TAC std_ss
          [SPEC_def, TEMPORAL_def, RUN_def, LET_DEF,  PULL_FORALL,
           T_IMPLIES_def, NOW_def, ALWAYS_def]
   \\ REPEAT STRIP_TAC
   \\ EQ_TAC
   \\ REPEAT STRIP_TAC
   THEN1 (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`state`, `seq`, `r`, `0`])
          \\ FULL_SIMP_TAC std_ss []
          \\ CONV_TAC (DEPTH_CONV ETA_CONV)
          \\ SIMP_TAC std_ss [])
   \\ FIRST_X_ASSUM MATCH_MP_TAC
   \\ Q.EXISTS_TAC `seq k`
   \\ FULL_SIMP_TAC std_ss [rel_sequence_def]
   \\ REPEAT STRIP_TAC
   \\ FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `n + k`)
   \\ FULL_SIMP_TAC std_ss [ADD_CLAUSES]
QED

Theorem TEMPORAL_NEXT_IMP_EVENTUALLY:
    TEMPORAL model code (T_IMPLIES p1 (NEXT p2)) ==>
    TEMPORAL model code (T_IMPLIES p1 (EVENTUALLY p2))
Proof
   INIT
   \\ ASM_SIMP_TAC std_ss
         [TEMPORAL_def, LET_DEF, T_IMPLIES_def, NEXT_def, EVENTUALLY_def]
   \\ METIS_TAC []
QED

Theorem SPEC_1_IMP_SPEC:
    SPEC_1 model pre code post err ==>
    SPEC model pre code (post \/ err)
Proof
  INIT
  \\ FULL_SIMP_TAC std_ss [SPEC_1_def,SPEC_EQ_TEMPORAL,TEMPORAL_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [T_IMPLIES_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [T_OR_F_def]
  \\ FULL_SIMP_TAC std_ss [NEXT_def,EVENTUALLY_def]
  THEN1 (Q.EXISTS_TAC `k+1` \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
    \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [NOW_def,SEP_REFINE_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_DISJ_def] \\ METIS_TAC [])
  THEN1 (Q.EXISTS_TAC `k` \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
    \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [NOW_def,SEP_REFINE_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_DISJ_def] \\ METIS_TAC [])
QED

Theorem SPEC_IMP_SPEC_1:
    SPEC model pre code (post \/ err) ==>
    let to_set = FST model in
    let instr = FST (SND (SND model)) in
    let less = FST (SND (SND (SND model))) in
      (!s r. SEP_REFINE (pre * CODE_POOL instr code * r) less to_set s ==>
             ~SEP_REFINE (post * CODE_POOL instr code * r) less to_set s) ==>
    SPEC_1 model pre code post err
Proof
  INIT \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SPEC_EQ_TEMPORAL,SPEC_1_def]
  \\ FULL_SIMP_TAC std_ss [TEMPORAL_def,LET_DEF,T_IMPLIES_def]
  \\ REVERSE (REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [EVENTUALLY_def,NOW_def,T_OR_F_def,NEXT_def])
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [SEP_REFINE_def,SEP_F_def]
  \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC]
  THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ Cases_on `k` \\ FULL_SIMP_TAC std_ss [ADD1,SEP_DISJ_def]
  \\ METIS_TAC []
QED

val SEP_IMP_IMP_SEP_REFINE = prove(
  ``SEP_IMP q1 q3 ==>
    (!r1 r2 t2.
      SEP_REFINE (q1 * r1 * r2) m f t2 ==>
      SEP_REFINE (q3 * r1 * r2) m f t2)``,
  FULL_SIMP_TAC std_ss [SEP_REFINE_def,GSYM STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC SEP_IMP_FRAME
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def] \\ METIS_TAC []);

Theorem SPEC_1_STRENGTHEN:
    !model p c q err.
       SPEC_1 model p c q err ==> !r. SEP_IMP r p ==>
       SPEC_1 model r c q err
Proof
  STRIP_TAC \\ INIT \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [TEMPORAL_def,LET_DEF,PULL_FORALL,
       AND_IMP_INTRO,T_IMPLIES_def,ALWAYS_def,EVENTUALLY_def,
       NOW_def,T_OR_F_def,SPEC_1_def]
  \\ METIS_TAC [SEP_IMP_IMP_SEP_REFINE]
QED

Theorem SPEC_1_WEAKEN:
    !model p c r err.
       SPEC_1 model p c r err ==> !q. SEP_IMP r q ==>
       SPEC_1 model p c q err
Proof
  STRIP_TAC \\ INIT \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [TEMPORAL_def,LET_DEF,PULL_FORALL,
       AND_IMP_INTRO,T_IMPLIES_def,ALWAYS_def,EVENTUALLY_def,
       NOW_def,T_OR_F_def,SPEC_1_def,SEP_DISJ_def,SEP_CLAUSES,NEXT_def]
  \\ METIS_TAC [SEP_IMP_IMP_SEP_REFINE]
QED

Theorem SPEC_1_FRAME:
    !model p c q err. SPEC_1 model p c q err ==>
                      !r. SPEC_1 model (p * r) c (q * r) (err * r)
Proof
  STRIP_TAC \\ INIT \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [TEMPORAL_def,LET_DEF,PULL_FORALL,
       AND_IMP_INTRO,T_IMPLIES_def,ALWAYS_def,EVENTUALLY_def,
       NOW_def,T_OR_F_def,SPEC_1_def,SEP_DISJ_def,SEP_CLAUSES,NEXT_def]
  \\ NTAC 3 STRIP_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`state`,`seq`,`r * r'`])
  \\ FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]
QED

Theorem SPEC_MOVE_1_COND:
    !model p c q g err.
      SPEC_1 model (p * cond g) c q err <=> (g ==> SPEC_1 model p c q err)
Proof
  STRIP_TAC \\ INIT \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [TEMPORAL_def,LET_DEF,PULL_FORALL,
       AND_IMP_INTRO,T_IMPLIES_def,ALWAYS_def,EVENTUALLY_def,
       NOW_def,T_OR_F_def,SPEC_1_def,SEP_DISJ_def,SEP_CLAUSES,NEXT_def]
  \\ FULL_SIMP_TAC std_ss [SEP_REFINE_def]
  \\ Cases_on `g` \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [SEP_F_def] \\ METIS_TAC []
QED

Theorem SPEC_1_PRE_EXISTS:
    !model p c q err. (!y. SPEC_1 model (p y) c q err) <=>
                      SPEC_1 model (SEP_EXISTS y. p y) c q err
Proof
  STRIP_TAC \\ INIT \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [TEMPORAL_def,LET_DEF,PULL_FORALL,
       AND_IMP_INTRO,T_IMPLIES_def,ALWAYS_def,EVENTUALLY_def,
       NOW_def,T_OR_F_def,SPEC_1_def,SEP_DISJ_def,SEP_CLAUSES,NEXT_def]
  \\ FULL_SIMP_TAC std_ss [SEP_REFINE_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC []
QED

