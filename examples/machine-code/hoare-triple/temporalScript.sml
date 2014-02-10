open HolKernel Parse boolLib bossLib
open progTheory pairTheory set_sepTheory arithmeticTheory;

val _ = new_theory "temporal"

infix \\ val op \\ = op THEN;

(* --- definitions --- *)

val TEMPORAL_def = Define `
  TEMPORAL ((to_set,next,instr,less,allow): ('a,'b,'c) processor) c exp =
   !state seq r.
     rel_sequence next seq state ==>
     let f p state = SEP_REFINE (p * CODE_POOL instr c * r) less to_set state
                     \/ allow state in
        exp f seq`

val f = ``f: 'a set set -> 'b set``
val seq = ``seq: num -> 'b``

val NOW_def        = Define `NOW p ^f seq        = f p (seq 0)`
val NEXT_def       = Define `NEXT p ^f seq       = p f (\n. seq (n + 1:num))`
val EVENTUALLY_def = Define `EVENTUALLY p ^f seq = ?k. p f (\n. seq (n + k:num))`
val ALWAYS_def     = Define `ALWAYS p ^f seq      = !k. p f (\n. seq (n + k:num))`

val T_AND_def     = Define `T_AND p q ^f ^seq = p f seq /\ q f seq`
val T_IMPLIES_def = Define `T_IMPLIES p q ^f ^seq = p f seq ==> q f seq`

(* --- theorems --- *)

val INIT = `?to_set next instr less allow. model = (to_set,next,instr,less,allow)`
           by METIS_TAC [PAIR]

val SPEC_EQ_TEMPORAL = Q.store_thm("SPEC_EQ_TEMPORAL",
   `SPEC model pre code post <=>
    TEMPORAL model code (T_IMPLIES (NOW pre) (EVENTUALLY (NOW post)))`,
   INIT
   \\ ASM_SIMP_TAC std_ss
        [SPEC_def, TEMPORAL_def, RUN_def, LET_DEF, PULL_FORALL, T_IMPLIES_def,
         NOW_def, EVENTUALLY_def, rel_sequence_def]
   \\ SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM, GSYM rel_sequence_def]
   \\ METIS_TAC []
   );

val TEMPORAL_ALWAYS = Q.store_thm("TEMPORAL_ALWAYS",
   `TEMPORAL model code (ALWAYS p) <=> TEMPORAL model code p`,
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
   )

val TEMPORAL_NEXT_IMP_EVENTUALLY = Q.store_thm("TEMPORAL_NEXT_IMP_EVENTUALLY",
   `TEMPORAL model code (T_IMPLIES p1 (NEXT p2)) ==>
    TEMPORAL model code (T_IMPLIES p1 (EVENTUALLY p2))`,
   INIT
   \\ ASM_SIMP_TAC std_ss
         [TEMPORAL_def, LET_DEF, T_IMPLIES_def, NEXT_def, EVENTUALLY_def]
   \\ METIS_TAC []
   )

val _ = export_theory()
