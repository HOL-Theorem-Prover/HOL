Theory temporal_state
Ancestors
  set_sep prog temporal state

(* ------------------------------------------------------------------------ *)

Definition TEMPORAL_NEXT_def:
   TEMPORAL_NEXT
      ((to_set,next,instr,less,avoid): ('a, 'b, 'c) processor) p c q =
   TEMPORAL (to_set,next,instr,$=,K F) c (T_IMPLIES (NOW p) (NEXT (NOW q)))
End

(* ------------------------------------------------------------------------ *)

val INIT =
   strip_tac
   \\ `?to_set next instr less avoid. x = (to_set,next,instr,less,avoid)`
   by metis_tac [pairTheory.PAIR]

Theorem TEMPORAL_NEXT_MOVE_COND:
    !x p c q g.
       TEMPORAL_NEXT x (p * cond g) c q <=> g ==> TEMPORAL_NEXT x p c q
Proof
   INIT
   \\ Cases_on `g`
   \\ simp [SEP_F_def, TEMPORAL_NEXT_def, TEMPORAL_def, SEP_CLAUSES,
            SEP_REFINE_def, T_IMPLIES_def, NOW_def]
QED

Theorem TEMPORAL_NEXT_FRAME:
    !x p c q. TEMPORAL_NEXT x p c q ==> !r. TEMPORAL_NEXT x (p * r) c (q * r)
Proof
   INIT
   \\ simp [GSYM STAR_ASSOC, TEMPORAL_NEXT_def, TEMPORAL_def,
            T_IMPLIES_def, NOW_def, NEXT_def]
   \\ REPEAT strip_tac
   \\ qpat_assum `!a. b`
         (qspecl_then [`state`, `seq`, `r * r'`] imp_res_tac)
   \\ fs [AC STAR_COMM STAR_ASSOC]
QED

Theorem TEMPORAL_NEXT_DUPLICATE_COND:
    !x p c q g.
        TEMPORAL_NEXT x (p * cond g) c q ==>
        TEMPORAL_NEXT x (p * cond g) c (q * cond g)
Proof
   simp [TEMPORAL_NEXT_MOVE_COND, SEP_CLAUSES]
QED

Theorem TEMPORAL_NEXT_FALSE_PRE:
    !x c q. TEMPORAL_NEXT x SEP_F c q
Proof
   INIT
   \\ simp [SEP_F_def, TEMPORAL_NEXT_def, TEMPORAL_def, SEP_CLAUSES,
            SEP_REFINE_def, T_IMPLIES_def, NOW_def]
QED

(* ------------------------------------------------------------------------ *)

val CODE_POOL_EMP = Q.prove(
   `!instr. CODE_POOL instr {} = emp`,
   simp [CODE_POOL_def, emp_def]
   )

val SPLIT_STATE_cor = METIS_PROVE [SPLIT_STATE]
   ``p (SELECT_STATE m y s) ==>
     ?u v. SPLIT (STATE m s) (u, v) /\ p u /\ (\v. v = FRAME_STATE m y s) v``

Theorem TEMPORAL_STATE_SEMANTICS:
    !m next instr less avoid p q.
       TEMPORAL_NEXT (STATE m, next, instr, less, avoid) p {} q =
       !state y seq.
          p (SELECT_STATE m y (seq 0)) /\ rel_sequence next seq state ==>
          q (SELECT_STATE m y (seq 1)) /\
          (FRAME_STATE m y (seq 0) = FRAME_STATE m y (seq 1))
Proof
   simp [TEMPORAL_NEXT_def, TEMPORAL_def, T_IMPLIES_def, NOW_def, NEXT_def,
         CODE_POOL_EMP, SEP_CLAUSES]
   \\ simp [STAR_def, SEP_REFINE_def]
   \\ REPEAT strip_tac
   \\ Tactical.REVERSE eq_tac
   \\ REPEAT strip_tac
   >- (full_simp_tac std_ss [SPLIT_STATE]
       \\ metis_tac [])
   \\ imp_res_tac SPLIT_STATE_cor
   \\ res_tac
   \\ full_simp_tac bool_ss [SPLIT_STATE]
   \\ metis_tac [FRAME_SET_EQ]
QED

val IMP_TEMPORAL = Q.prove(
   `!m next instr less avoid p q.
       (!y s.
          p (SELECT_STATE m y s) ==>
          ?v. (next s = SOME v) /\ q (SELECT_STATE m y v) /\
              (FRAME_STATE m y s = FRAME_STATE m y v)) ==>
       TEMPORAL_NEXT (STATE m, NEXT_REL (=) next, instr, less, avoid) p {} q`,
   rewrite_tac [TEMPORAL_STATE_SEMANTICS]
   \\ REPEAT strip_tac
   \\ `NEXT_REL (=) next (seq 0) (seq (SUC 0))`
   by (
       `?x. NEXT_REL (=) next (seq 0) x`
       by (res_tac
           \\ qexists_tac `v`
           \\ asm_simp_tac std_ss [NEXT_REL_def]
           \\ qexists_tac `seq 0`
           \\ asm_simp_tac std_ss []
           \\ full_simp_tac bool_ss [rel_sequence_def]
          )
       \\ metis_tac [rel_sequence_def]
      )
   \\ full_simp_tac std_ss [NEXT_REL_def]
   \\ qpat_assum `!y:'b set. P` (qspecl_then [`y`,`seq 0`] imp_res_tac)
   \\ metis_tac [optionTheory.SOME_11]
   )

Theorem TEMPORAL_NEXT_CODE:
    !x p c q.
       TEMPORAL_NEXT x (CODE_POOL (FST (SND (SND x))) c * p) {}
                       (CODE_POOL (FST (SND (SND x))) c * q) =
    TEMPORAL_NEXT x p c q
Proof
   INIT
   \\ simp [TEMPORAL_NEXT_def, TEMPORAL_def, T_IMPLIES_def, NOW_def, NEXT_def,
            CODE_POOL_EMP, SEP_CLAUSES,
            AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
QED

Theorem TEMPORAL_MOVE_CODE:
    !to_set next instr less avoid p c q.
       TEMPORAL_NEXT (to_set,next,instr,less,avoid)
          (p * CODE_POOL instr c) {} (q * CODE_POOL instr c) =
    TEMPORAL_NEXT (to_set,next,instr,less,avoid) p c q
Proof
   simp [TEMPORAL_NEXT_def, TEMPORAL_def, T_IMPLIES_def, NOW_def, NEXT_def,
         CODE_POOL_EMP, SEP_CLAUSES]
QED

val IMP_TEMPORAL = Theory.save_thm ("IMP_TEMPORAL",
   IMP_TEMPORAL
   |> Q.SPECL [`m`, `next`, `instr: 'd -> 'b # 'c -> bool`, `less`, `avoid`,
               `p * CODE_POOL instr (c: 'd -> bool)`,
               `q * CODE_POOL instr (c: 'd -> bool)`]
   |> REWRITE_RULE [TEMPORAL_MOVE_CODE]
   |> Q.GENL [`m`, `next`, `instr`, `less`, `avoid`, `c`, `p`, `q`]
   )

(* ------------------------------------------------------------------------ *)

fun SPECC_FRAME_RULE frame th =
   Thm.SPEC frame (Drule.MATCH_MP TEMPORAL_NEXT_FRAME th)

Theorem SEP_ARRAY_TEMPORAL_FRAME:
    !x (prefix: 'a word list) (postfix: 'a word list) p c q m i a l1 l2.
       (LENGTH l2 = LENGTH l1) /\
       TEMPORAL_NEXT x (p * SEP_ARRAY m i a l1) c (q * SEP_ARRAY m i a l2) ==>
       TEMPORAL_NEXT x (p * SEP_ARRAY m i (a - n2w (LENGTH prefix) * i)
                                      (prefix ++ l1 ++ postfix)) c
              (q * SEP_ARRAY m i (a - n2w (LENGTH prefix) * i)
                             (prefix ++ l2 ++ postfix))
Proof
   REPEAT strip_tac
   \\ rewrite_tac [set_sepTheory.SEP_ARRAY_APPEND]
   \\ pop_assum
        (assume_tac o
         SPECC_FRAME_RULE
            ``SEP_ARRAY (m: 'e word -> 'a word -> ('c -> bool) -> bool) i
                        (a - n2w (LENGTH prefix) * i) (prefix: 'a word list)``)
   \\ pop_assum
        (assume_tac o
         SPECC_FRAME_RULE
            ``SEP_ARRAY (m: 'e word -> 'a word -> ('c -> bool) -> bool) i
                        (a - n2w (LENGTH (prefix: 'a word list)) * i +
                         n2w (LENGTH (prefix ++ l1)) * i)
                        (postfix: 'a word list)``)
   \\ full_simp_tac (srw_ss()++helperLib.star_ss) []
QED

(* ------------------------------------------------------------------------ *)

