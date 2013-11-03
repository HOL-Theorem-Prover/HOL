open HolKernel boolLib bossLib
open lcsymtacs set_sepTheory progTheory

val _ = new_theory "state"

infix \\
val op \\ = op THEN;

(* ------------------------------------------------------------------------ *)

val NEXT_REL_def = Define `NEXT_REL r next s t = ?u. r s u /\ (next u = SOME t)`

val SELECT_STATE_def = Define `SELECT_STATE m d s = fun2set (m s, d)`

val STATE_def = Define `STATE m = SELECT_STATE m UNIV`

val FRAME_STATE_def = Define `FRAME_STATE m d = SELECT_STATE m (COMPL d)`

(* ------------------------------------------------------------------------ *)

val NEXT_REL_EQ = Q.store_thm ("NEXT_REL_EQ",
   `!next. NEXT_REL (=) next = \s t. next s = SOME t`,
   rw [NEXT_REL_def, FUN_EQ_THM])

val PreOrder_EQ = Q.store_thm ("PreOrder_EQ",
   `PreOrder (=)`,
   rw [relationTheory.PreOrder, relationTheory.reflexive_def,
       relationTheory.transitive_def])

val FRAME_SET_EQ = Q.store_thm ("FRAME_SET_EQ",
   `!m x y s t. (FRAME_STATE m x s = FRAME_STATE m y t) ==> (x = y)`,
   simp [pred_setTheory.EXTENSION, FRAME_STATE_def, SELECT_STATE_def,
         fun2set_def]
   \\ metis_tac [pairTheory.FST])

val SEP_EQ_SINGLETON = Q.store_thm ("SEP_EQ_SINGLETON",
   `!x. SEP_EQ x = { x }`,
   rw [SEP_EQ_def, pred_setTheory.EXTENSION, boolTheory.IN_DEF])

val SPLIT_STATE = Q.store_thm ("SPLIT_STATE",
   `!m s u v.
      SPLIT (STATE m s) (u, v) =
      ?y. (u = SELECT_STATE m y s) /\ (v = FRAME_STATE m y s)`,
   rw [SPLIT_def, STATE_def, SELECT_STATE_def, FRAME_STATE_def,
       pred_setTheory.DISJOINT_DEF, fun2set_def]
   \\ eq_tac
   \\ rw [pred_setTheory.EXTENSION]
   >| [
      qexists_tac `IMAGE FST u`
      \\ rw []
      \\ metis_tac [pairTheory.FST],
      eq_tac \\ rw [],
      metis_tac [pairTheory.FST]
   ])

val SPLIT_STATE_cor = METIS_PROVE [SPLIT_STATE]
   ``p (SELECT_STATE m y s) ==>
     ?u v. SPLIT (STATE m s) (u, v) /\ p u /\ (\v. v = FRAME_STATE m y s) v``

(* ........................................................................ *)

val R_STATE_SEMANTICS = Q.store_thm ("R_STATE_SEMANTICS",
   `!m next instr r p q.
       SPEC (STATE m, next, instr, r) p {} q =
       !y s t1 seq.
          p (SELECT_STATE m y t1) /\ r t1 s /\ rel_sequence next seq s ==>
          ?k t2. q (SELECT_STATE m y t2) /\ r t2 (seq k) /\
                 (FRAME_STATE m y t1 = FRAME_STATE m y t2)`,
   simp [GSYM RUN_EQ_SPEC, RUN_def, STAR_def, SEP_REFINE_def]
   \\ REPEAT strip_tac
   \\ Tactical.REVERSE eq_tac
   \\ REPEAT strip_tac
   >- (full_simp_tac std_ss [SPLIT_STATE]
       \\ metis_tac [])
   \\ full_simp_tac std_ss
        [METIS_PROVE [] ``((?x. P x) ==> b) = !x. P x ==> b``,
         METIS_PROVE [] ``(b /\ (?x. P x)) = ?x. b /\ P x``]
   \\ full_simp_tac std_ss [GSYM AND_IMP_INTRO]
   \\ imp_res_tac SPLIT_STATE_cor
   \\ res_tac
   \\ full_simp_tac bool_ss [SPLIT_STATE]
   \\ metis_tac [FRAME_SET_EQ]
   )

val STATE_SEMANTICS = Q.store_thm ("STATE_SEMANTICS",
   `!m next instr p q.
       SPEC (STATE m, next, instr, $=) p {} q =
       !y s seq.
          p (SELECT_STATE m y s) /\ rel_sequence next seq s ==>
          ?k. q (SELECT_STATE m y (seq k)) /\
              (FRAME_STATE m y s = FRAME_STATE m y (seq k))`,
   rw [R_STATE_SEMANTICS])

val IMP_R_SPEC = Q.prove(
   `!r m next instr p q.
       PreOrder r ==>
       (!y s t1.
          p (SELECT_STATE m y t1) /\ r t1 s ==>
          ?v t2.
             p (SELECT_STATE m y s) /\
             (next s = SOME v) /\ q (SELECT_STATE m y t2) /\ r t2 v /\
             (FRAME_STATE m y t1 = FRAME_STATE m y t2)) ==>
       SPEC (STATE m, NEXT_REL r next, instr, r) p {} q`,
   rewrite_tac [R_STATE_SEMANTICS, relationTheory.PreOrder,
                relationTheory.reflexive_def, relationTheory.transitive_def]
   \\ REPEAT strip_tac
   \\ `p (SELECT_STATE m y s)` by metis_tac []
   \\ `NEXT_REL r next (seq 0) (seq (SUC 0))`
   by (
       `?x. NEXT_REL r next (seq 0) x`
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
   \\ `seq 0 = s` by full_simp_tac std_ss [rel_sequence_def]
   \\ full_simp_tac std_ss []
   \\ qexists_tac `1`
   \\ `r t1 u` by metis_tac []
   \\ qpat_assum `!y:'b set. P`
        (qspecl_then [`y`,`u`,`t1`]
           (strip_assume_tac o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO]))
   \\ qexists_tac `t2`
   \\ metis_tac [optionTheory.SOME_11]
   )

val IMP_SPEC = Q.prove(
   `!m next instr p q.
       (!y s.
          p (SELECT_STATE m y s) ==>
          ?v. (next s = SOME v) /\ q (SELECT_STATE m y v) /\
              (FRAME_STATE m y s = FRAME_STATE m y v)) ==>
       SPEC (STATE m, NEXT_REL (=) next, instr, (=)) p {} q`,
   REPEAT strip_tac
   \\ qspec_then `(=)` (match_mp_tac o REWRITE_RULE [PreOrder_EQ]) IMP_R_SPEC
   \\ metis_tac [])

val STATE_SPEC_CODE =
   Drule.ISPEC
    (IMP_R_SPEC
     |> Drule.SPEC_ALL
     |> Thm.concl
     |> boolSyntax.dest_imp |> snd
     |> boolSyntax.dest_imp |> snd
     |> boolSyntax.rator
     |> boolSyntax.rator
     |> boolSyntax.rator
     |> boolSyntax.rand) SPEC_CODE
   |> SIMP_RULE std_ss []
   |> Drule.GEN_ALL

val IMP_R_SPEC = Theory.save_thm ("IMP_R_SPEC",
   IMP_R_SPEC
   |> Q.SPECL [`r`, `m`, `next`, `instr: 'd -> 'b # 'c -> bool`,
               `CODE_POOL instr (c: 'd -> bool) * p`,
               `CODE_POOL instr (c: 'd -> bool) * q`]
   |> REWRITE_RULE [STATE_SPEC_CODE]
   |> ONCE_REWRITE_RULE [STAR_COMM]
   |> Q.GENL [`q`, `p`, `c`, `instr`, `next`, `m`, `r`]
   )

val IMP_SPEC = Theory.save_thm ("IMP_SPEC",
   IMP_SPEC
   |> Q.SPECL [`m`, `next`, `instr: 'd -> 'b # 'c -> bool`,
               `CODE_POOL instr (c: 'd -> bool) * p`,
               `CODE_POOL instr (c: 'd -> bool) * q`]
   |> REWRITE_RULE [STATE_SPEC_CODE]
   |> ONCE_REWRITE_RULE [STAR_COMM]
   |> Q.GENL [`q`, `p`, `c`, `instr`, `next`, `m`]
   )

val CODE_POOL = Theory.save_thm ("CODE_POOL",
   REWRITE_RULE [GSYM SEP_EQ_def, SEP_EQ_SINGLETON] CODE_POOL_def)

(* ........................................................................ *)

(*
val DIFF_EMPTY = Q.store_thm("DIFF_EMPTY",
   `!t v s. (t = v) /\ (s DIFF t = {}) ==> (s DIFF v = {})`,
   ntac 2 (srw_tac [] [])
   )
*)

val IN_SUBSET = Q.prove(
   `!a A B. a IN A /\ A SUBSET B ==> a IN B`,
   srw_tac [] [pred_setTheory.SUBSET_DEF])

val PAIR_GRAPH = Q.prove(
   `!m s.
       (!e. e IN s ==> (SND e = m (FST e))) =
       (!a b. (a, b) IN s ==> (b = m a))`,
   REPEAT strip_tac
   \\ eq_tac
   \\ rw []
   \\ metis_tac [pairTheory.FST, pairTheory.SND])

val IN_fun2set_cor =
   IN_fun2set
   |> Q.SPECL [`FST c`, `SND c`]
   |> REWRITE_RULE [pairTheory.PAIR]
   |> Drule.GEN_ALL

val SUBSET_fun2set = Q.prove(
   `!m s cd x.
      cd SUBSET fun2set (m s, x) =
      IMAGE FST cd SUBSET x /\ (!e. e IN cd ==> (SND e = m s (FST e)))`,
   rw [fun2set_def, pred_setTheory.SUBSET_DEF]
   \\ eq_tac
   \\ rw []
   \\ metis_tac [pairTheory.FST, pairTheory.SND, pairTheory.PAIR]
   )

val fun2set_DIFF = Q.prove(
   `!x f q. (!e. e IN q ==> (SND e = f (FST e))) ==>
            (fun2set (f, x) DIFF q = fun2set (f, x DIFF IMAGE FST q))`,
   rw [pred_setTheory.EXTENSION, IN_fun2set_cor]
   \\ eq_tac
   \\ rw []
   \\ metis_tac [pairTheory.FST, pairTheory.SND, pairTheory.PAIR]
   )

val fun2set_DIFF2 = Q.prove(
   `!x m s q.
       q SUBSET (fun2set (m s, x)) ==>
       (fun2set (m s, x) DIFF q = fun2set (m s, x DIFF IMAGE FST q))`,
   metis_tac [fun2set_DIFF, SUBSET_fun2set, PAIR_GRAPH]
   )

val STAR_SELECT_STATE = Q.store_thm ("STAR_SELECT_STATE",
   `!cd m p s x.
       ({cd} * p) (SELECT_STATE m x s) =
       (!c d. (c, d) IN cd ==> (m s c = d)) /\ IMAGE FST cd SUBSET x /\
       p (SELECT_STATE m (x DIFF IMAGE FST cd) s)`,
   REPEAT strip_tac
   \\ once_rewrite_tac [GSYM SEP_EQ_SINGLETON]
   \\ simp [SELECT_STATE_def, EQ_STAR]
   \\ eq_tac
   \\ rw []
   >- metis_tac [IN_SUBSET, IN_fun2set, PAIR_GRAPH]
   >- metis_tac [SUBSET_fun2set]
   >- metis_tac [fun2set_DIFF2, PAIR_GRAPH]
   >- metis_tac [fun2set_DIFF, PAIR_GRAPH]
   \\ metis_tac [SUBSET_fun2set, PAIR_GRAPH]
   )

(*
val STAR_SELECT_STATE1 = Theory.save_thm ("STAR_SELECT_STATE1",
   STAR_SELECT_STATE
   |> Q.SPEC `{(v, w)}`
   |> SIMP_RULE (srw_ss()) [GSYM pred_setTheory.DELETE_DEF]
   |> Drule.GEN_ALL
   )
*)

val emp_SELECT_STATE = Q.store_thm ("emp_SELECT_STATE",
   `!m x s. emp (SELECT_STATE m x s) = (x = {})`,
   rw [emp_def, SELECT_STATE_def, fun2set_def, pred_setTheory.EXTENSION]
   )

(* ........................................................................ *)

val UPDATE_FRAME_STATE = Q.store_thm ("UPDATE_FRAME_STATE",
   `!m f u r.
      (!b s a w. b <> f a ==> (m (u s a w) b = m (r s) b)) ==>
      !a w s x.
          f a IN x ==> (FRAME_STATE m x (u s a w) = FRAME_STATE m x (r s))`,
   rw [FRAME_STATE_def, SELECT_STATE_def, fun2set_def, pred_setTheory.EXTENSION]
   \\ metis_tac []
   )

(* ........................................................................ *)

val UNION_STAR = Q.store_thm("UNION_STAR",
   `!a b c. DISJOINT a b ==> ({a UNION b} * c = {a} * {b} * c)`,
   simp [set_sepTheory.STAR_def, set_sepTheory.SPLIT_def]
   )

val BIGUNION_IMAGE_1 = Q.store_thm("BIGUNION_IMAGE_1",
   `!f x. BIGUNION (IMAGE f {x}) = f x`,
   simp []
   )

val BIGUNION_IMAGE_2 = Q.store_thm("BIGUNION_IMAGE_2",
   `!f x y. BIGUNION (IMAGE f {x; y}) = f x UNION f y`,
   simp []
   )

(* ........................................................................ *)

val SEP_EQ_STAR = Q.store_thm("SEP_EQ_STAR",
   `((q = p1 UNION p2) /\ DISJOINT p1 p2) ==>
    ((SEP_EQ p1 * SEP_EQ p2) = (SEP_EQ q))`,
  REPEAT strip_tac
  \\ simp_tac std_ss [SEP_EQ_def, Once FUN_EQ_THM, STAR_def, SPLIT_def]
  \\ METIS_TAC []
  )

val MAPPED_COMPONENT_INSERT = Q.store_thm("MAPPED_COMPONENT_INSERT",
   `!P n x y single_c map_c.
     (!c d. single_c c d = {set (GENLIST (\i. (x c i, y d i)) n)}) ==>
     (!a b i j. P a /\ P b /\ i < n /\ j < n ==>
                ((x a i = x b j) = (a = b) /\ (i = j))) /\
     (!df f. map_c df f =
             {BIGUNION {BIGUNION (single_c c (f c)) | c | c IN df /\ P c}}) ==>
     !f df c d.
       c IN df /\ P c ==>
       (single_c c d * map_c (df DELETE c) f = map_c df ((c =+ d) f))`,
   REPEAT strip_tac
   \\ asm_rewrite_tac [GSYM SEP_EQ_SINGLETON]
   \\ match_mp_tac SEP_EQ_STAR
   \\ rewrite_tac [SEP_EQ_SINGLETON, pred_setTheory.BIGUNION_SING,
                   pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION]
   \\ rw [boolTheory.PULL_EXISTS, combinTheory.APPLY_UPDATE_THM,
          listTheory.MEM_GENLIST]
   >- metis_tac []
   \\ Cases_on `x'`     \\ simp [] (* shouldn't rely on name here *)
   \\ Cases_on `i < n`  \\ simp []
   \\ Cases_on `i' < n` \\ simp []
   \\ metis_tac []
   )

val cnv = SIMP_CONV (srw_ss()) [DECIDE ``i < 1n = (i = 0)``]

val MAPPED_COMPONENT_INSERT1 = Theory.save_thm("MAPPED_COMPONENT_INSERT1",
   MAPPED_COMPONENT_INSERT
   |> Q.SPECL [`K T`, `1n`, `\c i. x c`, `\d i. y d`]
   |> Conv.CONV_RULE
        (Conv.STRIP_QUANT_CONV
           (Conv.RATOR_CONV cnv
            THENC Conv.RAND_CONV (Conv.RATOR_CONV cnv)
            THENC REWRITE_CONV [combinTheory.K_THM]))
   |> Drule.GEN_ALL)

val MAPPED_COMPONENT_INSERT_OPT = Q.store_thm("MAPPED_COMPONENT_INSERT_OPT",
   `!y x single_c map_c.
      (!c d. single_c c d = {{(x c,y d)}}) ==>
      (!a b. (x a = x b) <=> (a = b)) /\
      (!df f.
         map_c df f =
         {BIGUNION {BIGUNION (single_c c (SOME (f c))) | c IN df}}) ==>
      !f df c d.
        c IN df ==>
        (single_c c (SOME d) * map_c (df DELETE c) f = map_c df ((c =+ d) f))`,
   REPEAT strip_tac
   \\ asm_rewrite_tac [GSYM SEP_EQ_SINGLETON]
   \\ match_mp_tac SEP_EQ_STAR
   \\ rewrite_tac [SEP_EQ_SINGLETON, pred_setTheory.BIGUNION_SING,
                   pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION]
   \\ rw [boolTheory.PULL_EXISTS, combinTheory.APPLY_UPDATE_THM]
   >- metis_tac []
   \\ Cases_on `x'` \\ simp [] (* shouldn't rely on name here *)
   \\ metis_tac []
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory ()
