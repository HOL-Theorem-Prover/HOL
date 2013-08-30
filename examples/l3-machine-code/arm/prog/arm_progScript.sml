open HolKernel boolLib bossLib
open lcsymtacs blastLib stateLib arm_stepTheory

infix \\
val op \\ = op THEN;

val () = new_theory "arm_prog"

(* ------------------------------------------------------------------------ *)

val _ =
   stateLib.sep_definitions "arm"
      [["CPSR"], ["FP", "FPSCR"]]
      [["undefined"], ["CurrentCondition"], ["Encoding"]]
      arm_stepTheory.NextStateARM_def

val arm_MEM_def = DB.definition "arm_MEM_def"

val arm_instr_def = Define`
   arm_instr (a, i: word32) =
   { (arm_c_MEM a, arm_d_word8 ((7 >< 0) i));
     (arm_c_MEM (a + 1w), arm_d_word8 ((15 >< 8) i));
     (arm_c_MEM (a + 2w), arm_d_word8 ((23 >< 16) i));
     (arm_c_MEM (a + 3w), arm_d_word8 ((31 >< 24) i)) }`;

val ARM_IMP_SPEC = Theory.save_thm ("ARM_IMP_SPEC",
   Q.ISPECL [`arm_proj`, `NextStateARM`, `arm_instr`] stateTheory.IMP_SPEC
   )

(* ------------------------------------------------------------------------ *)

val arm_instr_star = Q.prove(
   `!a w.
       {arm_instr (a, w)} =
       arm_MEM a ((7 >< 0) w) *
       arm_MEM (a + 1w) ((15 >< 8) w) *
       arm_MEM (a + 2w) ((23 >< 16) w) *
       arm_MEM (a + 3w) ((31 >< 24) w)`,
   srw_tac [wordsLib.WORD_ARITH_EQ_ss]
       [pred_setTheory.INSERT_UNION_EQ, arm_instr_def, arm_MEM_def,
        set_sepTheory.STAR_def, set_sepTheory.SPLIT_def]
   \\ simp [boolTheory.FUN_EQ_THM]
   \\ metis_tac []
   )

val arm_instr_star_not_disjoint = Q.prove(
   `!a w p.
      ~DISJOINT (arm_instr (a, w)) p ==>
        ({p} *
         arm_MEM a ((7 >< 0) w) *
         arm_MEM (a + 1w) ((15 >< 8) w) *
         arm_MEM (a + 2w) ((23 >< 16) w) *
         arm_MEM (a + 3w) ((31 >< 24) w) = SEP_F)`,
   rw [set_sepTheory.STAR_def, set_sepTheory.SPLIT_def,
       arm_instr_def, arm_MEM_def, pred_setTheory.DISJOINT_DEF]
   \\ simp [boolTheory.FUN_EQ_THM, set_sepTheory.SEP_F_def]
   \\ Cases_on `(arm_c_MEM a,arm_d_word8 ((7 >< 0) w)) IN p`          \\ simp []
   \\ Cases_on `(arm_c_MEM (a + 1w),arm_d_word8 ((15 >< 8) w)) IN p`  \\ simp []
   \\ Cases_on `(arm_c_MEM (a + 2w),arm_d_word8 ((23 >< 16) w)) IN p` \\ simp []
   \\ Cases_on `(arm_c_MEM (a + 3w),arm_d_word8 ((31 >< 24) w)) IN p` \\ simp []
   \\ fs [pred_setTheory.INSERT_INTER]
   )

val MOVE_TO_ARM_CODE_POOL = Q.store_thm("MOVE_TO_ARM_CODE_POOL",
   `!a w c p q.
       SPEC (STATE arm_proj, NEXT_REL $= NextStateARM, arm_instr, $=)
        (p *
         arm_MEM a ((7 >< 0) w) *
         arm_MEM (a + 1w) ((15 >< 8) w) *
         arm_MEM (a + 2w) ((23 >< 16) w) *
         arm_MEM (a + 3w) ((31 >< 24) w))
        c
        (q *
         arm_MEM a ((7 >< 0) w) *
         arm_MEM (a + 1w) ((15 >< 8) w) *
         arm_MEM (a + 2w) ((23 >< 16) w) *
         arm_MEM (a + 3w) ((31 >< 24) w)) =
       SPEC (STATE arm_proj, NEXT_REL $= NextStateARM, arm_instr, $=)
        (cond (DISJOINT (arm_instr (a, w)) (BIGUNION (IMAGE arm_instr c))) * p)
        ((a, w) INSERT c)
        q`,
    REPEAT strip_tac
    \\ once_rewrite_tac [GSYM progTheory.SPEC_CODE]
    \\ rewrite_tac [stateTheory.CODE_POOL, pred_setTheory.IMAGE_INSERT,
                    pred_setTheory.IMAGE_EMPTY, pred_setTheory.BIGUNION_INSERT,
                    pred_setTheory.BIGUNION_EMPTY]
    \\ Cases_on `DISJOINT (arm_instr (a, w)) (BIGUNION (IMAGE arm_instr c))`
    \\ rw [stateTheory.UNION_STAR, arm_instr_star, set_sepTheory.SEP_CLAUSES,
           progTheory.SPEC_FALSE_PRE,
           AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
    \\ imp_res_tac arm_instr_star_not_disjoint
    \\ fs [set_sepTheory.SEP_CLAUSES, progTheory.SPEC_FALSE_PRE,
           AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
    )

val sub_intro = Theory.save_thm("sub_intro",
   simpLib.SIMP_PROVE (srw_ss()) []
      ``(a + (-b + c) = a - b + c : word32) /\ (a + -b = a - b)``
   )

val tac = asm_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss)
             [pred_setTheory.INSERT_INTER]

(*
val top = utilsLib.rhsc (wordsLib.WORD_EVAL_CONV ``word_T - 2w : word32``)
*)

val DISJOINT_arm_instr = Q.store_thm("DISJOINT_arm_instr",
   `!a pc x y.
      3w <+ a /\ a <+ 0xFFFFFFFDw ==>
      DISJOINT (arm_instr (pc + a, x)) (arm_instr (pc, y))`,
   rw [arm_instr_def, pred_setTheory.DISJOINT_DEF]
   \\ `a + 1w <> 0w` by blastLib.FULL_BBLAST_TAC
   \\ `a + 2w <> 0w` by blastLib.FULL_BBLAST_TAC
   \\ `a + 3w <> 0w` by blastLib.FULL_BBLAST_TAC
   \\ `a <> 0w` by blastLib.FULL_BBLAST_TAC
   \\ `3w <> a` by blastLib.FULL_BBLAST_TAC
   \\ `2w <> a` by blastLib.FULL_BBLAST_TAC
   \\ `1w <> a` by blastLib.FULL_BBLAST_TAC
   \\ tac
   )

val lem = Q.prove(
   `!a x y. arm_instr (a + 4w, x) INTER arm_instr (a, y) = {}`,
   rw [arm_instr_def, pred_setTheory.DISJOINT_DEF]
   \\ tac
   )

val DISJOINT_arm_instr_2 = Q.prove(
   `!a pc x1 x2 y.
      DISJOINT (arm_instr (pc + a, x1))
               (arm_instr (pc + a + 4w, x2) UNION arm_instr (pc, y)) =
      DISJOINT (arm_instr (pc + a, x1)) (arm_instr (pc, y))`,
   rw [pred_setTheory.DISJOINT_DEF, lem]
   \\ metis_tac [pred_setTheory.INTER_COMM]
   )

val rearrange =
   blastLib.BBLAST_PROVE ``a + (b + c + d) = a + (b + c) + d : word32``

fun disjoint_arm_instr q =
   DISJOINT_arm_instr
   |> Q.SPEC q
   |> Drule.SPEC_ALL
   |> Conv.CONV_RULE (LAND_CONV blastLib.BBLAST_CONV)
   |> REWRITE_RULE [rearrange]
   |> Drule.GEN_ALL

fun disjoint_arm_instr_2 q =
   DISJOINT_arm_instr_2
   |> Q.SPEC q
   |> REWRITE_RULE [sub_intro, wordsTheory.WORD_ADD_ASSOC,
                    GSYM wordsTheory.WORD_ADD_SUB_ASSOC]
   |> Drule.GEN_ALL

val disjoint_arm_instr_thms = Theory.save_thm("disjoint_arm_instr_thms",
   Drule.LIST_CONJ
     ([disjoint_arm_instr `(w2w (w: word8) + 8w) + 4w`,
       disjoint_arm_instr `w2w (w: word8) + 8w`,
       disjoint_arm_instr `w2w (w: word12) + 8w`,
       disjoint_arm_instr
         `^(bitstringSyntax.mk_v2w (bitstringSyntax.mk_bstring 10 0, ``:32``))
          + 8w`,
       disjoint_arm_instr
         `(^(bitstringSyntax.mk_v2w (bitstringSyntax.mk_bstring 10 0, ``:32``))
           + 8w) + 4w`] @
      List.map disjoint_arm_instr_2 [`a`, `-a`, `a + b`, `a - b`])
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
