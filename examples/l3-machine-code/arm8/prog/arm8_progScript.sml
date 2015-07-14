open HolKernel boolLib bossLib
open lcsymtacs blastLib stateLib
open set_sepTheory progTheory temporal_stateTheory arm8_stepTheory

val () = new_theory "arm8_prog"

(* ------------------------------------------------------------------------ *)

val _ =
   stateLib.sep_definitions "arm8"
      [["PSTATE"], ["SCTLR_EL1"], ["TCR_EL1"]]
      [["undefined"], ["branch_hint"]]
      arm8_stepTheory.NextStateARM8_def

val arm8_instr_def = Define`
   arm8_instr (a, i: word32) =
   { (arm8_c_MEM a, arm8_d_word8 ((7 >< 0) i));
     (arm8_c_MEM (a + 1w), arm8_d_word8 ((15 >< 8) i));
     (arm8_c_MEM (a + 2w), arm8_d_word8 ((23 >< 16) i));
     (arm8_c_MEM (a + 3w), arm8_d_word8 ((31 >< 24) i)) }`

val ARM8_MODEL_def = Define`
   ARM8_MODEL =
   (STATE arm8_proj, NEXT_REL (=) NextStateARM8, arm8_instr,
    ($= :arm8_state -> arm8_state -> bool), (K F: arm8_state -> bool))`

val ARM8_IMP_SPEC = Theory.save_thm ("ARM8_IMP_SPEC",
   stateTheory.IMP_SPEC
   |> Q.ISPECL [`arm8_proj`, `NextStateARM8`, `arm8_instr`]
   |> REWRITE_RULE [GSYM ARM8_MODEL_def]
   )

val ARM8_IMP_TEMPORAL = Theory.save_thm ("ARM8_IMP_TEMPORAL",
   temporal_stateTheory.IMP_TEMPORAL
   |> Q.ISPECL [`arm8_proj`, `NextStateARM8`, `arm8_instr`,
                `(=): arm8_state -> arm8_state -> bool`,
                `K F: arm8_state -> bool`]
   |> REWRITE_RULE [GSYM ARM8_MODEL_def]
   )

(* ------------------------------------------------------------------------ *)

(* Aliases *)

val arm8_REG_def = DB.definition "arm8_REG_def"
val arm8_MEM_def = DB.definition "arm8_MEM_def"

val (arm8_REGISTERS_def, arm8_REGISTERS_INSERT) =
   stateLib.define_map_component ("arm8_REGISTERS", "reg", arm8_REG_def)

val (arm8_MEMORY_def, arm8_MEMORY_INSERT) =
   stateLib.define_map_component ("arm8_MEMORY", "mem", arm8_MEM_def)

val arm8_WORD_def = Define`
   arm8_WORD a (i: word32) =
   arm8_MEM a ((7 >< 0) i) *
   arm8_MEM (a + 1w) ((15 >< 8) i) *
   arm8_MEM (a + 2w) ((23 >< 16) i) *
   arm8_MEM (a + 3w) ((31 >< 24) i)`;

val arm8_WORD_MEMORY_def = Define`
  arm8_WORD_MEMORY dmem mem =
  {BIGUNION { BIGUNION (arm8_WORD a (mem a)) | a IN dmem /\ aligned 2 a}}`

val arm8_DWORD_def = Define`
   arm8_DWORD a (i: word64) =
   arm8_MEM a ((7 >< 0) i) *
   arm8_MEM (a + 1w) ((15 >< 8) i) *
   arm8_MEM (a + 2w) ((23 >< 16) i) *
   arm8_MEM (a + 3w) ((31 >< 24) i) *
   arm8_MEM (a + 4w) ((39 >< 32) i) *
   arm8_MEM (a + 5w) ((47 >< 40) i) *
   arm8_MEM (a + 6w) ((55 >< 48) i) *
   arm8_MEM (a + 7w) ((63 >< 56) i)`;

val arm8_DWORD_MEMORY_def = Define`
  arm8_DWORD_MEMORY dmem mem =
  {BIGUNION { BIGUNION (arm8_DWORD a (mem a)) | a IN dmem /\ aligned 3 a}}`

val arm8_pc_def = Define`
   arm8_pc pc =
   arm8_PC pc * arm8_exception NoException * arm8_PSTATE_EL 0w *
   arm8_SCTLR_EL1_E0E F * arm8_TCR_EL1_TBI0 F * arm8_TCR_EL1_TBI1 F *
   arm8_SCTLR_EL1_SA0 F * set_sep$cond (aligned 2 pc)`;

val aS_def = Define `
   aS (n,z,c,v) =
   arm8_PSTATE_N n * arm8_PSTATE_Z z * arm8_PSTATE_C c * arm8_PSTATE_V v`;

(* ------------------------------------------------------------------------ *)

val aS_HIDE = Q.store_thm("aS_HIDE",
   `~aS = ~arm8_PSTATE_N * ~arm8_PSTATE_Z * ~arm8_PSTATE_C * ~arm8_PSTATE_V`,
   SIMP_TAC std_ss [SEP_HIDE_def, aS_def, SEP_CLAUSES, FUN_EQ_THM]
   \\ SIMP_TAC std_ss [SEP_EXISTS]
   \\ METIS_TAC [aS_def, pairTheory.PAIR]
   )

val arm_CPSR_T_F = Q.store_thm("arm_CPSR_T_F",
   `( n ==> (arm8_PSTATE_N T = arm8_PSTATE_N n)) /\
    (~n ==> (arm8_PSTATE_N F = arm8_PSTATE_N n)) /\
    ( z ==> (arm8_PSTATE_Z T = arm8_PSTATE_Z z)) /\
    (~z ==> (arm8_PSTATE_Z F = arm8_PSTATE_Z z)) /\
    ( c ==> (arm8_PSTATE_C T = arm8_PSTATE_C c)) /\
    (~c ==> (arm8_PSTATE_C F = arm8_PSTATE_C c)) /\
    ( v ==> (arm8_PSTATE_V T = arm8_PSTATE_V v)) /\
    (~v ==> (arm8_PSTATE_V F = arm8_PSTATE_V v))`,
    simp []
    )

(* ------------------------------------------------------------------------ *)

val arm8_PC_INTRO = Q.store_thm("arm8_PC_INTRO",
   `SPEC m (p1 * arm8_pc pc) code
       (p2 * arm8_PC pc' * arm8_exception NoException * arm8_PSTATE_EL 0w *
        arm8_SCTLR_EL1_E0E F * arm8_TCR_EL1_TBI0 F * arm8_TCR_EL1_TBI1 F *
        arm8_SCTLR_EL1_SA0 F) ==>
    (aligned 2 pc ==> aligned 2 pc') ==>
    SPEC m (p1 * arm8_pc pc) code (p2 * arm8_pc pc')`,
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss
        [arm8_pc_def, SPEC_MOVE_COND, STAR_ASSOC, SEP_CLAUSES]
   )

val arm8_TEMPORAL_PC_INTRO = Q.store_thm("arm8_TEMPORAL_PC_INTRO",
   `TEMPORAL_NEXT m (p1 * arm8_pc pc) code
       (p2 * arm8_PC pc' * arm8_exception NoException * arm8_PSTATE_EL 0w *
        arm8_SCTLR_EL1_E0E F * arm8_TCR_EL1_TBI0 F * arm8_TCR_EL1_TBI1 F *
        arm8_SCTLR_EL1_SA0 F) ==>
    (aligned 2 pc ==> aligned 2 pc') ==>
    TEMPORAL_NEXT m (p1 * arm8_pc pc) code (p2 * arm8_pc pc')`,
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss
         [arm8_pc_def, TEMPORAL_NEXT_MOVE_COND, STAR_ASSOC, SEP_CLAUSES]
   )

(* ------------------------------------------------------------------------ *)

val lem = Q.prove(
  `!x. ((\s. x = s) = {x})`,
  rewrite_tac [GSYM stateTheory.SEP_EQ_SINGLETON, set_sepTheory.SEP_EQ_def]
  \\ simp [FUN_EQ_THM]
  \\ REPEAT strip_tac
  \\ eq_tac
  \\ simp []
  )

fun thm v n x y =
   stateTheory.MAPPED_COMPONENT_INSERT
   |> Q.ISPECL
        [`\a:word64. aligned ^n a`, `2n ** ^n`, `\a i. arm8_c_MEM (a + n2w i)`,
         `\v i. arm8_d_word8 (EL i ^v)`, x, y]
   |> Conv.CONV_RULE
        (Conv.LAND_CONV
            (SIMP_CONV (srw_ss())
               [arm8_MEM_def, arm8_WORD_def, arm8_DWORD_def,
                pred_setTheory.INSERT_UNION_EQ, lem,
                set_sepTheory.STAR_def, set_sepTheory.SPLIT_def,
                blastLib.BBLAST_PROVE
                  ``a <> a + 1w:word64 /\ a <> a + 2w /\ a <> a + 3w /\
                    a <> a + 4w /\ a <> a + 5w /\ a <> a + 6w /\ a <> a + 7w``])
         THENC REWRITE_CONV [])

val lem1 = Q.prove(
   `!i. i < 4 ==> n2w i <+ (4w: word64)`,
   simp [wordsTheory.word_lo_n2w])

val lem2 = Q.prove(
   `aligned 2 (a: word64) /\ aligned 2 b /\ x <+ 4w /\ y <+ 4w ==>
    ((a + x = b + y) = (a = b) /\ (x = y))`,
   simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val v4 = ``[( 7 ><  0) v; (15 ><  8) v;
            (23 >< 16) v; (31 >< 24) (v:word32)]:word8 list``


(* Need ``(\a. ..) c`` below for automation to work *)
val arm8_WORD_MEMORY_INSERT = Q.store_thm("arm8_WORD_MEMORY_INSERT",
   `!f df c d.
     c IN df /\ (\a. aligned 2 a) c ==>
     (arm8_WORD c d * arm8_WORD_MEMORY (df DELETE c) f =
      arm8_WORD_MEMORY df ((c =+ d) f))`,
   match_mp_tac (thm v4 ``2n`` `arm8_WORD` `arm8_WORD_MEMORY`)
   \\ rw [arm8_WORD_MEMORY_def]
   \\ `(i = j) = (n2w i = n2w j: word64)` by simp []
   \\ asm_rewrite_tac []
   \\ match_mp_tac lem2
   \\ simp [lem1]
   )

val lem1 = Q.prove(
   `!i. i < 8 ==> n2w i <+ (8w: word64)`,
   simp [wordsTheory.word_lo_n2w])

val lem2 = Q.prove(
   `aligned 3 (a: word64) /\ aligned 3 b /\ x <+ 8w /\ y <+ 8w ==>
    ((a + x = b + y) = (a = b) /\ (x = y))`,
   simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val v8 = ``[( 7 ><  0) v; (15 ><  8) v;
            (23 >< 16) v; (31 >< 24) v;
            (39 >< 32) v; (47 >< 40) v;
            (55 >< 48) v; (63 >< 56) (v:word64)]:word8 list``

val arm8_DWORD_MEMORY_INSERT = Q.store_thm("arm8_DWORD_MEMORY_INSERT",
   `!f df c d.
     c IN df /\ (\a. aligned 3 a) c ==>
     (arm8_DWORD c d * arm8_DWORD_MEMORY (df DELETE c) f =
      arm8_DWORD_MEMORY df ((c =+ d) f))`,
   match_mp_tac (thm v8 ``3n`` `arm8_DWORD` `arm8_DWORD_MEMORY`)
   \\ rw [arm8_DWORD_MEMORY_def]
   \\ `(i = j) = (n2w i = n2w j: word64)` by simp []
   \\ asm_rewrite_tac []
   \\ match_mp_tac lem2
   \\ simp [lem1]
   )

(* ------------------------------------------------------------------------ *)

(* Theorems for moving literal loads into the code pool *)

val arm_instr_star = Q.prove(
   `!a w.
       {arm8_instr (a, w)} =
       arm8_MEM a ((7 >< 0) w) *
       arm8_MEM (a + 1w) ((15 >< 8) w) *
       arm8_MEM (a + 2w) ((23 >< 16) w) *
       arm8_MEM (a + 3w) ((31 >< 24) w)`,
   srw_tac [wordsLib.WORD_ARITH_EQ_ss]
       [pred_setTheory.INSERT_UNION_EQ, arm8_instr_def, arm8_MEM_def,
        set_sepTheory.STAR_def, set_sepTheory.SPLIT_def]
   \\ simp [boolTheory.FUN_EQ_THM]
   \\ metis_tac []
   )

val arm_instr_star_not_disjoint = Q.prove(
   `!a w p.
      ~DISJOINT (arm8_instr (a, w)) p ==>
        ({p} *
         arm8_MEM a ((7 >< 0) w) *
         arm8_MEM (a + 1w) ((15 >< 8) w) *
         arm8_MEM (a + 2w) ((23 >< 16) w) *
         arm8_MEM (a + 3w) ((31 >< 24) w) = SEP_F)`,
   rw [set_sepTheory.STAR_def, set_sepTheory.SPLIT_def,
       arm8_instr_def, arm8_MEM_def, pred_setTheory.DISJOINT_DEF]
   \\ simp [boolTheory.FUN_EQ_THM, set_sepTheory.SEP_F_def]
   \\ Cases_on `(arm8_c_MEM a,arm8_d_word8 ((7 >< 0) w)) IN p`
   \\ simp []
   \\ Cases_on `(arm8_c_MEM (a + 1w),arm8_d_word8 ((15 >< 8) w)) IN p`
   \\ simp []
   \\ Cases_on `(arm8_c_MEM (a + 2w),arm8_d_word8 ((23 >< 16) w)) IN p`
   \\ simp []
   \\ Cases_on `(arm8_c_MEM (a + 3w),arm8_d_word8 ((31 >< 24) w)) IN p`
   \\ simp []
   \\ fs [pred_setTheory.INSERT_INTER]
   )

val MOVE_TO_TEMPORAL_ARM_CODE_POOL = Q.store_thm
  ("MOVE_TO_TEMPORAL_ARM_CODE_POOL",
   `!a w c p q.
       TEMPORAL_NEXT ARM8_MODEL
        (p *
         arm8_MEM a ((7 >< 0) w) *
         arm8_MEM (a + 1w) ((15 >< 8) w) *
         arm8_MEM (a + 2w) ((23 >< 16) w) *
         arm8_MEM (a + 3w) ((31 >< 24) w))
        c
        (q *
         arm8_MEM a ((7 >< 0) w) *
         arm8_MEM (a + 1w) ((15 >< 8) w) *
         arm8_MEM (a + 2w) ((23 >< 16) w) *
         arm8_MEM (a + 3w) ((31 >< 24) w)) =
       TEMPORAL_NEXT ARM8_MODEL
        (cond (DISJOINT (arm8_instr (a, w)) (BIGUNION (IMAGE arm8_instr c))) *
         p)
        ((a, w) INSERT c)
        q`,
    REPEAT strip_tac
    \\ once_rewrite_tac [GSYM temporal_stateTheory.TEMPORAL_NEXT_CODE]
    \\ rewrite_tac [ARM8_MODEL_def, stateTheory.CODE_POOL,
                    pred_setTheory.IMAGE_INSERT,
                    pred_setTheory.IMAGE_EMPTY,
                    pred_setTheory.BIGUNION_INSERT,
                    pred_setTheory.BIGUNION_EMPTY]
    \\ Cases_on `DISJOINT (arm8_instr (a, w)) (BIGUNION (IMAGE arm8_instr c))`
    \\ rw [stateTheory.UNION_STAR, arm_instr_star, set_sepTheory.SEP_CLAUSES,
           temporal_stateTheory.TEMPORAL_NEXT_FALSE_PRE,
           AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
    \\ imp_res_tac arm_instr_star_not_disjoint
    \\ fs [set_sepTheory.SEP_CLAUSES,
           temporal_stateTheory.TEMPORAL_NEXT_FALSE_PRE,
           AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
    )

val MOVE_TO_ARM_CODE_POOL = Q.store_thm("MOVE_TO_ARM_CODE_POOL",
   `!a w c p q.
       SPEC ARM8_MODEL
        (p *
         arm8_MEM a ((7 >< 0) w) *
         arm8_MEM (a + 1w) ((15 >< 8) w) *
         arm8_MEM (a + 2w) ((23 >< 16) w) *
         arm8_MEM (a + 3w) ((31 >< 24) w))
        c
        (q *
         arm8_MEM a ((7 >< 0) w) *
         arm8_MEM (a + 1w) ((15 >< 8) w) *
         arm8_MEM (a + 2w) ((23 >< 16) w) *
         arm8_MEM (a + 3w) ((31 >< 24) w)) =
       SPEC ARM8_MODEL
        (cond (DISJOINT (arm8_instr (a, w)) (BIGUNION (IMAGE arm8_instr c))) *
         p)
        ((a, w) INSERT c)
        q`,
    REPEAT strip_tac
    \\ once_rewrite_tac [GSYM progTheory.SPEC_CODE]
    \\ rewrite_tac [ARM8_MODEL_def, stateTheory.CODE_POOL,
                    pred_setTheory.IMAGE_INSERT,
                    pred_setTheory.IMAGE_EMPTY,
                    pred_setTheory.BIGUNION_INSERT,
                    pred_setTheory.BIGUNION_EMPTY]
    \\ Cases_on `DISJOINT (arm8_instr (a, w)) (BIGUNION (IMAGE arm8_instr c))`
    \\ rw [stateTheory.UNION_STAR, arm_instr_star, set_sepTheory.SEP_CLAUSES,
           progTheory.SPEC_FALSE_PRE,
           AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
    \\ imp_res_tac arm_instr_star_not_disjoint
    \\ fs [set_sepTheory.SEP_CLAUSES, progTheory.SPEC_FALSE_PRE,
           AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
    )

val sub_intro = Theory.save_thm("sub_intro",
   simpLib.SIMP_PROVE (srw_ss()) []
      ``(a + (-b + c) = a - b + c : word64) /\ (a + -b = a - b)``
   )

val tac = asm_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss)
             [pred_setTheory.INSERT_INTER]

(*
val top = utilsLib.rhsc (wordsLib.WORD_EVAL_CONV ``word_T - 2w : word32``)
*)

val DISJOINT_arm_instr = Q.store_thm("DISJOINT_arm_instr",
   `!a pc x y.
      3w <+ a /\ a <+ 0xFFFFFFFFFFFFFFFDw ==>
      DISJOINT (arm8_instr (pc + a, x)) (arm8_instr (pc, y))`,
   rw [arm8_instr_def, pred_setTheory.DISJOINT_DEF]
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
   `!a x y. arm8_instr (a + 4w, x) INTER arm8_instr (a, y) = {}`,
   rw [arm8_instr_def, pred_setTheory.DISJOINT_DEF]
   \\ tac
   )

val DISJOINT_arm_instr_2 = Q.prove(
   `!a pc x1 x2 y.
      DISJOINT (arm8_instr (pc + a, x1))
               (arm8_instr (pc + a + 4w, x2) UNION arm8_instr (pc, y)) =
      DISJOINT (arm8_instr (pc + a, x1)) (arm8_instr (pc, y))`,
   rw [pred_setTheory.DISJOINT_DEF, lem]
   \\ metis_tac [pred_setTheory.INTER_COMM]
   )

val rearrange =
   blastLib.BBLAST_PROVE ``a + (b + c + d) = a + (b + c) + d : word64``

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
       disjoint_arm_instr `w2w (w: word12) + 8w`] @
      List.map disjoint_arm_instr_2 [`a`, `-a`, `a + b`, `a - b`])
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
