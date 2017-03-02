open HolKernel boolLib bossLib
open lcsymtacs blastLib stateLib set_sepTheory progTheory m0_stepTheory

val () = new_theory "m0_prog"

(* ------------------------------------------------------------------------ *)

val _ = stateLib.sep_definitions "m0"
          [["PSR"], ["CONTROL"], ["AIRCR"]] [["pcinc"]]
          m0_stepTheory.NextStateM0_def

val m0_instr_def = Define`
  (m0_instr (a, INL (opc16: word16)) =
   { (m0_c_MEM a, m0_d_word8 ((7 >< 0) opc16));
     (m0_c_MEM (a + 1w), m0_d_word8 ((15 >< 8) opc16)) }) /\
  (m0_instr (a, INR (opc32: word32)) =
   { (m0_c_MEM a, m0_d_word8 ((23 >< 16) opc32));
     (m0_c_MEM (a + 1w), m0_d_word8 ((31 >< 24) opc32));
     (m0_c_MEM (a + 2w), m0_d_word8 ((7 >< 0) opc32));
     (m0_c_MEM (a + 3w), m0_d_word8 ((15 >< 8) opc32)) })`;

val M0_MODEL_def = Define`
  M0_MODEL = (STATE m0_proj, NEXT_REL (=) NextStateM0, m0_instr,
              ($= :m0_state -> m0_state -> bool), K F : m0_state -> bool)`

val M0_IMP_SPEC = Theory.save_thm ("M0_IMP_SPEC",
   stateTheory.IMP_SPEC
   |> Q.ISPECL [`m0_proj`, `NextStateM0`, `m0_instr`]
   |> REWRITE_RULE [GSYM M0_MODEL_def]
   )

val M0_IMP_TEMPORAL_NEXT = Theory.save_thm ("M0_IMP_TEMPORAL_NEXT",
   temporal_stateTheory.IMP_TEMPORAL
   |> Q.ISPECL [`m0_proj`, `NextStateM0`, `m0_instr`,
                `(=) : m0_state -> m0_state -> bool`, `K F : m0_state -> bool`]
   |> REWRITE_RULE [GSYM M0_MODEL_def]
   )

(* ------------------------------------------------------------------------ *)

val m0_REG_def = DB.definition "m0_REG_def"
val m0_MEM_def = DB.definition "m0_MEM_def"

val (m0_REGISTERS_def, m0_REGISTERS_INSERT) =
   stateLib.define_map_component ("m0_REGISTERS", "reg", m0_REG_def)

val (m0_MEMORY_def, m0_MEMORY_INSERT) =
   stateLib.define_map_component ("m0_MEMORY", "mem", m0_MEM_def)

val m0_WORD_def = Define`
   m0_WORD a (i: word32) =
   m0_MEM a ((7 >< 0) i) *
   m0_MEM (a + 1w) ((15 >< 8) i) *
   m0_MEM (a + 2w) ((23 >< 16) i) *
   m0_MEM (a + 3w) ((31 >< 24) i)`;

val m0_BE_WORD_def = Define`
   m0_BE_WORD a (i: word32) =
   m0_MEM a ((31 >< 24) i) *
   m0_MEM (a + 1w) ((23 >< 16) i) *
   m0_MEM (a + 2w) ((15 >< 8) i) *
   m0_MEM (a + 3w) ((7 >< 0) i)`;

val m0_CONFIG_def = Define`
   m0_CONFIG (bigend, spsel) =
      m0_exception NoException * m0_AIRCR_ENDIANNESS bigend *
      m0_CONTROL_SPSEL spsel`

val m0_PC_def = Define`
   m0_PC pc = m0_REG RName_PC pc * cond (aligned 1 pc)`

val m0_NZCV_def = Define`
   m0_NZCV (n,z,c,v) = m0_PSR_N n * m0_PSR_Z z * m0_PSR_C c * m0_PSR_V v`

(* ------------------------------------------------------------------------ *)

val m0_NZCV_HIDE = Q.store_thm("m0_NZCV_HIDE",
   `~m0_NZCV = ~m0_PSR_N * ~m0_PSR_Z * ~m0_PSR_C * ~m0_PSR_V`,
   SIMP_TAC std_ss [SEP_HIDE_def, m0_NZCV_def, SEP_CLAUSES, FUN_EQ_THM]
   \\ SIMP_TAC std_ss [SEP_EXISTS]
   \\ METIS_TAC [m0_NZCV_def, pairTheory.PAIR]
   )

val m0_PSR_T_F = Q.store_thm("m0_PSR_T_F",
   `( n ==> (m0_PSR_N T = m0_PSR_N n)) /\
    (~n ==> (m0_PSR_N F = m0_PSR_N n)) /\
    ( z ==> (m0_PSR_Z T = m0_PSR_Z z)) /\
    (~z ==> (m0_PSR_Z F = m0_PSR_Z z)) /\
    ( c ==> (m0_PSR_C T = m0_PSR_C c)) /\
    (~c ==> (m0_PSR_C F = m0_PSR_C c)) /\
    ( v ==> (m0_PSR_V T = m0_PSR_V v)) /\
    (~v ==> (m0_PSR_V F = m0_PSR_V v))`,
    simp []
    )

val m0_PC_INTRO = Q.store_thm("m0_PC_INTRO",
   `SPEC m (p1 * m0_PC pc) code (p2 * m0_REG RName_PC pc') ==>
    (aligned 1 pc ==> aligned 1 pc') ==>
    SPEC m (p1 * m0_PC pc) code (p2 * m0_PC pc')`,
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss [m0_PC_def, SPEC_MOVE_COND, STAR_ASSOC, SEP_CLAUSES]
   )

val m0_TEMPORAL_PC_INTRO = Q.store_thm("m0_TEMPORAL_PC_INTRO",
   `TEMPORAL_NEXT m (p1 * m0_PC pc) code (p2 * m0_REG RName_PC pc') ==>
    (aligned 1 pc ==> aligned 1 pc') ==>
    TEMPORAL_NEXT m (p1 * m0_PC pc) code (p2 * m0_PC pc')`,
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss
        [m0_PC_def, temporal_stateTheory.TEMPORAL_NEXT_MOVE_COND,
         STAR_ASSOC, SEP_CLAUSES]
   )

(* ------------------------------------------------------------------------ *)

(*
  Theorems for moving literal loads into the code pool (e.g. ldr r1, [pc, #4])
*)

val () = wordsLib.guess_lengths()

val data_to_thumb2_def = Define`
   data_to_thumb2 (w: word32) =
   INR ((15 >< 8) w @@ (7 >< 0) w @@ (31 >< 24) w @@ (23 >< 16) w):
   word16 + word32`

val tm = data_to_thumb2_def |> SPEC_ALL |> concl |> rhs |> rand

val byte_lem =
   utilsLib.map_conv blastLib.BBLAST_PROVE
      [``(31 >< 24) ^tm = (15 >< 8) w``,
       ``(23 >< 16) ^tm = (7 >< 0) w``,
       ``(15 >< 8) ^tm = (31 >< 24) w``,
       ``(7 >< 0) ^tm = (23 >< 16) w``]

val m0_instr_star = Q.prove(
   `!a w.
       {m0_instr (a, data_to_thumb2 w)} =
       m0_MEM a ((7 >< 0) w) *
       m0_MEM (a + 1w) ((15 >< 8) w) *
       m0_MEM (a + 2w) ((23 >< 16) w) *
       m0_MEM (a + 3w) ((31 >< 24) w)`,
   srw_tac [wordsLib.WORD_ARITH_EQ_ss]
       [pred_setTheory.INSERT_UNION_EQ, m0_instr_def, m0_MEM_def,
        data_to_thumb2_def, set_sepTheory.STAR_def, set_sepTheory.SPLIT_def,
        byte_lem]
   \\ simp [boolTheory.FUN_EQ_THM]
   \\ metis_tac []
   )

val m0_instr_star_not_disjoint = Q.prove(
   `!a w p.
      ~DISJOINT (m0_instr (a, data_to_thumb2 w)) p ==>
        ({p} *
         m0_MEM a ((7 >< 0) w) *
         m0_MEM (a + 1w) ((15 >< 8) w) *
         m0_MEM (a + 2w) ((23 >< 16) w) *
         m0_MEM (a + 3w) ((31 >< 24) w) = SEP_F)`,
   rw [set_sepTheory.STAR_def, set_sepTheory.SPLIT_def, m0_instr_def,
       data_to_thumb2_def, m0_MEM_def, pred_setTheory.DISJOINT_DEF, byte_lem]
   \\ simp [boolTheory.FUN_EQ_THM, set_sepTheory.SEP_F_def]
   \\ Cases_on `(m0_c_MEM a,m0_d_word8 ((7 >< 0) w)) IN p`          \\ simp []
   \\ Cases_on `(m0_c_MEM (a + 1w),m0_d_word8 ((15 >< 8) w)) IN p`  \\ simp []
   \\ Cases_on `(m0_c_MEM (a + 2w),m0_d_word8 ((23 >< 16) w)) IN p` \\ simp []
   \\ Cases_on `(m0_c_MEM (a + 3w),m0_d_word8 ((31 >< 24) w)) IN p` \\ simp []
   \\ fs [pred_setTheory.INSERT_INTER]
   )

val MOVE_TO_TEMPORAL_M0_CODE_POOL = Q.store_thm
  ("MOVE_TO_TEMPORAL_M0_CODE_POOL",
   `!a w c p q.
       TEMPORAL_NEXT M0_MODEL
        (p *
         m0_MEM a ((7 >< 0) w) *
         m0_MEM (a + 1w) ((15 >< 8) w) *
         m0_MEM (a + 2w) ((23 >< 16) w) *
         m0_MEM (a + 3w) ((31 >< 24) w))
        c
        (q *
         m0_MEM a ((7 >< 0) w) *
         m0_MEM (a + 1w) ((15 >< 8) w) *
         m0_MEM (a + 2w) ((23 >< 16) w) *
         m0_MEM (a + 3w) ((31 >< 24) w)) =
       TEMPORAL_NEXT M0_MODEL
        (cond (DISJOINT (m0_instr (a, data_to_thumb2 w))
              (BIGUNION (IMAGE m0_instr c))) * p)
        ((a, data_to_thumb2 w) INSERT c)
        q`,
    REPEAT strip_tac
    \\ once_rewrite_tac [GSYM temporal_stateTheory.TEMPORAL_NEXT_CODE]
    \\ rewrite_tac [M0_MODEL_def, stateTheory.CODE_POOL,
                    pred_setTheory.IMAGE_INSERT,
                    pred_setTheory.IMAGE_EMPTY,
                    pred_setTheory.BIGUNION_INSERT,
                    pred_setTheory.BIGUNION_EMPTY]
    \\ Cases_on `DISJOINT (m0_instr (a, data_to_thumb2 w))
                          (BIGUNION (IMAGE m0_instr c))`
    \\ rw [stateTheory.UNION_STAR, m0_instr_star, set_sepTheory.SEP_CLAUSES,
           temporal_stateTheory.TEMPORAL_NEXT_FALSE_PRE,
           AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
    \\ imp_res_tac m0_instr_star_not_disjoint
    \\ fs [set_sepTheory.SEP_CLAUSES,
           temporal_stateTheory.TEMPORAL_NEXT_FALSE_PRE,
           AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
    )

val MOVE_TO_M0_CODE_POOL = Q.store_thm("MOVE_TO_M0_CODE_POOL",
   `!a w c p q.
       SPEC M0_MODEL
        (p *
         m0_MEM a ((7 >< 0) w) *
         m0_MEM (a + 1w) ((15 >< 8) w) *
         m0_MEM (a + 2w) ((23 >< 16) w) *
         m0_MEM (a + 3w) ((31 >< 24) w))
        c
        (q *
         m0_MEM a ((7 >< 0) w) *
         m0_MEM (a + 1w) ((15 >< 8) w) *
         m0_MEM (a + 2w) ((23 >< 16) w) *
         m0_MEM (a + 3w) ((31 >< 24) w)) =
       SPEC M0_MODEL
        (cond (DISJOINT (m0_instr (a, data_to_thumb2 w))
                        (BIGUNION (IMAGE m0_instr c))) * p)
        ((a, data_to_thumb2 w) INSERT c)
        q`,
    REPEAT strip_tac
    \\ once_rewrite_tac [GSYM progTheory.SPEC_CODE]
    \\ rewrite_tac [M0_MODEL_def, stateTheory.CODE_POOL,
                    pred_setTheory.IMAGE_INSERT,
                    pred_setTheory.IMAGE_EMPTY,
                    pred_setTheory.BIGUNION_INSERT,
                    pred_setTheory.BIGUNION_EMPTY]
    \\ Cases_on `DISJOINT (m0_instr (a, data_to_thumb2 w))
                          (BIGUNION (IMAGE m0_instr c))`
    \\ rw [stateTheory.UNION_STAR, m0_instr_star, set_sepTheory.SEP_CLAUSES,
           progTheory.SPEC_FALSE_PRE,
           AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
    \\ imp_res_tac m0_instr_star_not_disjoint
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
val top = utilsLib.rhsc (wordsLib.WORD_EVAL_CONV ``word_T : word32``)
*)

val DISJOINT_m0_instr = Q.store_thm("DISJOINT_m0_instr",
   `!a pc x y.
      3w <+ a /\ a <+ 0xFFFFFFFDw ==>
      DISJOINT (m0_instr (pc + a, data_to_thumb2 x)) (m0_instr (pc, INL y))`,
   rw [m0_instr_def, data_to_thumb2_def, byte_lem, pred_setTheory.DISJOINT_DEF]
   \\ `a + 1w <> 0w` by blastLib.FULL_BBLAST_TAC
   \\ `a + 2w <> 0w` by blastLib.FULL_BBLAST_TAC
   \\ `a + 3w <> 0w` by blastLib.FULL_BBLAST_TAC
   \\ `a <> 0w` by blastLib.FULL_BBLAST_TAC
   \\ `3w <> a` by blastLib.FULL_BBLAST_TAC
   \\ `2w <> a` by blastLib.FULL_BBLAST_TAC
   \\ `1w <> a` by blastLib.FULL_BBLAST_TAC
   \\ tac
   )

fun disjoint_m0_instr q =
   DISJOINT_m0_instr
   |> Q.SPEC q
   |> Drule.SPEC_ALL
   |> Conv.CONV_RULE (LAND_CONV blastLib.BBLAST_CONV)
   |> REWRITE_RULE []
   |> Drule.GEN_ALL

val disjoint_m0_instr_thms = Theory.save_thm("disjoint_m0_instr_thms",
   disjoint_m0_instr `w2w (w: word10) + 4w`
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
