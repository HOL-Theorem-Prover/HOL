open HolKernel boolLib bossLib
open lcsymtacs blastLib stateLib set_sepTheory progTheory m0_stepTheory

val () = new_theory "m0_prog"

infix \\
val op \\ = op THEN;

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
              ($= :m0_state -> m0_state -> bool))`

val M0_IMP_SPEC = Theory.save_thm ("M0_IMP_SPEC",
   stateTheory.IMP_SPEC
   |> Q.ISPECL [`m0_proj`, `NextStateM0`, `m0_instr`]
   |> REWRITE_RULE [GSYM M0_MODEL_def]
   )

val M0_IMP_TEMPORAL_NEXT = Theory.save_thm ("M0_IMP_TEMPORAL_NEXT",
   temporal_stateTheory.IMP_TEMPORAL
   |> Q.ISPECL [`m0_proj`, `NextStateM0`, `m0_instr`]
   |> REWRITE_RULE [GSYM M0_MODEL_def]
   )

(* ------------------------------------------------------------------------ *)

val m0_REG_def = DB.definition "m0_REG_def"
val m0_MEM_def = DB.definition "m0_MEM_def"

val (m0_REGISTERS_def, m0_REGISTERS_INSERT) =
   stateLib.define_map_component ("m0_REGISTERS", "reg", m0_REG_def)

val (m0_MEMORY_def, m0_MEMORY_INSERT) =
   stateLib.define_map_component ("m0_MEMORY", "mem", m0_MEM_def)

val m0_CONFIG_def = Define`
   m0_CONFIG (bigend, spsel) =
      m0_exception NoException * m0_AIRCR_ENDIANNESS bigend *
      m0_CONTROL_SPSEL spsel`

val m0_PC_def = Define`
   m0_PC pc = m0_REG RName_PC pc * cond (Aligned (pc,2))`

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
    (Aligned (pc,2) ==> Aligned (pc',2)) ==>
    SPEC m (p1 * m0_PC pc) code (p2 * m0_PC pc')`,
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss [m0_PC_def, SPEC_MOVE_COND, STAR_ASSOC, SEP_CLAUSES]
   )

val m0_TEMPORAL_PC_INTRO = Q.store_thm("m0_TEMPORAL_PC_INTRO",
   `TEMPORAL_NEXT m (p1 * m0_PC pc) code (p2 * m0_REG RName_PC pc') ==>
    (Aligned (pc,2) ==> Aligned (pc',2)) ==>
    TEMPORAL_NEXT m (p1 * m0_PC pc) code (p2 * m0_PC pc')`,
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss
        [m0_PC_def, temporal_stateTheory.TEMPORAL_NEXT_MOVE_COND,
         STAR_ASSOC, SEP_CLAUSES]
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
