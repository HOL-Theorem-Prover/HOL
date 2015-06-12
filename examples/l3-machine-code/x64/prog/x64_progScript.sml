open HolKernel boolLib bossLib
open lcsymtacs set_sepTheory progTheory pred_setTheory stateLib x64_stepTheory

val () = new_theory "x64_prog"

infix \\
val op \\ = op THEN;

(* ------------------------------------------------------------------------ *)

val _ = stateLib.sep_definitions "x64" [] [] x64_stepTheory.NextStateX64_def

val x64_mem_def = Define`
   x64_mem a (l: word8 list) =
   set (GENLIST (\i. (x64_c_MEM (a + n2w i),
                      x64_d_word8 (EL i l))) (LENGTH l))`

val x64_instr_def = Define`x64_instr (a, i) = x64_mem a i`

val x64_mem16_def = Define`
   x64_mem16 a (v: word16) = { x64_mem a [(7 >< 0) v; (15 >< 8) v] }`

val x64_mem32_def = Define`
   x64_mem32 a (v: word32) =
   { x64_mem a [(7 >< 0) v; (15 >< 8) v; (23 >< 16) v; (31 >< 24) v] }`

val v8 = ``[( 7 ><  0) v; (15 ><  8) v; (23 >< 16) v; (31 >< 24) (v:word64);
            (39 >< 32) v; (47 >< 40) v; (55 >< 48) v; (63 >< 56) v]:word8 list``

val x64_mem64_def = Define`
   x64_mem64 a (v: word64) = { x64_mem a ^v8 }`

val X64_MODEL_def = Define`
  X64_MODEL = (STATE x64_proj, NEXT_REL (=) NextStateX64, x64_instr,
               ($= :x64_state -> x64_state -> bool), K F : x64_state -> bool)`

val X64_IMP_SPEC = Theory.save_thm ("X64_IMP_SPEC",
   stateTheory.IMP_SPEC
   |> Q.ISPECL [`x64_proj`, `NextStateX64`, `x64_instr`]
   |> REWRITE_RULE [GSYM X64_MODEL_def]
   )

val X64_IMP_TEMPORAL = Theory.save_thm ("X64_IMP_TEMPORAL",
   temporal_stateTheory.IMP_TEMPORAL
   |> Q.ISPECL [`x64_proj`, `NextStateX64`, `x64_instr`,
                `(=) : x64_state -> x64_state -> bool`,
                `K F : x64_state -> bool`]
   |> REWRITE_RULE [GSYM X64_MODEL_def]
   )

(* ------------------------------------------------------------------------ *)

val x64_MEM_def = DB.definition "x64_MEM_def"

val (x64_BYTE_MEMORY_def, x64_BYTE_MEMORY_INSERT) =
   stateLib.define_map_component ("x64_BYTE_MEMORY", "bmem", x64_MEM_def)

val x64_MEMORY_def = Define`
  x64_MEMORY dmem mem =
  { BIGUNION { BIGUNION (x64_mem64 a (mem a)) | a IN dmem /\ (a && 7w = 0w)} }`

val x64_PC_def = Define `x64_PC pc = x64_RIP pc * x64_exception NoException`

val x64_ALL_EFLAGS_def = Define `
  x64_ALL_EFLAGS =
    ~(x64_EFLAGS Z_AF) *
    ~(x64_EFLAGS Z_CF) *
    ~(x64_EFLAGS Z_OF) *
    ~(x64_EFLAGS Z_PF) *
    ~(x64_EFLAGS Z_SF) *
    ~(x64_EFLAGS Z_ZF)`

(* ------------------------------------------------------------------------ *)

val thm =
   MATCH_MP
     (stateTheory.MAPPED_COMPONENT_INSERT
      |> Q.ISPECL
            [`\a:word64. a && 7w = 0w`, `8`, `\a i. x64_c_MEM (a + n2w i)`,
             `\v:word64 i.  x64_d_word8 (EL i ^v8)`, `x64_mem64`,
             `x64_MEMORY`]
      |> Conv.CONV_RULE (Conv.LAND_CONV (SIMP_CONV std_ss [])))
     (REWRITE_RULE [x64_mem_def, EVAL ``LENGTH [a; b; c; d; e; f; g; h]``]
         x64_mem64_def)

val lem1 = Q.prove(
   `!i. i < 8 ==> n2w i <+ (8w: word64)`,
   simp [wordsTheory.word_lo_n2w])

val lem2 =
   blastLib.BBLAST_PROVE
      ``(7w && a = 0w:word64) /\ (7w && b = 0w) /\ x <+ 8w /\ y <+ 8w ==>
        ((a + x = b + y) = (a = b) /\ (x = y))``

(* Need ``(\a. ..) c`` below for automation to work *)
val x64_MEMORY_INSERT = Q.store_thm("x64_MEMORY_INSERT",
   `!f df c d.
     c IN df /\ (\a. a && 7w = 0w) c ==>
     (x64_mem64 c d * x64_MEMORY (df DELETE c) f = x64_MEMORY df ((c =+ d) f))`,
   match_mp_tac thm
   \\ rw [x64_MEMORY_def]
   \\ `(i = j) = (n2w i = n2w j: word64)` by simp []
   \\ asm_rewrite_tac []
   \\ match_mp_tac lem2
   \\ simp [lem1]
   )

(* ------------------------------------------------------------------------ *)

val x64_mem64_APPEND = Q.prove(
   `x64_mem32 a v * x64_mem32 (a + 4w) ((63 >< 32) w) =
    x64_mem64 a ((((63 >< 32) w):word32) @@ v)`,
   SIMP_TAC std_ss [x64_mem64_def, x64_mem32_def]
   \\ SIMP_TAC std_ss [GSYM stateTheory.SEP_EQ_SINGLETON]
   \\ MATCH_MP_TAC stateTheory.SEP_EQ_STAR
   \\ SIMP_TAC std_ss [stateTheory.SEP_EQ_SINGLETON, BIGUNION_SING,
                       DISJOINT_DEF, EXTENSION]
   \\ SIMP_TAC (srw_ss())
         [PULL_EXISTS, combinTheory.APPLY_UPDATE_THM, x64_mem_def]
   \\ REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss []
   THEN1 (REPEAT STRIP_TAC
          \\ EQ_TAC
          \\ REPEAT STRIP_TAC
          \\ FULL_SIMP_TAC (srw_ss()) [addressTheory.WORD_EQ_ADD_CANCEL]
          \\ blastLib.BBLAST_TAC)
   \\ CCONTR_TAC
   \\ FULL_SIMP_TAC std_ss []
   \\ FULL_SIMP_TAC (srw_ss()) [addressTheory.WORD_EQ_ADD_CANCEL]
   )

val lemma = blastLib.BBLAST_PROVE
   ``(((63 >< 32) w):word32) @@ ((w2w w):word32) = (w:word64)``

val lemma2 = blastLib.BBLAST_PROVE
   ``((((63 :num) >< (32 :num))
        (((((63 :num) >< (32 :num)) (w:word64) :word32)
           @@ (v:word32)) :word64) :word32) =
     ((63 >< 32) w):word32) /\
     (w2w (((((63 >< 32) w):word32) @@ v):word64) = v)``

val tac =
   REPEAT STRIP_TAC
   \\ ONCE_REWRITE_TAC [GSYM lemma]
   \\ SIMP_TAC std_ss [GSYM x64_mem64_APPEND, STAR_ASSOC]
   \\ SIMP_TAC std_ss [lemma, lemma2]
   \\ METIS_TAC [SPEC_FRAME, temporal_stateTheory.TEMPORAL_NEXT_FRAME]

val x64_mem32_READ_EXTEND = Q.store_thm("x64_mem32_READ_EXTEND",
   `SPEC m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a (w2w w)) ==>
    SPEC m (p * x64_mem64 a w) c (q * x64_mem64 a w)`,
   tac)

val x64_mem32_WRITE_EXTEND = Q.store_thm("x64_mem32_WRITE_EXTEND",
   `SPEC m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a v) ==>
    SPEC m (p * x64_mem64 a w) c
           (q * x64_mem64 a ((((63 >< 32) w):word32) @@ v))`,
   tac)

val x64_mem32_TEMPORAL_READ_EXTEND = Q.store_thm
  ("x64_mem32_TEMPORAL_READ_EXTEND",
   `TEMPORAL_NEXT m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a (w2w w)) ==>
    TEMPORAL_NEXT m (p * x64_mem64 a w) c (q * x64_mem64 a w)`,
   tac)

val x64_mem32_TEMPORAL_WRITE_EXTEND = Q.store_thm
  ("x64_mem32_TEMPORAL_WRITE_EXTEND",
   `TEMPORAL_NEXT m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a v) ==>
    TEMPORAL_NEXT m (p * x64_mem64 a w) c
                    (q * x64_mem64 a ((((63 >< 32) w):word32) @@ v))`,
   tac)

(* ------------------------------------------------------------------------ *)

val () = export_theory()
