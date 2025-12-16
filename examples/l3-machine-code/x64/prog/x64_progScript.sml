Theory x64_prog
Ancestors
  set_sep prog pred_set temporal_state x64_step
Libs
  numLib stateLib

val _ = ParseExtras.temp_loose_equality()
val _ = numLib.temp_prefer_num ();
(* ------------------------------------------------------------------------ *)

val _ = stateLib.sep_definitions "x64" [] [] x64_stepTheory.NextStateX64_def

Definition x64_mem_def:
   x64_mem a (l: word8 list) =
   set (GENLIST (\i. (x64_c_MEM (a + n2w i),
                      x64_d_word8 (EL i l))) (LENGTH l))
End

Definition x64_instr_def:  x64_instr (a, i) = x64_mem a i
End

Definition x64_mem16_def:
   x64_mem16 a (v: word16) = { x64_mem a [(7 >< 0) v; (15 >< 8) v] }
End

Definition x64_mem32_def:
   x64_mem32 a (v: word32) =
   { x64_mem a [(7 >< 0) v; (15 >< 8) v; (23 >< 16) v; (31 >< 24) v] }
End

val v8 = ``[( 7 ><  0) v; (15 ><  8) v; (23 >< 16) v; (31 >< 24) (v:word64);
            (39 >< 32) v; (47 >< 40) v; (55 >< 48) v; (63 >< 56) v]:word8 list``

val v16 =
  ``[(  7 ><  0) v; ( 15 ><   8) v; ( 23 ><  16) v; ( 31 ><  24) (v:word128);
     ( 39 >< 32) v; ( 47 ><  40) v; ( 55 ><  48) v; ( 63 ><  56) v;
     ( 71 >< 64) v; ( 79 ><  72) v; ( 87 ><  80) v; ( 95 ><  88) v;
     (103 >< 96) v; (111 >< 104) v; (119 >< 112) v; (127 >< 120) v]:word8 list``

Definition x64_mem64_def:   x64_mem64 a (v: word64) = { x64_mem a ^v8 }
End
Definition x64_mem128_def:   x64_mem128 a (v: word128) = { x64_mem a ^v16 }
End

Definition X64_MODEL_def:
  X64_MODEL = (STATE x64_proj, NEXT_REL (=) NextStateX64, x64_instr,
               ($= :x64_state -> x64_state -> bool), K F : x64_state -> bool)
End

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

Definition x64_MEMORY_def:
  x64_MEMORY dmem mem =
  { BIGUNION { BIGUNION (x64_mem64 a (mem a)) | a IN dmem /\ (a && 7w = 0w)} }
End

Definition x64_PC_def:   x64_PC pc = x64_RIP pc * x64_exception NoException
End

Definition x64_ALL_EFLAGS_def:
  x64_ALL_EFLAGS =
    ~(x64_EFLAGS Z_AF) *
    ~(x64_EFLAGS Z_CF) *
    ~(x64_EFLAGS Z_OF) *
    ~(x64_EFLAGS Z_PF) *
    ~(x64_EFLAGS Z_SF) *
    ~(x64_EFLAGS Z_ZF)
End

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
Theorem x64_MEMORY_INSERT:
    !f df c d.
     c IN df /\ (\a. a && 7w = 0w) c ==>
     (x64_mem64 c d * x64_MEMORY (df DELETE c) f = x64_MEMORY df ((c =+ d) f))
Proof
   match_mp_tac thm
   \\ rw [x64_MEMORY_def]
   \\ `(i = j) = (n2w i = n2w j: word64)` by simp []
   \\ asm_rewrite_tac []
   \\ match_mp_tac lem2
   \\ simp [lem1]
QED

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

Theorem x64_mem32_READ_EXTEND:
    SPEC m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a (w2w w)) ==>
    SPEC m (p * x64_mem64 a w) c (q * x64_mem64 a w)
Proof
   tac
QED

Theorem x64_mem32_WRITE_EXTEND:
    SPEC m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a v) ==>
    SPEC m (p * x64_mem64 a w) c
           (q * x64_mem64 a ((((63 >< 32) w):word32) @@ v))
Proof
   tac
QED

Theorem x64_mem32_TEMPORAL_READ_EXTEND:
    TEMPORAL_NEXT m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a (w2w w)) ==>
    TEMPORAL_NEXT m (p * x64_mem64 a w) c (q * x64_mem64 a w)
Proof
   tac
QED

Theorem x64_mem32_TEMPORAL_WRITE_EXTEND:
    TEMPORAL_NEXT m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a v) ==>
    TEMPORAL_NEXT m (p * x64_mem64 a w) c
                    (q * x64_mem64 a ((((63 >< 32) w):word32) @@ v))
Proof
   tac
QED

(* ------------------------------------------------------------------------ *)
