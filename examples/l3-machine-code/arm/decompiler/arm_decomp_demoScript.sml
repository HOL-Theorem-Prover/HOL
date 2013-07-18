
open HolKernel Parse boolLib bossLib;

val _ = new_theory "arm_decomp_demo";

val (PID_C_cert,PID_C_def) = arm_decompLib.l3_arm_decompile "PID_C" `
            (* ------ PID example ------- *)
  ed907a00  (*  vldr      s14, [r0]       *)
  edd16a00  (*  vldr      s13, [r1]       *)
  ee676a26  (*  vmul.f32  s13, s14, s13   *)
  e3001000  (*  movw      r1, #0          *)
  e3401000  (*  movt      r1, #0          *)
  edd15a00  (*  vldr      s11, [r1]       *)
  ed936a00  (*  vldr      s12, [r3]       *)
  ed925a00  (*  vldr      s10, [r2]       *)
  edd17a01  (*  vldr      s15, [r1, #4]   *)
  e59d3000  (*  ldr       r3, [sp]        *)
  ed817a00  (*  vstr      s14, [r1]       *)
  ee775a65  (*  vsub.f32  s11, s14, s11   *)
  ee477a05  (*  vmla.f32  s15, s14, s10   *)
  ee456a86  (*  vmla.f32  s13, s11, s12   *)
  edc17a01  (*  vstr      s15, [r1, #4]   *)
  ee767aa7  (*  vadd.f32  s15, s13, s15   *)
  edc37a00  (*  vstr      s15, [r3]       *)`;

val _ = save_thm("PID_C_cert",PID_C_cert);

val (PID_ADA_cert,PID_ADA_def) = arm_decompLib.l3_arm_decompile "PID_ADA" `
  e3003000  (*  movw      r3, #0          *)
  e3403000  (*  movt      r3, #0          *)
  ed937a00  (*  vldr      s14, [r3]       *)
  edd37a03  (*  vldr      s15, [r3, #12]  *)
  ee676a27  (*  vmul.f32  s13, s14, s15   *)
  edd35a01  (*  vldr      s11, [r3, #4]   *)
  edd37a05  (*  vldr      s15, [r3, #20]  *)
  ed936a02  (*  vldr      s12, [r3, #8]   *)
  ed935a04  (*  vldr      s10, [r3, #16]  *)
  ed837a01  (*  vstr      s14, [r3, #4]   *)
  ee775a65  (*  vsub.f32  s11, s14, s11   *)
  ee477a05  (*  vmla.f32  s15, s14, s10   *)
  ee456a86  (*  vmla.f32  s13, s11, s12   *)
  edc37a05  (*  vstr      s15, [r3, #20]  *)
  ee767aa7  (*  vadd.f32  s15, s13, s15   *)
  edc37a06  (*  vstr      s15, [r3, #24]  *)`

val _ = save_thm("PID_ADA_cert",PID_ADA_cert);

(* an attempt at proving them equivalent *)

open wordsTheory;
open wordsLib;
val _ = (guessing_word_lengths := true);

val word_read_def = Define `
  word_read (m:word32 -> word8) a =
    (m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m (a))`;

val word_write_def = Define `
  word_write (m:word32 -> word8) (a:word32) (w:word32) =
           (a + 3w =+ (31 >< 24) w)
             ((a + 2w =+ (23 >< 16) w)
                ((a + 1w =+ (15 >< 8) w)
                   ((a =+ (7 >< 0) w) m)))`;

val put_upper_def = Define `
  ((put_upper (w:word32) (d:word64)):word64) =
     bit_field_insert 63 32 w d`;

val put_lower_def = Define `
  ((put_lower (w:word32) (d:word64)):word64) =
     bit_field_insert 31 0 w d`;

val get_upper_def = Define `
  ((get_upper (d:word64)):word32) = (63 >< 32) d`;

val get_lower_def = Define `
  ((get_lower (d:word64)):word32) = (31 >< 0) d`;

val word_write_lower = prove(
  ``((a + 3w =+ (31 >< 24) d7)
     ((a + 2w =+ (23 >< 16) d7)
      ((a + 1w =+ (15 >< 8) d7)
       ((a =+ (7 >< 0) d7) m)))) =
    (word_write m a (get_lower d7))``,
  SIMP_TAC std_ss [word_write_def,get_lower_def]
  THEN REPEAT (MATCH_MP_TAC
   (METIS_PROVE [] ``(x1 = x2) /\ (m1 = m2) ==> ((a =+ x1) m1 = (a =+ x2) m2)``)
  THEN REPEAT STRIP_TAC THEN SIMP_TAC std_ss [] THEN1 blastLib.BBLAST_TAC));

val word_write_upper = prove(
  ``((a + 3w =+ (63 >< 56) d7)
            ((a + 2w =+ (55 >< 48) d7)
               ((a + 1w =+ (47 >< 40) d7)
                  ((a =+ (39 >< 32) d7) m)))) =
    (word_write m a (get_upper d7))``,
  SIMP_TAC std_ss [word_write_def,get_upper_def]
  THEN REPEAT (MATCH_MP_TAC
   (METIS_PROVE [] ``(x1 = x2) /\ (m1 = m2) ==> ((a =+ x1) m1 = (a =+ x2) m2)``)
  THEN REPEAT STRIP_TAC THEN SIMP_TAC std_ss [] THEN1 blastLib.BBLAST_TAC));

val put_get_simp = prove(
  ``(put_upper w (put_upper w1 d) = put_upper w d) /\
    (get_upper (put_upper w d) = w) /\
    (get_upper (put_lower w1 d) = get_upper d) /\
    (put_lower w (put_lower w1 d) = put_lower w d) /\
    (get_lower (put_lower w d) = w) /\
    (get_lower (put_upper w1 d) = get_lower d) /\
    (put_upper w1 (put_lower w2 d) = put_lower w2 (put_upper w1 d))``,
  SIMP_TAC std_ss [put_lower_def,get_lower_def,put_upper_def,get_upper_def]
  THEN blastLib.BBLAST_TAC);

val lemma = EVAL ``bit_field_insert 31 16 (0w:word16) (0w:word32) : word32``

val PID_ADA_lemma =
  PID_ADA_def |> CONJUNCT1 |> SIMP_RULE std_ss [GSYM word_read_def,
    GSYM put_upper_def,GSYM put_lower_def,word_write_lower,word_write_upper,
    GSYM get_lower_def,GSYM get_upper_def,Once LET_DEF,lemma]
  |> SIMP_RULE std_ss [LET_DEF,put_get_simp,word_add_n2w]

val PID_C_lemma =
  PID_C_def |> CONJUNCT1 |> SIMP_RULE std_ss [GSYM word_read_def,
    GSYM put_upper_def,GSYM put_lower_def,word_write_lower,word_write_upper,
    GSYM get_lower_def,GSYM get_upper_def,Once LET_DEF,lemma]
  |> SIMP_RULE std_ss [LET_DEF,put_get_simp,word_add_n2w,lemma]

val PID_ADA_EQUIV_PID_C = store_thm("PID_ADA_EQUIV_PID_C",
  ``(word_read m2 r0 = word_read m1 0w) /\
    (word_read m2 0w = word_read m1 4w) /\
    (word_read m2 r3 = word_read m1 8w) /\
    (word_read m2 r2 = word_read m1 16w) ==>
    let (r3_a,d5_a,d6_a,d7_a,dm_a,m_a,rmode_a) =
            PID_ADA (d5,d6,d7,dm,m1,rmode) in
    let (r0_c,r1_c,r2_c,r3_c,r13_c,d5_c,d6_c,d7_c,dm_c,m_c,rmode_c) =
            PID_C (r0,r1,r2,r3,r13,d5,d6,d7,dm,m2,rmode) in
      (d7_a,rmode_a) = (d7_c,rmode_c)``,
  SIMP_TAC std_ss [PID_ADA_lemma,PID_C_lemma,LET_DEF]);

val _ = export_theory();
