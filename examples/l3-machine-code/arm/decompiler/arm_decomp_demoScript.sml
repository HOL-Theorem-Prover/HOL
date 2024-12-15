open HolKernel Parse boolLib bossLib;

open core_decompilerLib
open arm_core_decompLib

val () = new_theory "arm_decomp_demo";

(* the first PID exmaple *)

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

(* the second PID example *)

val (PID_C2_cert, PID_C2_def) = core_decompilerLib.core_decompile "PID_C2" `
                         (* ----------------------------------- *)
    e59f322c  00012f94   (* ldr        r3, [pc, #556]  ; 824c   *)
    e59f222c  00012f80   (* ldr        r2, [pc, #556]  ; 8250   *)
    edd37a00             (* vldr       s15, [r3]                *)
    ed927a00             (* vldr       s14, [r2]                *)
    e59f3224  00012e84   (* ldr        r3, [pc, #548]  ; 8254   *)
    e59f2224  00012f98   (* ldr        r2, [pc, #548]  ; 8258   *)
    edd25a00             (* vldr       s11, [r2]                *)
    e1d320f8             (* ldrsh      r2, [r3, #8]             *)
    e3520000             (* cmp        r2, #0                   *)
    e52d4004             (* push       {r4}            ; (str   *)
    edd36a00             (* vldr       s13, [r3]                *)
    ed936a01             (* vldr       s12, [r3, #4]            *)
    edc37a00             (* vstr       s15, [r3]                *)
    ee277a87             (* vmul.f32   s14, s15, s14            *)
    e1d320fa             (* ldrsh      r2, [r3, #10]            *)
    0a000061             (* beq        81e0 <main+0x1c8>        *)
    e3520000             (* cmp        r2, #0                   *)
    0a00000b             (* beq        8090 <main+0x78>         *)
    e59f11f4  00012f86   (* ldr        r1, [pc, #500]  ; 825c   *)
    e59f01f4  00012f8c   (* ldr        r0, [pc, #500]  ; 8260   *)
    e3a02000             (* mov        r2, #0                   *)
    e1c120b0             (* strh       r2, [r1]                 *)
    e1c020b0             (* strh       r2, [r0]                 *)
    e1c320ba             (* strh       r2, [r3, #10]            *)
    e1d320fc             (* ldrsh      r2, [r3, #12]            *)
    e3520000             (* cmp        r2, #0                   *)
    03a02001             (* moveq      r2, #1                   *)
    01c320bc             (* strheq     r2, [r3, #12]            *)
    01c120b0             (* strheq     r2, [r1]                 *)
    ea00005a             (* b  81fc <main+0x1e4>                *)
    eeb65a00             (* vmov.f32   s10, #96        ; 0x60   *)
    eef47ac5             (* vcmpe.f32  s15, s10                 *)
    eef1fa10             (* vmrs       APSR_nzcv, fpscr         *)
    e1d300fc             (* ldrsh      r0, [r3, #12]            *)
    83a01000             (* movhi      r1, #0                   *)
    93a01001             (* movls      r1, #1                   *)
    e3500000             (* cmp        r0, #0                   *)
    0a000018             (* beq        8114 <main+0xfc>         *)
    e59f01a4  00012f86   (* ldr        r0, [pc, #420]  ; 825c   *)
    e1d040f0             (* ldrsh      r4, [r0]                 *)
    e3540008             (* cmp        r4, #8                   *)
    e1d0c0b0             (* ldrh       ip, [r0]                 *)
    d3a02001             (* movle      r2, #1                   *)
    d1c320bc             (* strhle     r2, [r3, #12]            *)
    d08c3002             (* addle      r3, ip, r2               *)
    d1c030b0             (* strhle     r3, [r0]                 *)
    da000049             (* ble        81fc <main+0x1e4>        *)
    e3510000             (* cmp        r1, #0                   *)
    0a000007             (* beq        80fc <main+0xe4>         *)
    e1c020b0             (* strh       r2, [r0]                 *)
    e1c320bc             (* strh       r2, [r3, #12]            *)
    e1d320fe             (* ldrsh      r2, [r3, #14]            *)
    e3520000             (* cmp        r2, #0                   *)
    03a02001             (* moveq      r2, #1                   *)
    01c320be             (* strheq     r2, [r3, #14]            *)
    01c020b0             (* strheq     r2, [r0]                 *)
    ea00003f             (* b  81fc <main+0x1e4>                *)
    e3a02001             (* mov        r2, #1                   *)
    e1c310bc             (* strh       r1, [r3, #12]            *)
    e1c320ba             (* strh       r2, [r3, #10]            *)
    e59f3154  00012f84   (* ldr        r3, [pc, #340]  ; 8264   *)
    e1c310b0             (* strh       r1, [r3]                 *)
    ea000039             (* b  81fc <main+0x1e4>                *)
    e1d320fe             (* ldrsh      r2, [r3, #14]            *)
    e3520000             (* cmp        r2, #0                   *)
    0a00001a             (* beq        818c <main+0x174>        *)
    e59f2134  00012f86   (* ldr        r2, [pc, #308]  ; 825c   *)
    e1d240f0             (* ldrsh      r4, [r2]                 *)
    e3540008             (* cmp        r4, #8                   *)
    e1d2c0b0             (* ldrh       ip, [r2]                 *)
    d3a01001             (* movle      r1, #1                   *)
    d1c310be             (* strhle     r1, [r3, #14]            *)
    d08c3001             (* addle      r3, ip, r1               *)
    d1c230b0             (* strhle     r3, [r2]                 *)
    da00002d             (* ble        81fc <main+0x1e4>        *)
    e3510000             (* cmp        r1, #0                   *)
    1a000009             (* bne        8174 <main+0x15c>        *)
    e1d321f0             (* ldrsh      r2, [r3, #16]            *)
    e3520000             (* cmp        r2, #0                   *)
    e1c310be             (* strh       r1, [r3, #14]            *)
    1a000027             (* bne        81fc <main+0x1e4>        *)
    e3a02001             (* mov        r2, #1                   *)
    e1c321b0             (* strh       r2, [r3, #16]            *)
    e59f30f4  00012f8c   (* ldr        r3, [pc, #244]  ; 8260   *)
    e1d320b0             (* ldrh       r2, [r3]                 *)
    e2822001             (* add        r2, r2, #1               *)
    ea000020             (* b  81f8 <main+0x1e0>                *)
    e3a02001             (* mov        r2, #1                   *)
    e1c300be             (* strh       r0, [r3, #14]            *)
    e1c320ba             (* strh       r2, [r3, #10]            *)
    e59f30dc  00012f84   (* ldr        r3, [pc, #220]  ; 8264   *)
    e1c300b0             (* strh       r0, [r3]                 *)
    ea00001b             (* b  81fc <main+0x1e4>                *)
    e1d311f0             (* ldrsh      r1, [r3, #16]            *)
    e3510000             (* cmp        r1, #0                   *)
    0a00000b             (* beq        81c8 <main+0x1b0>        *)
    e59f10c0  00012f8c   (* ldr        r1, [pc, #192]  ; 8260   *)
    e1d110f0             (* ldrsh      r1, [r1]                 *)
    e3510ffa             (* cmp        r1, #1000       ; 0x3e8  *)
    e1c321b0             (* strh       r2, [r3, #16]            *)
    b3a02001             (* movlt      r2, #1                   *)
    b1c320bc             (* strhlt     r2, [r3, #12]            *)
    b59f30a4  00012f86   (* ldrlt      r3, [pc, #164]  ; 825c   *)
    ba00000f             (* blt        81f8 <main+0x1e0>        *)
    e1d321f2             (* ldrsh      r2, [r3, #18]            *)
    e3520000             (* cmp        r2, #0                   *)
    1a00000d             (* bne        81fc <main+0x1e4>        *)
    ea000002             (* b  81d4 <main+0x1bc>                *)
    e1d321f2             (* ldrsh      r2, [r3, #18]            *)
    e3520000             (* cmp        r2, #0                   *)
    0a000009             (* beq        81fc <main+0x1e4>        *)
    e3a02001             (* mov        r2, #1                   *)
    e1c321b2             (* strh       r2, [r3, #18]            *)
    ea000004             (* b  81f4 <main+0x1dc>                *)
    e3a01001             (* mov        r1, #1                   *)
    e3520000             (* cmp        r2, #0                   *)
    e1c310b8             (* strh       r1, [r3, #8]             *)
    1a000002             (* bne        81fc <main+0x1e4>        *)
    e1c310ba             (* strh       r1, [r3, #10]            *)
    e59f3068  00012f84   (* ldr        r3, [pc, #104]  ; 8264   *)
    e1c320b0             (* strh       r2, [r3]                 *)
    ee377a06             (* vadd.f32   s14, s14, s12            *)
    e59f305c  00012f84   (* ldr        r3, [pc, #92]   ; 8264   *)
    e59f205c  00012f7c   (* ldr        r2, [pc, #92]   ; 8268   *)
    e1d330b0             (* ldrh       r3, [r3]                 *)
    e1c230b0             (* strh       r3, [r2]                 *)
    e59f203c  00012e84   (* ldr        r2, [pc, #60]   ; 8254   *)
    ed827a01             (* vstr       s14, [r2, #4]            *)
    e59f204c  00012f90   (* ldr        r2, [pc, #76]   ; 826c   *)
    e3530000             (* cmp        r3, #0                   *)
    0e776ae6             (* vsubeq.f32 s13, s15, s13            *)
    ed926a00             (* vldr       s12, [r2]                *)
    0e677aa5             (* vmuleq.f32 s15, s15, s11            *)
    0e467a26             (* vmlaeq.f32 s15, s12, s13            *)
    1ddf7a04  42c7cccd   (* vldrne     s15, [pc, #16]  ; 8248   *)
    0e777a87             (* vaddeq.f32 s15, s15, s14            *)
    e59f3030  00012f88   (* ldr        r3, [pc, #48]   ; 8270   *)
    edc37a00             (* vstr       s15, [r3]                *)
    e8bd0010             (* pop        {r4}                     *)`;

val _ = save_thm("PID_C2_cert",PID_C2_cert);

val () = export_theory()
