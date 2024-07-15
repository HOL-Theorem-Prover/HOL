(* ------------------------------------------------------------------------
   Support for x86 step evaluator
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib

open bitstringLib wordsLib blastLib
open x64Theory
open utilsLib

val _ = new_theory "x64_step"

(* ------------------------------------------------------------------------ *)

val () =
   (numLib.temp_prefer_num (); wordsLib.prefer_word ();
    wordsLib.guess_lengths (); ParseExtras.temp_loose_equality())

(* ------------------------------------------------------------------------ *)

val NextStateX64_def = Define`
   NextStateX64 s0 =
   let s1 = x64_next s0 in if s1.exception = NoException then SOME s1 else NONE`

val NextStateX64_0 = utilsLib.ustore_thm("NextStateX64_0",
  `(s.exception = NoException) ==>
   (x64_decode (x64_fetch s) = Zfull_inst (p, ast, SOME strm1)) /\
   (20 - LENGTH strm1 = len) /\
   (!s. Run ast s = f s) /\
   (f (s with RIP := s.RIP + n2w len) = s1) /\
   (s1.exception = s.exception) ==>
   (NextStateX64 s = SOME s1)`,
   lrw [NextStateX64_def, x64_next_def] \\ lrw [])

val NextStateX64 = utilsLib.ustore_thm("NextStateX64",
  `(s.exception = NoException) ==>
   (x64_decode (x64_fetch s) = Zfull_inst (p, ast, SOME strm1)) /\
   (20 - LENGTH strm1 = len) /\
   (!s. Run ast s = f x s) /\
   (f x (s with RIP := s.RIP + n2w len) = s1) /\
   (s1.exception = s.exception) ==>
   (NextStateX64 s = SOME s1)`,
   lrw [NextStateX64_def, x64_next_def] \\ lrw [])

(* ------------------------------------------------------------------------ *)

val read_mem16_def = Lib.with_flag (Feedback.emit_MESG, false) Define`
   read_mem16 (m: word64 -> word8) a = m (a + 1w) @@ m a`

val read_mem32_def = Lib.with_flag (Feedback.emit_MESG, false) Define`
   read_mem32 (m: word64 -> word8) a =
   m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a`

val read_mem64_def = Lib.with_flag (Feedback.emit_MESG, false) Define`
   read_mem64 (m: word64 -> word8) a =
   m (a + 7w) @@ m (a + 6w) @@ m (a + 5w) @@ m (a + 4w) @@
   m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a`

val read_mem128_def = Lib.with_flag (Feedback.emit_MESG, false) Define`
   read_mem128 (m: word64 -> word8) a =
   m (a + 15w) @@ m (a + 14w) @@ m (a + 13w) @@ m (a + 12w) @@
   m (a + 11w) @@ m (a + 10w) @@ m (a + 9w) @@ m (a + 8w) @@
   m (a + 7w) @@ m (a + 6w) @@ m (a + 5w) @@ m (a + 4w) @@
   m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a`

val write_mem16_def = Define`
   write_mem16 (m: word64 -> word8) a (v: word16) =
     (a + 1w =+ (15 >< 8) v)
        ((a =+ (7 >< 0) v) m)`;

val write_mem32_def = Define`
   write_mem32 (m: word64 -> word8) a (v: word32) =
     (a + 3w =+ (31 >< 24) v)
        ((a + 2w =+ (23 >< 16) v)
           ((a + 1w =+ (15 >< 8) v)
              ((a =+ (7 >< 0) v) m)))`;

val write_mem64_def = Define`
   write_mem64 (m: word64 -> word8) a (v: word64) =
     (a + 7w =+ (63 >< 56) v)
        ((a + 6w =+ (55 >< 48) v)
           ((a + 5w =+ (47 >< 40) v)
              ((a + 4w =+ (39 >< 32) v)
                 ((a + 3w =+ (31 >< 24) v)
                    ((a + 2w =+ (23 >< 16) v)
                       ((a + 1w =+ (15 >< 8) v)
                          ((a =+ (7 >< 0) v) m)))))))`;

val write_mem128_def = Define`
   write_mem128 (m: word64 -> word8) a (v: word128) =
     (a + 15w =+ (127 >< 120) v)
        ((a + 14w =+ (119 >< 112) v)
           ((a + 13w =+ (111 >< 104) v)
              ((a + 12w =+ (103 >< 96) v)
                 ((a + 11w =+ (95 >< 88) v)
                    ((a + 10w =+ (87 >< 80) v)
                       ((a + 9w =+ (79 >< 72) v)
                          ((a + 8w =+ (71 >< 64) v)
     ((a + 7w =+ (63 >< 56) v)
        ((a + 6w =+ (55 >< 48) v)
           ((a + 5w =+ (47 >< 40) v)
              ((a + 4w =+ (39 >< 32) v)
                 ((a + 3w =+ (31 >< 24) v)
                    ((a + 2w =+ (23 >< 16) v)
                       ((a + 1w =+ (15 >< 8) v)
                          ((a =+ (7 >< 0) v) m)))))))))))))))`;

val mem16_rwt = ustore_thm("mem16_rwt",
   `(read_mem16 s.MEM a = v) ==> (mem16 a s = v)`,
   simp [mem16_def, mem8_def, read_mem16_def]
   )

val mem32_rwt = ustore_thm("mem32_rwt",
   `(read_mem32 s.MEM a = v) ==> (mem32 a s = v)`,
   simp [mem32_def, mem16_def, mem8_def, read_mem32_def]
   \\ blastLib.BBLAST_TAC
   )

val mem64_rwt = ustore_thm("mem64_rwt",
   `(read_mem64 s.MEM a = v) ==> (mem64 a s = v)`,
   simp [mem64_def, mem32_def, mem16_def, mem8_def, read_mem64_def]
   \\ blastLib.BBLAST_TAC
   )

val mem128_rwt = ustore_thm("mem128_rwt",
   `(read_mem128 s.MEM a = v) ==> (mem128 a s = v)`,
   simp [mem128_def, mem64_def, mem32_def, mem16_def, mem8_def, read_mem128_def]
   \\ blastLib.BBLAST_TAC
   )

val write'mem16_rwt = ustore_thm("write'mem16_rwt",
   `(read_mem16 s.MEM a = wv) ==>
    (write'mem16 (d, a) s = s with MEM := write_mem16 s.MEM a d)`,
   simp [combinTheory.APPLY_UPDATE_THM,
         blastLib.BBLAST_PROVE ``a <> a + 1w: word64``,
         write'mem16_def, write'mem8_def, write_mem16_def, read_mem16_def]
   )

val write'mem32_rwt = ustore_thm("write'mem32_rwt",
   `(read_mem32 s.MEM a = wv) ==>
    (write'mem32 (d, a) s = s with MEM := write_mem32 s.MEM a d)`,
   simp [combinTheory.APPLY_UPDATE_THM,
         blastLib.BBLAST_PROVE ``a <> a + 1w: word64``,
         blastLib.BBLAST_PROVE ``a <> a + 2w: word64``,
         blastLib.BBLAST_PROVE ``a <> a + 3w: word64``,
         write'mem32_def, write'mem16_def, write'mem8_def,
         write_mem32_def, read_mem32_def]
   \\ srw_tac [wordsLib.WORD_EXTRACT_ss] []
   )

val write'mem64_rwt = ustore_thm("write'mem64_rwt",
   `(read_mem64 s.MEM a = wv) ==>
    (write'mem64 (d, a) s = s with MEM := write_mem64 s.MEM a d)`,
   simp [write'mem64_def, write'mem32_def, write'mem16_def,
         write_mem64_def, read_mem64_def]
   \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
   \\ ASM_REWRITE_TAC [optionTheory.NOT_NONE_SOME, optionTheory.option_case_def]
   \\ simp [combinTheory.APPLY_UPDATE_THM,
            blastLib.BBLAST_PROVE ``a <> a + 1w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 2w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 3w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 4w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 5w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 6w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 7w: word64``,
            write'mem8_def]
   )

val write'mem128_rwt = ustore_thm("write'mem128_rwt",
   `(read_mem128 s.MEM a = wv) ==>
    (write'mem128 (d, a) s = s with MEM := write_mem128 s.MEM a d)`,
   simp [write'mem128_def, write'mem64_def, write'mem32_def, write'mem16_def,
         write_mem128_def, read_mem128_def]
   \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
   \\ ASM_REWRITE_TAC [optionTheory.NOT_NONE_SOME, optionTheory.option_case_def]
   \\ simp [combinTheory.APPLY_UPDATE_THM,
            blastLib.BBLAST_PROVE ``a <> a + 1w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 2w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 3w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 4w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 5w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 6w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 7w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 8w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 9w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 10w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 11w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 12w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 13w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 14w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 15w: word64``,
            write'mem8_def]
   )

val read_mem16 = Q.store_thm("read_mem16",
   `!m a v. (read_mem16 m a = v) =
            (m a = (7 >< 0) v) /\ (m (a + 1w) = (15 ><  8) v)`,
   REPEAT strip_tac
   \\ simp [read_mem16_def]
   \\ blastLib.BBLAST_TAC
   )

val read_mem32 = Q.store_thm("read_mem32",
   `!m a v.
      (read_mem32 m a = v) =
      (m a = (7 >< 0) v) /\
      (m (a + 1w) = (15 ><  8) v) /\
      (m (a + 2w) = (23 >< 16) v) /\
      (m (a + 3w) = (31 >< 24) v)`,
   REPEAT strip_tac
   \\ simp [read_mem32_def]
   \\ blastLib.BBLAST_TAC
   )

val read_mem64 = Q.store_thm("read_mem64",
   `!m a v.
      (read_mem64 m a = v) =
      (m a = (7 >< 0) v) /\
      (m (a + 1w) = (15 ><  8) v) /\
      (m (a + 2w) = (23 >< 16) v) /\
      (m (a + 3w) = (31 >< 24) v) /\
      (m (a + 4w) = (39 >< 32) v) /\
      (m (a + 5w) = (47 >< 40) v) /\
      (m (a + 6w) = (55 >< 48) v) /\
      (m (a + 7w) = (63 >< 56) v)`,
   REPEAT strip_tac
   \\ simp [read_mem64_def]
   \\ blastLib.BBLAST_TAC
   )

val read_mem128 = Q.store_thm("read_mem128",
   `!m a v.
      (read_mem128 m a = v) =
      (m a = (7 >< 0) v) /\
      (m (a + 1w) = (15 ><  8) v) /\
      (m (a + 2w) = (23 >< 16) v) /\
      (m (a + 3w) = (31 >< 24) v) /\
      (m (a + 4w) = (39 >< 32) v) /\
      (m (a + 5w) = (47 >< 40) v) /\
      (m (a + 6w) = (55 >< 48) v) /\
      (m (a + 7w) = (63 >< 56) v) /\
      (m (a + 8w) = (71 >< 64) v) /\
      (m (a + 9w) = (79 >< 72) v) /\
      (m (a + 10w) = (87 >< 80) v) /\
      (m (a + 11w) = (95 >< 88) v) /\
      (m (a + 12w) = (103 >< 96) v) /\
      (m (a + 13w) = (111 >< 104) v) /\
      (m (a + 14w) = (119 >< 112) v) /\
      (m (a + 15w) = (127 >< 120) v)`,
   REPEAT strip_tac
   \\ simp [read_mem128_def]
   \\ blastLib.BBLAST_TAC
   )

(* ------------------------------------------------------------------------ *)

val OpSize_rwt = Q.store_thm("OpSize_rwt",
   `(!have_rex w override. OpSize (have_rex, w, 0w, override) = Z8 have_rex) /\
    (!have_rex override. OpSize (have_rex, T, 1w, override) = Z64) /\
    (!have_rex. OpSize (have_rex, F, 1w, T) = Z16) /\
    (!have_rex. OpSize (have_rex, F, 1w, F) = Z32)`,
   rw [OpSize_def])

val MOD256 =
   bitTheory.MOD_2EXP_def
   |> Q.SPEC `8`
   |> numLib.REDUCE_RULE
   |> GSYM

fun to_n2w l =
   Drule.GEN_ALL o SIMP_RULE (srw_ss()) [MOD256, wordsTheory.word_lo_n2w] o
   Q.SPECL l

val n2w_w2n_lem = Q.prove(
   `!b: word8. n2w (w2n b) = w2w b`,
   lrw [wordsTheory.w2w_def])

val immediate8_rwt = to_n2w [`n2w n`] (Q.prove(
   `!b1 l.
       immediate8 (b1 :: l) =
       (if b1 <+ 128w then
           n2w (w2n b1)
        else
           n2w (2 ** 64 - 2 ** 8 + w2n b1), SOME l)`,
   simp [GSYM wordsTheory.word_add_n2w, n2w_w2n_lem]
   \\ rw [immediate8_def, oimmediate8_def]
   \\ blastLib.FULL_BBLAST_TAC
   )) |> utilsLib.save_as "immediate8_rwt";

val immediate8 = Q.store_thm("immediate8",
   `!imm:word8 l. immediate8 (I imm :: l) = (sw2sw imm, SOME l)`,
   srw_tac [] [immediate8_def, oimmediate8_def]
   )

val immediate16_rwt = to_n2w [`n2w n2`, `n2w n1`] (Q.prove(
   `!b2 b1 l.
       immediate16 (b2 :: b1 :: l) =
       (if b1 <+ 128w then
           n2w (w2n b1 * 2 ** 8 + w2n b2)
        else
           n2w (2 ** 64 - 2 ** 16 + w2n b1 * 2 ** 8 + w2n b2), SOME l)`,
   simp [GSYM wordsTheory.word_add_n2w, n2w_w2n_lem,
         GSYM wordsTheory.word_mul_n2w]
   \\ rw [immediate16_def]
   \\ blastLib.FULL_BBLAST_TAC
   )) |> utilsLib.save_as "immediate16_rwt";

val immediate16 = Q.store_thm("immediate16",
   `!imm:word16 l.
       immediate16 ((7 >< 0) imm :: (15 >< 8) imm :: l) = (sw2sw imm, SOME l)`,
   srw_tac [wordsLib.WORD_EXTRACT_ss] [immediate16_def]
   )

val immediate32_rwt = to_n2w [`n2w n4`, `n2w n3`, `n2w n2`, `n2w n1`] (Q.prove(
   `!b4 b3 b2 b1 l.
       immediate32 (b4 :: b3 :: b2 :: b1 :: l) =
       (if b1 <+ 128w then
           n2w (w2n b1 * 2 ** 24 + w2n b2 * 2 ** 16 +
                w2n b3 * 2 ** 8 + w2n b4)
        else
           n2w (2 ** 64 - 2 ** 32 +
                w2n b1 * 2 ** 24 + w2n b2 * 2 ** 16 +
                w2n b3 * 2 ** 8 + w2n b4), SOME l)`,
   simp [GSYM wordsTheory.word_add_n2w, n2w_w2n_lem,
         GSYM wordsTheory.word_mul_n2w]
   \\ rw [immediate32_def]
   \\ blastLib.FULL_BBLAST_TAC
   )) |> utilsLib.save_as "immediate32_rwt";

val immediate32 = Q.store_thm("immediate32",
   `!imm:word32 l.
       immediate32
          ((7 >< 0) imm :: (15 >< 8) imm ::
           (23 >< 16) imm :: (31 >< 24) imm :: l) = (sw2sw imm, SOME l)`,
   srw_tac [wordsLib.WORD_EXTRACT_ss] [immediate32_def]
   )

val immediate64_rwt =
   to_n2w [`n2w n8`, `n2w n7`, `n2w n6`, `n2w n5`,
           `n2w n4`, `n2w n3`, `n2w n2`, `n2w n1`] (Q.prove(
   `!b8 b7 b6 b5 b4 b3 b2 b1 l.
       immediate64 (b8 :: b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: l) =
       (n2w (w2n b1 * 2 ** 56 + w2n b2 * 2 ** 48 +
             w2n b3 * 2 ** 40 + w2n b4 * 2 ** 32 +
             w2n b5 * 2 ** 24 + w2n b6 * 2 ** 16 +
             w2n b7 * 2 ** 8 + w2n b8), SOME l)`,
   rw [GSYM wordsTheory.word_add_n2w, n2w_w2n_lem,
       GSYM wordsTheory.word_mul_n2w, immediate64_def]
   \\ blastLib.FULL_BBLAST_TAC
   )) |> utilsLib.save_as "immediate64_rwt";

val immediate64 = Q.store_thm("immediate64",
   `!imm:word64 l.
       immediate64
          ((7 >< 0) imm :: (15 >< 8) imm ::
           (23 >< 16) imm :: (31 >< 24) imm ::
           (39 >< 32) imm :: (47 >< 40) imm ::
           (55 >< 48) imm :: (63 >< 56) imm :: l) = (imm, SOME l)`,
   srw_tac [wordsLib.WORD_EXTRACT_ss] [immediate64_def]
   )

(* ------------------------------------------------------------------------ *)

val rounding_mode_def = Define`
  rounding_mode rc =
  case rc : word2 of
    0w => roundTiesToEven
  | 1w => roundTowardNegative
  | 2w => roundTowardPositive
  | _ => roundTowardZero`

val rounding_mode = Q.store_thm ("rounding_mode",
  `!rc.
    (if rc = 0w then roundTiesToEven
     else if rc = 1w then roundTowardNegative
     else if rc = 2w then roundTowardPositive
     else if rc = 3w then roundTowardZero
     else ARB) = rounding_mode rc`,
  rw [rounding_mode_def]
  \\ blastLib.FULL_BBLAST_TAC)

val flush_to_zero32 = utilsLib.ustore_thm("flush_to_zero32",
   `~s.MXCSR.FZ ==> (flush_to_zero32 a s = a)`,
   Cases_on `a`
   \\ rw [flush_to_zero32_def])

val flush_to_zero64 = utilsLib.ustore_thm("flush_to_zero64",
   `~s.MXCSR.FZ ==> (flush_to_zero64 a s = a)`,
   Cases_on `a`
   \\ rw [flush_to_zero64_def])

val snd_with_flags = Q.store_thm("snd_with_flags",
  `(!a b c. SND (fp32_add_with_flags a b c) = fp32_add a b c) /\
   (!a b c. SND (fp64_add_with_flags a b c) = fp64_add a b c) /\
   (!a b c. SND (fp32_sub_with_flags a b c) = fp32_sub a b c) /\
   (!a b c. SND (fp64_sub_with_flags a b c) = fp64_sub a b c) /\
   (!a b c. SND (fp32_div_with_flags a b c) = fp32_div a b c) /\
   (!a b c. SND (fp64_div_with_flags a b c) = fp64_div a b c) /\
   (!a b c. SND (fp32_mul_with_flags a b c) = fp32_mul a b c) /\
   (!a b c. SND (fp64_mul_with_flags a b c) = fp64_mul a b c) /\
   (!a b. SND (fp32_sqrt_with_flags a b) = fp32_sqrt a b) /\
   (!a b. SND (fp64_sqrt_with_flags a b) = fp64_sqrt a b)`,
  rw [machine_ieeeTheory.fp32_add_with_flags_def,
      machine_ieeeTheory.fp32_add_def,
      machine_ieeeTheory.fp64_add_with_flags_def,
      machine_ieeeTheory.fp64_add_def,
      machine_ieeeTheory.fp32_sub_with_flags_def,
      machine_ieeeTheory.fp32_sub_def,
      machine_ieeeTheory.fp64_sub_with_flags_def,
      machine_ieeeTheory.fp64_sub_def,
      machine_ieeeTheory.fp32_div_with_flags_def,
      machine_ieeeTheory.fp32_div_def,
      machine_ieeeTheory.fp64_div_with_flags_def,
      machine_ieeeTheory.fp64_div_def,
      machine_ieeeTheory.fp32_mul_with_flags_def,
      machine_ieeeTheory.fp32_mul_def,
      machine_ieeeTheory.fp64_mul_with_flags_def,
      machine_ieeeTheory.fp64_mul_def,
      machine_ieeeTheory.fp32_sqrt_with_flags_def,
      machine_ieeeTheory.fp32_sqrt_def,
      machine_ieeeTheory.fp64_sqrt_with_flags_def,
      machine_ieeeTheory.fp64_sqrt_def]
  )

(* ------------------------------------------------------------------------ *)

val eflags_none = Q.store_thm("eflags_none",
   `!f. K NONE =
        (Z_CF =+ NONE)
          ((Z_PF =+ NONE)
             ((Z_AF =+ NONE)
                ((Z_ZF =+ NONE)
                   ((Z_SF =+ NONE)
                      ((Z_OF =+ NONE) f)))))`,
   STRIP_TAC
   \\ CONV_TAC (Conv.FUN_EQ_CONV)
   \\ Cases
   \\ srw_tac [] [combinTheory.APPLY_UPDATE_THM]
   )

(* ------------------------------------------------------------------------ *)

val id_state_cond = Q.store_thm("id_state_cond",
   `!b x y s.
      (if b then (x, s: x64_state) else (y, s)) = (if b then x else y, s)`,
   rw [])

val cond_thms = Q.store_thm("cond_thms",
   `(!b x. (if b then F else x) = ~b /\ x) /\
    (!b x. (if b then T else x) = b \/ x)`,
   rw [])

val bitfield_inserts = Q.store_thm("bitfield_inserts",
   `(!r: word64 d: word64.
       bit_field_insert 15 0 ((15 >< 0) d : word16) r =
       (r && 0xFFFFFFFFFFFF0000w) || (d && 0xFFFFw)) /\
    (!r: word64 d: word64.
       bit_field_insert 7 0 ((7 >< 0) d : word8) r =
       (r && 0xFFFFFFFFFFFFFF00w) || (d && 0xFFw)) /\
    (!r: word64 d: word64.
       bit_field_insert 15 8 ((7 >< 0) d : word8) r =
       (r && 0xFFFFFFFFFFFF00FFw) || ((d && 0xFFw) << 8))`,
   rw [wordsTheory.bit_field_insert_def]
   \\ blastLib.BBLAST_TAC)

(* ------------------------------------------------------------------------ *)

val extension_thms = Q.store_thm("extension_thms",
   `(!w: word8. (7 >< 0) (w2w w : word64) = w) /\
    (!w: word16. (15 >< 0) (w2w w : word64) = w) /\
    (!w: word32. (31 >< 0) (w2w w : word64) = w) /\
    (!w: word8.
       65535w && bit_field_insert 15 0 (sw2sw w : word16) (w2w w : word64) =
       65535w && w2w (sw2sw w : word16) : word64) /\
    (!w: word8.
      (31 >< 0) (bit_field_insert 31 0 (sw2sw w : word32) (w2w w : word64)) =
      w2w (sw2sw w : word32) : word64) /\
    (!w: word16.
      (31 >< 0) (bit_field_insert 31 0 (sw2sw w : word32) (w2w w : word64)) =
      w2w (sw2sw w : word32) : word64) /\
    (!w: word64.
      (31 >< 0) (bit_field_insert 31 0 (sw2sw (w2w w: word16) : word32)
                (w && 0xFFFFw)) =
      w2w (sw2sw (w2w w : word16) : word32) : word64)`,
   blastLib.BBLAST_TAC
)

val word_thms = Q.store_thm("word_thms",
   `(!a: word64.
       (31 >< 0) (a && 0xFFFFFFFFw) = w2w a : word32) /\
    (!a: word64.
       (15 >< 0) (a && 0xFFFFw) = w2w a : word16) /\
    (!a b: word64.
       (31 >< 0) (a && 0xFFFFFFFFw ?? b && 0xFFFFFFFFw) =
       (a ?? b) && 0xFFFFFFFFw) /\
    (!a b: word64.
       (w2w (a && 0xFFFFFFFFw ?? b && 0xFFFFFFFFw) = 0w: word32) =
       ((a ?? b) && 0xFFFFFFFFw = 0w)) /\
    (!a b: word64.
       (a && 0xFFFFFFFFw ?? b && 0xFFFFFFFFw) ' 31 =
       (a ' 31 <> b ' 31)) /\
    (!a b: word64.
       (7 >< 0) (a && 0xFFFFFFFFw ?? b && 0xFFFFFFFFw) : word8 =
       (7 >< 0) (a ?? b)) /\
    (!a b: word64.
       (31 >< 0) (a && 0xFFFFFFFFw || b && 0xFFFFFFFFw) =
       (a || b) && 0xFFFFFFFFw) /\
    (!a b: word64.
       (w2w (a && 0xFFFFFFFFw || b && 0xFFFFFFFFw) = 0w: word32) =
       ((a || b) && 0xFFFFFFFFw = 0w)) /\
    (!a b: word64.
       (a && 0xFFFFFFFFw || b && 0xFFFFFFFFw) ' 31 =
       (a ' 31 \/ b ' 31)) /\
    (!a b: word64.
       (7 >< 0) (a && 0xFFFFFFFFw || b && 0xFFFFFFFFw) : word8 =
       (7 >< 0) (a || b)) /\
    (!a b: word64.
       (31 >< 0) (a && 0xFFFFFFFFw && b && 0xFFFFFFFFw) =
       (a && b) && 0xFFFFFFFFw) /\
    (!a b: word64.
       (w2w (a && 0xFFFFFFFFw && b && 0xFFFFFFFFw) = 0w: word32) =
       ((a && b) && 0xFFFFFFFFw = 0w)) /\
    (!a b: word64.
       (a && 0xFFFFFFFFw && b && 0xFFFFFFFFw) ' 31 =
       (a ' 31 /\ b ' 31)) /\
    (!a b: word64.
       (7 >< 0) (a && 0xFFFFFFFFw && b && 0xFFFFFFFFw) : word8 =
       (7 >< 0) (a && b)) /\
    (!a: word64. (a && 0xFFFFFFFFw) ' 31 = a ' 31) /\
    (!a: word64. (7 >< 0) (a && 0xFFw) = (7 >< 0) a : word8) /\
    (!a: word64. (7 >< 0) (a && 0xFFFFw) = (7 >< 0) a : word8) /\
    (!a: word64. (7 >< 0) (a && 0xFFFFFFFFw) = (7 >< 0) a : word8) /\
    (!a: word64. (15 >< 0) (a && 0xFFFFw) = a && 0xFFFFw) /\
    (!a: word64. (31 >< 0) (a && 0xFFFFFFFFw) = a && 0xFFFFFFFFw) /\
    (!a: word64. (7 >< 0) (~(a && 0xFFw)) = ~a && 0xFFw) /\
    (!a: word64. (15 >< 0) (~(a && 0xFFFFw)) = ~a && 0xFFFFw) /\
    (!a: word64. (31 >< 0) (~(a && 0xFFFFFFFFw)) = ~a && 0xFFFFFFFFw) /\
    (!b. (7 >< 0) (v2w [b] : word64) = v2w [b] : word8) /\
    (!b. 255w && (v2w [b] : word64) = v2w [b] : word64) /\
    (!b. 0xFF00w && (v2w [b] : word64) << 8 = (v2w [b] << 8) : word64) /\
    (!a: word8. (7 >< 0) (w2w a : word64) = a) /\
    (!a: word16.
       sw2sw (((15 >< 0) (w2w a : word64)) : word16) = sw2sw a : word64) /\
    (!a: word32.
       sw2sw (((31 >< 0) (w2w a : word64)) : word32) = sw2sw a : word64) /\
    (!a: word8. (w2w a = 0w : word64) = (a = 0w)) /\
    (!a: word16. (w2w a = 0w : word64) = (a = 0w)) /\
    (!a: word32. (w2w a = 0w : word64) = (a = 0w)) /\
    (!a: word8. (sw2sw a = 0w : word64) = (a = 0w)) /\
    (!a: word16. (sw2sw a = 0w : word64) = (a = 0w)) /\
    (!a: word32. (sw2sw a = 0w : word64) = (a = 0w)) /\
    (!a: word128. w2w ((63 >< 0) a : word64) = (63 >< 0) a : word128) /\
    (!a: word64. w2w (w2w a : word32) = (31 >< 0) a : word128) /\
    (!a: word32. w2w ((31 >< 0) (w2w a : word64) : word32) =
                      (31 >< 0) a : word128) /\
    (!a: word128. (31 >< 0) (w2w ((31 >< 0) a : word32) : word64) =
                  (31 >< 0) a : word32) /\
    (!a: word128. (31 >< 0) (w2w ((31 >< 0) a : word32) : word64) =
                  (31 >< 0) a : word64) /\
    (!a: word32. (31 >< 0) (w2w a : word64) = w2w a : word64)
   `,
   rw [] \\ blastLib.BBLAST_TAC
   );

val lem32 = blastLib.BBLAST_PROVE ``!a: word64. a && 0xFFFFFFFFw = (31 >< 0) a``
val lem16 = blastLib.BBLAST_PROVE ``!a: word64. a && 0xFFFFw = (15 >< 0) a``
val lem8  = blastLib.BBLAST_PROVE ``!a: word64. a && 0xFFw = (7 >< 0) a``
fun mk_lem (x, y) =
   wordsTheory.WORD_EXTRACT_OVER_MUL2
   |> Thm.INST_TYPE [Type.alpha |-> ``:64``]
   |> Q.SPECL [x, `b`, y]
   |> SIMP_RULE (srw_ss()++wordsLib.WORD_EXTRACT_ss) []

val word_mul_thms = Q.store_thm("word_mul_thms",
   `(!a: word64 b: word32.
       (31 >< 0) ((a && 0xFFFFFFFFw) * w2w b) = (a * w2w b) && 0xFFFFFFFFw) /\
    (!a: word64 b: word16.
       (15 >< 0) ((a && 0xFFFFw) * w2w b) = (a * w2w b) && 0xFFFFw) /\
    (!a: word64 b: word8.
       (7 >< 0) ((a && 0xFFw) * w2w b) = (a * w2w b) && 0xFFw) /\
    (!a b: word64.
       (31 >< 0) ((a && 0xFFFFFFFFw) * (b && 0xFFFFFFFFw)) =
       (a * b) && 0xFFFFFFFFw) /\
    (!a b: word64.
       (15 >< 0) ((a && 0xFFFFw) * (b && 0xFFFFw)) = (a * b) && 0xFFFFw) /\
    (!a b: word64.
       (7 >< 0) ((a && 0xFFw) * (b && 0xFFw)) = (a * b) && 0xFFw)`,
   srw_tac [wordsLib.WORD_EXTRACT_ss]
      [lem8, lem16, lem32,
       mk_lem (`w2w (a: word8)`, `7`),
       mk_lem (`w2w (a: word16)`, `15`),
       mk_lem (`w2w (a: word32)`, `31`),
       wordsTheory.WORD_EXTRACT_OVER_MUL2])

local
   val bitwise_and_lt = Q.prove(
      `(!a. w2n (a && 0xFFw: word64) < 0x100) /\
       (!a. w2n (a && 0xFFFFw: word64) < 0x10000) /\
       (!a. w2n (a && 0xFFFFFFFFw: word64) < 0x100000000)`,
      REPEAT strip_tac
      \\ wordsLib.n2w_INTRO_TAC 64
      \\ blastLib.BBLAST_TAC)
   val bitwise_w2w_lt = Q.prove(
      `(!a: word8. w2n (w2w a: word64) < 0x100) /\
       (!a: word16. w2n (w2w a: word64) < 0x10000) /\
       (!a: word32. w2n (w2w a: word64) < 0x100000000)`,
      REPEAT strip_tac
      \\ wordsLib.n2w_INTRO_TAC 64
      \\ blastLib.BBLAST_TAC)
   val lt8 = DECIDE ``a < 0x10000n ==> a < 0x10000000000000000n``
   val lt16 = DECIDE ``a < 0x100000000n ==> a < 0x10000000000000000n``
   val lt32 = DECIDE ``a < 0x10000000000000000n ==> a < 0x10000000000000000n``
   val thms =
      ListPair.zip
        (ListPair.zip (Drule.CONJUNCTS bitwise_and_lt,
                       Drule.CONJUNCTS bitwise_w2w_lt), [lt8, lt16, lt32])
   val lo_thm = Q.prove(
      `x < y /\ y < 0x10000000000000000n ==> n2w x <+ (n2w y: word64)`,
      lrw [wordsTheory.word_lo_n2w])
   val mul_rule = Drule.GEN_ALL o REWRITE_RULE [GSYM wordsTheory.word_mul_def]
   fun mk_lt_thm t1 t2 =
      MATCH_MP bitTheory.LESS_MULT_MONO2
         (CONJ (Q.SPEC `a` t1) (Q.SPEC `b` t2))
          |> numLib.REDUCE_RULE
   val dummy_thm = combinTheory.I_THM
   fun div_thm n =
      let
         val s = case n of 0 => `8n` | 1 => `16n` | _ => `32n` : term frag list
         val ((thm, thm1), lt) = List.nth (thms, n)
         val lt_thm = mk_lt_thm thm thm
         val lt_thm1 = mk_lt_thm thm thm1
         val sz = eval ``(2n ** ^(Parse.Term s)) ** 2``
         val sz_lt =
            if n = 2 then dummy_thm
            else DECIDE ``^sz < 0x10000000000000000n``
         val lt_thm2 =
            if n = 2 then dummy_thm
            else mul_rule (Drule.MATCH_MP lo_thm (Thm.CONJ lt_thm sz_lt))
         val lt_thm3 =
            if n = 2 then dummy_thm
            else mul_rule (Drule.MATCH_MP lo_thm (Thm.CONJ lt_thm1 sz_lt))
         val dthm =
            wordsTheory.n2w_DIV
            |> Q.SPECL [`a`, s]
            |> Thm.INST_TYPE [Type.alpha |-> ``:64``]
            |> SIMP_RULE (srw_ss()) []
         fun mk_div_thm t = mul_rule (Drule.MATCH_MP dthm (Drule.MATCH_MP lt t))
      in
         [lt_thm2, lt_thm3, mk_div_thm lt_thm, mk_div_thm lt_thm1]
      end
   val shift_thm =
      Drule.LIST_CONJ
        [blastLib.BBLAST_PROVE
            ``(!a: word64. 0xFFw && (a >>> 8) = (a >>> 8) && 0xFFw) /\
              (!a: word64. 0xFFFFw && (a >>> 16) = (a >>> 16) && 0xFFFFw) /\
              (!a: word64. (31 >< 0) (a >>> 32) = a >>> 32)``,
         blastLib.BBLAST_PROVE
            ``(!a: word64. a <+ 0x10000w ==> ((a >>> 8) && 0xFFw = a >>> 8))``,
         blastLib.BBLAST_PROVE
            ``(!a: word64. a <+ 0x100000000w ==>
                           ((a >>> 16) && 0xFFFFw = a >>> 16))``]
in
   val word_mul_top = Q.store_thm("word_mul_top",
      `(!a: word64 b: word16.
          0xFFFFw &&
             (n2w
                (w2n (a && 0xFFFFw) * w2n (w2w b: word64) DIV 0x10000n)
                : word64) =
          ((a && 0xFFFFw) * w2w b) >>> 16) /\
       (!a: word64 b: word32.
          (31 >< 0)
             (n2w (w2n (a && 0xFFFFFFFFw) *
                   w2n (w2w b: word64) DIV 0x100000000n)
                : word64) =
          ((a && 0xFFFFFFFFw) * w2w b) >>> 32) /\
       (!a b: word64.
          0xFFFFw &&
             (n2w
                (w2n (a && 0xFFFFw) * w2n (b && 0xFFFFw) DIV 0x10000n)
                : word64) =
          ((a && 0xFFFFw) * (b && 0xFFFFw)) >>> 16) /\
       (!a b: word64.
          (31 >< 0)
             (n2w (w2n (a && 0xFFFFFFFFw) *
                   w2n (b && 0xFFFFFFFFw) DIV 0x100000000n)
                : word64) =
          ((a && 0xFFFFFFFFw) * (b && 0xFFFFFFFFw)) >>> 32)`,
      simp_tac std_ss (div_thm 1 @ div_thm 2 @ [shift_thm])
      )
end

(* ------------------------------------------------------------------------ *)

val prefixGroup = Q.store_thm("prefixGroup",
   `prefixGroup w =
       if w ' 7 then
          if w ' 6 /\ w ' 5 /\ w ' 4 /\ ~w ' 3 /\ ~w ' 2 then
             if ~w ' 1 /\ w ' 0 then 0 else 1
          else
             0
       else if w ' 6 then
          if w ' 5 then
             if ~w ' 4 /\ ~w ' 3 /\ w ' 2 then
                if w ' 1 then
                   if w ' 0 then 4 else 3
                else
                   2
             else
                0
          else if w ' 4 then 0 else 5
       else if w ' 5  /\ w ' 2 /\ w ' 1 /\ ~w ' 0 then
          2
       else
          0`,
   rewrite_tac [prefixGroup_def]
   \\ wordsLib.Cases_on_word_value `w`
   \\ EVAL_TAC)

val RexReg = Q.prove(
   `!r: word4. RexReg (r ' 3,v2w [r ' 2; r ' 1; r ' 0]) = num2Zreg (w2n r)`,
   rewrite_tac [x64Theory.RexReg_def]
   \\ wordsLib.Cases_word_value
   \\ EVAL_TAC
   )

val RexReg2 = Q.prove(
   `!r: word4. (2 >< 0) r = v2w [r ' 2; r ' 1; r ' 0]: word3`,
   wordsLib.Cases_word_value
   \\ EVAL_TAC
   )

val RegNot4_def = Define`
   RegNot4 (r: word4) = if (2 >< 0) r = (4w: word3) then 0w else r`

val RegNot4or5_def = Define`
   RegNot4or5 (r: word4) =
      if ((2 >< 0) r = (4w: word3)) \/ ((2 >< 0) r = (5w: word3)) then
         0w
      else
         r`

val RegNot = Q.prove(
   `(2 >< 0) (RegNot4 r) <> (4w: word3) /\
    (2 >< 0) (RegNot4or5 r) <> (4w: word3) /\
    (2 >< 0) (RegNot4or5 r) <> (5w: word3)`,
   rw [RegNot4_def, RegNot4or5_def]
   \\ fs []
   )

val tac =
   NTAC 2 strip_tac
   \\ wordsLib.Cases_on_word_value `(2 >< 0) r2: word3`
   \\ simp [x64Theory.readModRM_def, x64Theory.boolify8_def]
   \\ blastLib.BBLAST_TAC
   \\ simp [x64Theory.readDisplacement_def, RexReg]
   \\ blastLib.BBLAST_TAC
   \\ simp []
   \\ CONV_TAC (Conv.DEPTH_CONV bitstringLib.n2w_v2w_CONV)
   \\ rule_assum_tac (Conv.CONV_RULE (Conv.RHS_CONV bitstringLib.n2w_v2w_CONV))
   \\ pop_assum (SUBST1_TAC o SYM)
   \\ rw [RexReg2, RexReg]

val readModRM_byte_not_4 = Q.prove(
   `!r1: word4 r2:word4 b2 b1 X B rest.
      (2 >< 0) r2 <> (4w: word3) ==>
      (readModRM
          (REX b2 b1 X B,
           (1w: word2) @@ ((((2 >< 0) r1: word3) @@
                            ((2 >< 0) r2: word3)) : word6) :: rest) =
       let (displacement, strm2) = immediate8 rest in
          (if b1 = r1 ' 3 then num2Zreg (w2n r1) else RexReg (b1,(2 >< 0) r1),
           Zm (NONE, ZregBase (if b2 = r2 ' 3 then num2Zreg (w2n r2)
                               else RexReg (b2,(2 >< 0) r2)), displacement),
           strm2))`,
   tac
   )

val readModRM_dword_not_4 = Q.prove(
   `!r1: word4 r2:word4 b1 b2 X B rest.
      (2 >< 0) r2 <> (4w: word3) ==>
      (readModRM
          (REX b2 b1 X B,
           (2w: word2) @@ ((((2 >< 0) r1: word3) @@
                            ((2 >< 0) r2: word3)) : word6) :: rest) =
       let (displacement, strm2) = immediate32 rest in
          (if b1 = r1 ' 3 then num2Zreg (w2n r1) else RexReg (b1,(2 >< 0) r1),
           Zm (NONE, ZregBase (if b2 = r2 ' 3 then num2Zreg (w2n r2)
                               else RexReg (b2,(2 >< 0) r2)), displacement),
           strm2))`,
   tac
   )

val readModRM_not_4_or_5 = Q.prove(
   `!r1: word4 r2:word4 b1 b2 X B rest.
      (2 >< 0) r2 <> (4w: word3) /\ (2 >< 0) r2 <> (5w: word3) ==>
      (readModRM
          (REX b2 b1 X B,
           (0w: word2) @@ ((((2 >< 0) r1: word3) @@
                            ((2 >< 0) r2: word3)) : word6) :: rest) =
       (if b1 = r1 ' 3 then num2Zreg (w2n r1) else RexReg (b1,(2 >< 0) r1),
        Zm (NONE, ZregBase (if b2 = r2 ' 3 then num2Zreg (w2n r2)
                            else RexReg (b2,(2 >< 0) r2)), 0w), SOME rest))`,
   tac)

fun rule q = Drule.GEN_ALL o REWRITE_RULE [RegNot] o Q.SPECL [`r1`, q]

val readModRM_byte_not_4 = Theory.save_thm("readModRM_byte_not_4",
   rule `RegNot4 r2` readModRM_byte_not_4
   )

val readModRM_dword_not_4 = Theory.save_thm("readModRM_dword_not_4",
   rule `RegNot4 r2` readModRM_dword_not_4
   )

val readModRM_not_4_or_5 = Theory.save_thm("readModRM_not_4_or_5",
   rule `RegNot4or5 r2` readModRM_not_4_or_5
   )

val rbp = Q.store_thm("rbp",
   `!r b. (RexReg (b, r) = RBP) = ~b /\ (r = 5w)`,
   simp [x64Theory.RexReg_def]
   \\ wordsLib.Cases_word_value
   \\ Cases
   \\ CONV_TAC (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
   \\ simp [x64Theory.num2Zreg_thm]
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory ()
