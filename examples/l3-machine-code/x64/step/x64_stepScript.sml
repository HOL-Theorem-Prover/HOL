(* ------------------------------------------------------------------------
   Support for x86 step evaluator
   ------------------------------------------------------------------------ *)
Theory x64_step
Ancestors
  x64
Libs
  bitstringLib wordsLib blastLib utilsLib updateLib

(* ------------------------------------------------------------------------ *)

val () =
   (numLib.temp_prefer_num (); wordsLib.prefer_word ();
    wordsLib.guess_lengths (); ParseExtras.temp_loose_equality())

(* ------------------------------------------------------------------------ *)

Definition NextStateX64_def:
   NextStateX64 s0 =
   let s1 = x64_next s0 in if s1.exception = NoException then SOME s1 else NONE
End

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

Definition read_mem16_def:
   read_mem16 (m: word64 -> word8) a = m (a + 1w) @@ m a
End

Definition read_mem32_def:
   read_mem32 (m: word64 -> word8) a =
   m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a
End

Definition read_mem64_def:
   read_mem64 (m: word64 -> word8) a =
   m (a + 7w) @@ m (a + 6w) @@ m (a + 5w) @@ m (a + 4w) @@
   m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a
End

Definition read_mem128_def:
   read_mem128 (m: word64 -> word8) a =
   m (a + 15w) @@ m (a + 14w) @@ m (a + 13w) @@ m (a + 12w) @@
   m (a + 11w) @@ m (a + 10w) @@ m (a + 9w) @@ m (a + 8w) @@
   m (a + 7w) @@ m (a + 6w) @@ m (a + 5w) @@ m (a + 4w) @@
   m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a
End

Definition write_mem16_def:
   write_mem16 (m: word64 -> word8) a (v: word16) =
     (a + 1w =+ (15 >< 8) v)
        ((a =+ (7 >< 0) v) m)
End

Definition write_mem32_def:
   write_mem32 (m: word64 -> word8) a (v: word32) =
     (a + 3w =+ (31 >< 24) v)
        ((a + 2w =+ (23 >< 16) v)
           ((a + 1w =+ (15 >< 8) v)
              ((a =+ (7 >< 0) v) m)))
End

Definition write_mem64_def:
   write_mem64 (m: word64 -> word8) a (v: word64) =
     (a + 7w =+ (63 >< 56) v)
        ((a + 6w =+ (55 >< 48) v)
           ((a + 5w =+ (47 >< 40) v)
              ((a + 4w =+ (39 >< 32) v)
                 ((a + 3w =+ (31 >< 24) v)
                    ((a + 2w =+ (23 >< 16) v)
                       ((a + 1w =+ (15 >< 8) v)
                          ((a =+ (7 >< 0) v) m)))))))
End

Definition write_mem128_def:
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
                          ((a =+ (7 >< 0) v) m)))))))))))))))
End

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

Theorem read_mem16:
    !m a v. (read_mem16 m a = v) =
            (m a = (7 >< 0) v) /\ (m (a + 1w) = (15 ><  8) v)
Proof
   REPEAT strip_tac
   \\ simp [read_mem16_def]
   \\ blastLib.BBLAST_TAC
QED

Theorem read_mem32:
    !m a v.
      (read_mem32 m a = v) =
      (m a = (7 >< 0) v) /\
      (m (a + 1w) = (15 ><  8) v) /\
      (m (a + 2w) = (23 >< 16) v) /\
      (m (a + 3w) = (31 >< 24) v)
Proof
   REPEAT strip_tac
   \\ simp [read_mem32_def]
   \\ blastLib.BBLAST_TAC
QED

Theorem read_mem64:
    !m a v.
      (read_mem64 m a = v) =
      (m a = (7 >< 0) v) /\
      (m (a + 1w) = (15 ><  8) v) /\
      (m (a + 2w) = (23 >< 16) v) /\
      (m (a + 3w) = (31 >< 24) v) /\
      (m (a + 4w) = (39 >< 32) v) /\
      (m (a + 5w) = (47 >< 40) v) /\
      (m (a + 6w) = (55 >< 48) v) /\
      (m (a + 7w) = (63 >< 56) v)
Proof
   REPEAT strip_tac
   \\ simp [read_mem64_def]
   \\ blastLib.BBLAST_TAC
QED

Theorem read_mem128:
    !m a v.
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
      (m (a + 15w) = (127 >< 120) v)
Proof
   REPEAT strip_tac
   \\ simp [read_mem128_def]
   \\ blastLib.BBLAST_TAC
QED

(* ------------------------------------------------------------------------ *)

Theorem OpSize_rwt:
    (!have_rex w override. OpSize (have_rex, w, 0w, override) = Z8 have_rex) /\
    (!have_rex override. OpSize (have_rex, T, 1w, override) = Z64) /\
    (!have_rex. OpSize (have_rex, F, 1w, T) = Z16) /\
    (!have_rex. OpSize (have_rex, F, 1w, F) = Z32)
Proof
   rw [OpSize_def]
QED

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

Theorem immediate8:
    !imm:word8 l. immediate8 (I imm :: l) = (sw2sw imm, SOME l)
Proof
   srw_tac [] [immediate8_def, oimmediate8_def]
QED

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

Theorem immediate16:
    !imm:word16 l.
       immediate16 ((7 >< 0) imm :: (15 >< 8) imm :: l) = (sw2sw imm, SOME l)
Proof
   srw_tac [wordsLib.WORD_EXTRACT_ss] [immediate16_def]
QED

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

Theorem immediate32:
    !imm:word32 l.
       immediate32
          ((7 >< 0) imm :: (15 >< 8) imm ::
           (23 >< 16) imm :: (31 >< 24) imm :: l) = (sw2sw imm, SOME l)
Proof
   srw_tac [wordsLib.WORD_EXTRACT_ss] [immediate32_def]
QED

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

Theorem immediate64:
    !imm:word64 l.
       immediate64
          ((7 >< 0) imm :: (15 >< 8) imm ::
           (23 >< 16) imm :: (31 >< 24) imm ::
           (39 >< 32) imm :: (47 >< 40) imm ::
           (55 >< 48) imm :: (63 >< 56) imm :: l) = (imm, SOME l)
Proof
   srw_tac [wordsLib.WORD_EXTRACT_ss] [immediate64_def]
QED

(* ------------------------------------------------------------------------ *)

Definition rounding_mode_def:
  rounding_mode rc =
  case rc : word2 of
    0w => roundTiesToEven
  | 1w => roundTowardNegative
  | 2w => roundTowardPositive
  | _ => roundTowardZero
End

Theorem rounding_mode:
   !rc.
    (if rc = 0w then roundTiesToEven
     else if rc = 1w then roundTowardNegative
     else if rc = 2w then roundTowardPositive
     else if rc = 3w then roundTowardZero
     else ARB) = rounding_mode rc
Proof
  rw [rounding_mode_def]
  \\ blastLib.FULL_BBLAST_TAC
QED

val flush_to_zero32 = utilsLib.ustore_thm("flush_to_zero32",
   `~s.MXCSR.FZ ==> (flush_to_zero32 a s = a)`,
   Cases_on `a`
   \\ rw [flush_to_zero32_def])

val flush_to_zero64 = utilsLib.ustore_thm("flush_to_zero64",
   `~s.MXCSR.FZ ==> (flush_to_zero64 a s = a)`,
   Cases_on `a`
   \\ rw [flush_to_zero64_def])

Theorem snd_with_flags:
   (!a b c. SND (fp32_add_with_flags a b c) = fp32_add a b c) /\
   (!a b c. SND (fp64_add_with_flags a b c) = fp64_add a b c) /\
   (!a b c. SND (fp32_sub_with_flags a b c) = fp32_sub a b c) /\
   (!a b c. SND (fp64_sub_with_flags a b c) = fp64_sub a b c) /\
   (!a b c. SND (fp32_div_with_flags a b c) = fp32_div a b c) /\
   (!a b c. SND (fp64_div_with_flags a b c) = fp64_div a b c) /\
   (!a b c. SND (fp32_mul_with_flags a b c) = fp32_mul a b c) /\
   (!a b c. SND (fp64_mul_with_flags a b c) = fp64_mul a b c) /\
   (!a b. SND (fp32_sqrt_with_flags a b) = fp32_sqrt a b) /\
   (!a b. SND (fp64_sqrt_with_flags a b) = fp64_sqrt a b)
Proof
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
QED

(* ------------------------------------------------------------------------ *)

Theorem eflags_none:
    !f. K NONE =
        (Z_CF =+ NONE)
          ((Z_PF =+ NONE)
             ((Z_AF =+ NONE)
                ((Z_ZF =+ NONE)
                   ((Z_SF =+ NONE)
                      ((Z_OF =+ NONE) f)))))
Proof
   STRIP_TAC
   \\ CONV_TAC (Conv.FUN_EQ_CONV)
   \\ Cases
   \\ srw_tac [] [combinTheory.APPLY_UPDATE_THM]
QED

(* ------------------------------------------------------------------------ *)

Theorem id_state_cond:
    !b x y s.
      (if b then (x, s: x64_state) else (y, s)) = (if b then x else y, s)
Proof
   rw []
QED

Theorem cond_thms:
    (!b x. (if b then F else x) = ~b /\ x) /\
    (!b x. (if b then T else x) = b \/ x)
Proof
   rw []
QED

Theorem bitfield_inserts:
    (!r: word64 d: word64.
       bit_field_insert 15 0 ((15 >< 0) d : word16) r =
       (r && 0xFFFFFFFFFFFF0000w) || (d && 0xFFFFw)) /\
    (!r: word64 d: word64.
       bit_field_insert 7 0 ((7 >< 0) d : word8) r =
       (r && 0xFFFFFFFFFFFFFF00w) || (d && 0xFFw)) /\
    (!r: word64 d: word64.
       bit_field_insert 15 8 ((7 >< 0) d : word8) r =
       (r && 0xFFFFFFFFFFFF00FFw) || ((d && 0xFFw) << 8))
Proof
   rw [wordsTheory.bit_field_insert_def]
   \\ blastLib.BBLAST_TAC
QED

(* ------------------------------------------------------------------------ *)

Theorem extension_thms:
    (!w: word8. (7 >< 0) (w2w w : word64) = w) /\
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
      w2w (sw2sw (w2w w : word16) : word32) : word64)
Proof
   blastLib.BBLAST_TAC
QED

Theorem word_thms:
    (!a: word64.
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
Proof
   rw [] \\ blastLib.BBLAST_TAC
QED

val lem32 = blastLib.BBLAST_PROVE ``!a: word64. a && 0xFFFFFFFFw = (31 >< 0) a``
val lem16 = blastLib.BBLAST_PROVE ``!a: word64. a && 0xFFFFw = (15 >< 0) a``
val lem8  = blastLib.BBLAST_PROVE ``!a: word64. a && 0xFFw = (7 >< 0) a``
fun mk_lem (x, y) =
   wordsTheory.WORD_EXTRACT_OVER_MUL2
   |> Thm.INST_TYPE [Type.alpha |-> ``:64``]
   |> Q.SPECL [x, `b`, y]
   |> SIMP_RULE (srw_ss()++wordsLib.WORD_EXTRACT_ss) []

Theorem word_mul_thms:
    (!a: word64 b: word32.
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
       (7 >< 0) ((a && 0xFFw) * (b && 0xFFw)) = (a * b) && 0xFFw)
Proof
   srw_tac [wordsLib.WORD_EXTRACT_ss]
      [lem8, lem16, lem32,
       mk_lem (`w2w (a: word8)`, `7`),
       mk_lem (`w2w (a: word16)`, `15`),
       mk_lem (`w2w (a: word32)`, `31`),
       wordsTheory.WORD_EXTRACT_OVER_MUL2]
QED

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
Theorem word_mul_top:
       (!a: word64 b: word16.
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
          ((a && 0xFFFFFFFFw) * (b && 0xFFFFFFFFw)) >>> 32)
Proof
      simp_tac std_ss (div_thm 1 @ div_thm 2 @ [shift_thm])
QED
end

(* ------------------------------------------------------------------------ *)

Theorem prefixGroup:
    prefixGroup w =
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
          0
Proof
   rewrite_tac [prefixGroup_def]
   \\ wordsLib.Cases_on_word_value `w`
   \\ EVAL_TAC
QED

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

Definition RegNot4_def:
   RegNot4 (r: word4) = if (2 >< 0) r = (4w: word3) then 0w else r
End

Definition RegNot4or5_def:
   RegNot4or5 (r: word4) =
      if ((2 >< 0) r = (4w: word3)) \/ ((2 >< 0) r = (5w: word3)) then
         0w
      else
         r
End

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

Theorem rbp:
    !r b. (RexReg (b, r) = RBP) = ~b /\ (r = 5w)
Proof
   simp [x64Theory.RexReg_def]
   \\ wordsLib.Cases_word_value
   \\ Cases
   \\ CONV_TAC (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
   \\ simp [x64Theory.num2Zreg_thm]
QED

(* ------------------------------------------------------------------------ *)

val st = ``s: x64_state``
fun mapl x = utilsLib.augment x [[]]

local
   val state_fns = utilsLib.accessor_fns ``: x64_state``
   val other_fns =
      [pairSyntax.fst_tm, pairSyntax.snd_tm,
       wordsSyntax.w2w_tm, wordsSyntax.sw2sw_tm,
       ``(h >< l) : 'a word -> 'b word``,
       ``bit_field_insert h l : 'a word -> 'b word -> 'b word``] @
      utilsLib.update_fns ``: x64_state`` @
      utilsLib.accessor_fns ``: MXCSR`` @
      utilsLib.accessor_fns ``: binary_ieee$flags`` @
      utilsLib.update_fns ``: binary_ieee$flags``
   val exc = ``SND (raise'exception e s : 'a # x64_state)``
in
Theorem cond_rand_thms = utilsLib.mk_cond_rand_thms (other_fns @ state_fns)
Theorem snd_exception_thms =
  utilsLib.map_conv
    (Drule.GEN_ALL o
    utilsLib.SRW_CONV [cond_rand_thms, x64Theory.raise'exception_def] o
    (fn tm => Term.mk_comb (tm, exc))) state_fns;
end

(* x64 datatype theorems/conversions *)

local
   fun datatype_thms thms =
      thms @ [cond_rand_thms, snd_exception_thms] @
      utilsLib.datatype_rewrites true "binary_ieee" ["flags"] @
      utilsLib.datatype_rewrites true "x64"
        ["x64_state", "Zreg", "Zeflags", "Zsize", "Zbase", "Zrm", "Zdest_src",
         "Zimm_rm", "Zmonop_name", "Zbinop_name", "Zbit_test_name", "Zcond",
         "Zea", "MXCSR", "xmm_mem", "sse_binop", "sse_logic", "sse_compare",
         "Zinst"]
in
   val DATATYPE_CONV = REWRITE_CONV (datatype_thms [])
   val COND_UPDATE_CONV =
      REWRITE_CONV (utilsLib.mk_cond_update_thms [``:x64_state``])
   val EV = utilsLib.STEP (datatype_thms, st)
   val resetEvConv = utilsLib.resetStepConv
   val setEvConv = utilsLib.setStepConv
end

(* ------------------------------------------------------------------------ *)

local
   val cnv = Conv.REWR_CONV x64Theory.readPrefix_def
             THENC REWRITE_CONV [prefixGroup_def]
             THENC EVAL
             THENC REWRITE_CONV [rec'REX_def]
             THENC EVAL
   fun mk_ibyte w = wordsSyntax.mk_wordii (w, 8)
   val prefix_rwt1 =
      utilsLib.map_conv cnv
         (List.tabulate (256, fn i => ``readPrefix (s, p, ^(mk_ibyte i)::l)``))
   val prefix_rwt2 =
      x64Theory.readPrefix_def
      |> Q.SPEC `h::t`
      |> SIMP_RULE (srw_ss()) []
      |> GEN_ALL
in
   val prefix_CONV =
      Conv.CHANGED_CONV (PURE_ONCE_REWRITE_CONV [prefix_rwt1])
      ORELSEC (Conv.REWR_CONV prefix_rwt2
               THENC Conv.RAND_CONV
                        (Conv.REWR_CONV prefixGroup
                         THENC Conv.DEPTH_CONV blastLib.BBLAST_CONV
                         THENC REWRITE_CONV [])
               THENC numLib.REDUCE_CONV
               THENC REWRITE_CONV [rec'REX_def]
               THENC Conv.DEPTH_CONV blastLib.BBLAST_CONV)
end

local
   fun mk_3 w = wordsSyntax.mk_wordii (w, 3)
   val boolify8_CONV =
      (Conv.REWR_CONV boolify8_n2w THENC numLib.REDUCE_CONV)
      ORELSEC (Conv.REWR_CONV boolify8_def
               THENC Conv.DEPTH_CONV blastLib.BBLAST_CONV)
   fun RexReg_rwt b =
      utilsLib.map_conv (REWRITE_CONV [RexReg_def]
                         THENC EVAL
                         THENC REWRITE_CONV [num2Zreg_thm])
         (List.tabulate (8, fn i => ``RexReg (^b, ^(mk_3 i))``))
   val cmp = computeLib.copy wordsLib.words_compset
   val cmp =
      utilsLib.add_theory
         ([immediate8_rwt, immediate16_rwt, immediate32_rwt, immediate64_rwt,
           immediate8, immediate16, immediate32, immediate64, immediate_def,
           OpSize_rwt, rbp, x64Theory.readModRM_def, readModRM_not_4_or_5,
           readModRM_byte_not_4, readModRM_dword_not_4,
           RexReg_rwt boolSyntax.F, RexReg_rwt boolSyntax.T],
          utilsLib.filter_inventory ["readPrefix"] (Import.gen_inventory{thyname="x64"})) cmp
   val cmp = utilsLib.add_base_datatypes cmp
   val cmp = computeLib.add_conv
               (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV) cmp
   val cmp = computeLib.add_conv (``boolify8``, 1, boolify8_CONV) cmp
   val cmp = computeLib.add_conv (``readPrefix``, 1, prefix_CONV) cmp
in
   val x64_CONV = utilsLib.CHANGE_CBV_CONV cmp
end

Theorem highByte =
  utilsLib.map_conv x64_CONV
    (List.map (fn r => ``num2Zreg (Zreg2num ^r - 4)``)
              [``RSP``, ``RBP``, ``RSI``, ``RDI``])

(* ------------------------------------------------------------------------ *)

Theorem mem8_rwt =
   EV [mem8_def] [[``^st.MEM a = v``]] []
      ``mem8 a``
      |> hd

Theorem write'mem8_rwt =
   EV [write'mem8_def] [] []
      ``write'mem8 (d, addr)``
      |> hd
      |> Drule.ADD_ASSUM ``^st.MEM addr = wv``

(* ------------------------------------------------------------------------ *)

val sizes = [``Z8 have_rex``, ``Z16``, ``Z32``, ``Z64``]

Theorem Cflag_rwt =
   EV [Eflag_def] [[``^st.EFLAGS Z_CF = SOME cflag``]] []
      ``Eflag Z_CF``
   |> hd

Theorem write'Eflag_rwt =
   EV [write'Eflag_def] [] []
      ``write'Eflag (b, flag)``
   |> hd

Theorem FlagUnspecified_rwt =
   EV [FlagUnspecified_def] [] []
      ``FlagUnspecified (flag)``
   |> hd

Theorem write_PF_rwt =
   EV [write_PF_def, write'PF_def, write'Eflag_rwt] [] []
      ``write_PF w``
   |> hd

val () = setEvConv (Conv.DEPTH_CONV (wordsLib.WORD_BIT_INDEX_CONV true))

val write_SF_rwt =
   EV [write_SF_def, write'SF_def, write'Eflag_rwt, word_size_msb_def,
       Zsize_width_def] []
      (mapl (`size`, sizes))
      ``write_SF (size, w)``
Theorem write_SF_rwts = LIST_CONJ write_SF_rwt

val write_ZF_rwt =
   EV [write_ZF_def, write'ZF_def, write'Eflag_rwt] [] (mapl (`size`, sizes))
      ``write_ZF (size, w)``
Theorem write_ZF_rwts = LIST_CONJ write_ZF_rwt

Theorem erase_eflags =
   erase_eflags_def
   |> Thm.SPEC st
   |> REWRITE_RULE [ISPEC ``^st.EFLAGS`` eflags_none]

(* ------------------------------------------------------------------------ *)

val mem_addr_rwt =
  EV [mem_addr_def, ea_index_def, ea_base_def, wordsTheory.WORD_ADD_0] []
     [[`m` |-> ``(NONE, ZnoBase, d)``],
      [`m` |-> ``(NONE, ZripBase, d)``],
      [`m` |-> ``(NONE, ZregBase r, d)``],
      [`m` |-> ``(SOME (scale, inx), ZnoBase, d)``],
      [`m` |-> ``(SOME (scale, inx), ZripBase, d)``],
      [`m` |-> ``(SOME (scale, inx), ZregBase r, d)``]]
     ``mem_addr m``
Theorem mem_addr_rwts = LIST_CONJ mem_addr_rwt

val ea_Zrm_rwt =
   EV ([ea_Zrm_def] @ mem_addr_rwt) []
      [[`rm` |-> ``Zr r``],
       [`rm` |-> ``Zm (NONE, ZnoBase, d)``],
       [`rm` |-> ``Zm (NONE, ZripBase, d)``],
       [`rm` |-> ``Zm (NONE, ZregBase r, d)``],
       [`rm` |-> ``Zm (SOME (scale, inx), ZnoBase, d)``],
       [`rm` |-> ``Zm (SOME (scale, inx), ZripBase, d)``],
       [`rm` |-> ``Zm (SOME (scale, inx), ZregBase r, d)``]]
      ``ea_Zrm (size, rm)``
Theorem ea_Zrm_rwts = LIST_CONJ ea_Zrm_rwt

val ea_Zdest_rwt =
   EV (ea_Zdest_def :: ea_Zrm_rwt) []
      [[`ds` |-> ``Zrm_i (Zr r, x)``],
       [`ds` |-> ``Zrm_i (Zm (NONE, ZnoBase, d), x)``],
       [`ds` |-> ``Zrm_i (Zm (NONE, ZripBase, d), x)``],
       [`ds` |-> ``Zrm_i (Zm (NONE, ZregBase r, d), x)``],
       [`ds` |-> ``Zrm_i (Zm (SOME (scale, inx), ZnoBase, d), x)``],
       [`ds` |-> ``Zrm_i (Zm (SOME (scale, inx), ZripBase, d), x)``],
       [`ds` |-> ``Zrm_i (Zm (SOME (scale, inx), ZregBase r, d), x)``],
       [`ds` |-> ``Zrm_r (Zr r, x)``],
       [`ds` |-> ``Zrm_r (Zm (NONE, ZnoBase, d), x)``],
       [`ds` |-> ``Zrm_r (Zm (NONE, ZripBase, d), x)``],
       [`ds` |-> ``Zrm_r (Zm (NONE, ZregBase r, d), x)``],
       [`ds` |-> ``Zrm_r (Zm (SOME (scale, inx), ZnoBase, d), x)``],
       [`ds` |-> ``Zrm_r (Zm (SOME (scale, inx), ZripBase, d), x)``],
       [`ds` |-> ``Zrm_r (Zm (SOME (scale, inx), ZregBase r, d), x)``],
       [`ds` |-> ``Zr_rm (r, x)``]]
      ``ea_Zdest (size, ds)``
Theorem ea_Zdest_rwts = LIST_CONJ ea_Zdest_rwt

val ea_Zsrc_rwt =
   EV (ea_Zsrc_def :: ea_Zrm_rwt) []
      [[`ds` |-> ``Zrm_i (x, i)``],
       [`ds` |-> ``Zrm_r (x, r)``],
       [`ds` |-> ``Zr_rm (x, Zr r)``],
       [`ds` |-> ``Zr_rm (x, Zm (NONE, ZnoBase, d))``],
       [`ds` |-> ``Zr_rm (x, Zm (NONE, ZripBase, d))``],
       [`ds` |-> ``Zr_rm (x, Zm (NONE, ZregBase r, d))``],
       [`ds` |-> ``Zr_rm (x, Zm (SOME (scale, inx), ZnoBase, d))``],
       [`ds` |-> ``Zr_rm (x, Zm (SOME (scale, inx), ZripBase, d))``],
       [`ds` |-> ``Zr_rm (x, Zm (SOME (scale, inx), ZregBase r, d))``]]
      ``ea_Zsrc (size, ds)``
Theorem ea_Zsrc_rwts = LIST_CONJ ea_Zsrc_rwt

val ea_Zimm_rm_rwt =
   EV (ea_Zimm_rm_def :: ea_Zrm_rwt) []
      [[`irm` |-> ``Zimm (i)``],
       [`irm` |-> ``Zrm (Zr r)``],
       [`irm` |-> ``Zrm (Zm (NONE, ZnoBase, d))``],
       [`irm` |-> ``Zrm (Zm (NONE, ZripBase, d))``],
       [`irm` |-> ``Zrm (Zm (NONE, ZregBase r, d))``],
       [`irm` |-> ``Zrm (Zm (SOME (scale, inx), ZnoBase, d))``],
       [`irm` |-> ``Zrm (Zm (SOME (scale, inx), ZripBase, d))``],
       [`irm` |-> ``Zrm (Zm (SOME (scale, inx), ZregBase r, d))``]]
      ``ea_Zimm_rm (irm)``
Theorem ea_Zimm_rm_rwts = LIST_CONJ ea_Zimm_rm_rwt

(* ------------------------------------------------------------------------ *)

val no_imm_ea =
   [[`ea` |-> ``Zea_r (Z8 have_rex, r)``],
    [`ea` |-> ``Zea_r (Z16, r)``],
    [`ea` |-> ``Zea_r (Z32, r)``],
    [`ea` |-> ``Zea_r (Z64, r)``],
    [`ea` |-> ``Zea_m (Z8 have_rex, a)``],
    [`ea` |-> ``Zea_m (Z16, a)``],
    [`ea` |-> ``Zea_m (Z32, a)``],
    [`ea` |-> ``Zea_m (Z64, a)``]] : cover

val ea =
   [[`ea` |-> ``Zea_i (Z8 have_rex, i)``],
    [`ea` |-> ``Zea_i (Z16, i)``],
    [`ea` |-> ``Zea_i (Z32, i)``],
    [`ea` |-> ``Zea_i (Z64, i)``]] @ no_imm_ea

val EA_rwt =
   EV [EA_def, restrictSize_def, id_state_cond, pred_setTheory.IN_INSERT,
       pred_setTheory.NOT_IN_EMPTY, mem8_rwt, mem16_rwt, mem32_rwt, mem64_rwt]
      [] ea
      ``EA ea``
Theorem EA_rwts = LIST_CONJ (map DISCH_ALL EA_rwt)

val write'EA_rwt =
   EV [write'EA_def, bitfield_inserts,
       pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY,
       write'mem8_rwt, write'mem16_rwt, write'mem32_rwt, write'mem64_rwt] []
      no_imm_ea
      ``write'EA (d, ea)``
   |> List.map (Conv.RIGHT_CONV_RULE
                  (utilsLib.EXTRACT_CONV THENC COND_UPDATE_CONV))
Theorem write'EA_rwts = LIST_CONJ (map DISCH_ALL write'EA_rwt)

val wv_to_v = List.map (Q.INST [`wv` |-> `v`])

val write'EA_rwt_r = wv_to_v write'EA_rwt
Theorem write'EA_rwt_rs = LIST_CONJ (map DISCH_ALL write'EA_rwt_r)

val xmm =
   [[`xmm` |-> ``xmm_reg x``],
    [`xmm` |-> ``xmm_mem (NONE, ZnoBase, d)``],
    [`xmm` |-> ``xmm_mem (NONE, ZripBase, d)``],
    [`xmm` |-> ``xmm_mem (NONE, ZregBase r, d)``],
    [`xmm` |-> ``xmm_mem (SOME (scale, inx), ZnoBase, d)``],
    [`xmm` |-> ``xmm_mem (SOME (scale, inx), ZripBase, d)``],
    [`xmm` |-> ``xmm_mem (SOME (scale, inx), ZregBase r, d)``]] : cover

val XMM_rwt =
  EV ([XMM_def, mem128_rwt] @ mem_addr_rwt) [] xmm
    ``XMM xmm``

val write'XMM_rwt = EV ([write'XMM_def, write'mem128_rwt] @ mem_addr_rwt) [] xmm
  ``write'XMM (d, xmm)``

(* ------------------------------------------------------------------------ *)

val write_arith_eflags_except_CF_OF_rwt =
   EV ([write_arith_eflags_except_CF_OF_def, FlagUnspecified_rwt,
        write_PF_rwt] @ write_SF_rwt @ write_ZF_rwt) [] (mapl (`size`, sizes))
      ``write_arith_eflags_except_CF_OF (size, w)``
Theorem write_arith_eflags_except_CF_OF_rwts =
  LIST_CONJ write_arith_eflags_except_CF_OF_rwt

val write_arith_eflags_rwt =
   EV ([write_arith_eflags_def, write'CF_def, write'OF_def, write'Eflag_rwt] @
       write_arith_eflags_except_CF_OF_rwt) [] (mapl (`size`, sizes))
      ``write_arith_eflags (size, r, carry, overflow)``
Theorem write_arith_eflags_rwts = LIST_CONJ write_arith_eflags_rwt

val write_logical_eflags_rwt =
   EV ([write_logical_eflags_def, write'CF_def, write'OF_def, write'Eflag_rwt] @
       write_arith_eflags_rwt) [] (mapl (`size`, sizes))
      ``write_logical_eflags (size, w)``
Theorem write_logical_eflags_rwts = LIST_CONJ write_logical_eflags_rwt

val () = setEvConv (Conv.DEPTH_CONV (wordsLib.WORD_BIT_INDEX_CONV true))

val ea_op =
   [[`size1` |-> ``Z8 have_rex``,  `ea` |-> ``Zea_r (Z8 have_rex, r)``],
    [`size1` |-> ``Z16``, `ea` |-> ``Zea_r (Z16, r)``],
    [`size1` |-> ``Z32``, `ea` |-> ``Zea_r (Z32, r)``],
    [`size1` |-> ``Z64``, `ea` |-> ``Zea_r (Z64, r)``],
    [`size1` |-> ``Z8 have_rex``,  `ea` |-> ``Zea_m (Z8 have_rex, a)``],
    [`size1` |-> ``Z16``, `ea` |-> ``Zea_m (Z16, a)``],
    [`size1` |-> ``Z32``, `ea` |-> ``Zea_m (Z32, a)``],
    [`size1` |-> ``Z64``, `ea` |-> ``Zea_m (Z64, a)``]] : cover

val monops = TypeBase.constructors_of ``:Zmonop_name``
val binops = Lib.op_set_diff aconv
                             (TypeBase.constructors_of ``:Zbinop_name``)
                             [``Zrcl``, ``Zrcr``]

val () = resetEvConv ()

val write_binop_rwt =
   EV ([write_binop_def, write_arith_result_def, write_logical_result_def,
        write_arith_result_no_CF_OF_def, write_result_erase_eflags_def,
        write_arith_eflags_except_CF_OF_def,
        add_with_carry_out_def, sub_with_borrow_def,
        maskShift_def, ROL_def, ROR_def, SAR_def, value_width_def,
        Zsize_width_def, word_size_msb_def,
        word_signed_overflow_add_def, word_signed_overflow_sub_def,
        erase_eflags, write_PF_rwt, write'CF_def, write'OF_def,
        write'Eflag_rwt, CF_def, Cflag_rwt, FlagUnspecified_def] @
       write_arith_eflags_rwt @ write_logical_eflags_rwt @ write_SF_rwt @
       write_ZF_rwt @ write'EA_rwt) []
      (utilsLib.augment (`bop`, binops) ea_op)
      ``write_binop (size1, bop, x, y, ea)``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE DATATYPE_CONV)
Theorem write_binop_rwts = LIST_CONJ (map DISCH_ALL write_binop_rwt)

val write_monop_rwt =
   EV ([write_monop_def,
        write_arith_result_no_CF_OF_def,
        write_arith_eflags_except_CF_OF_def,
        write_PF_rwt, write'CF_def, write'OF_def,
        write'Eflag_rwt, CF_def, FlagUnspecified_def] @
       write_SF_rwt @ write_ZF_rwt @ write'EA_rwt) []
      (utilsLib.augment (`mop`, monops) ea_op)
      ``write_monop (size1, mop, x, ea)``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE DATATYPE_CONV)
Theorem write_monop_rwts = LIST_CONJ (map DISCH_ALL write_monop_rwt)

(* ------------------------------------------------------------------------ *)

val () = resetEvConv ()

val conds = TypeBase.constructors_of ``:Zcond``

val read_cond_rwt =
   EV [read_cond_def, Eflag_def, CF_def, PF_def, AF_def, ZF_def, SF_def, OF_def,
       id_state_cond, cond_thms]
      [[``^st.EFLAGS (Z_CF) = SOME cflag``,
        ``^st.EFLAGS (Z_PF) = SOME pflag``,
        ``^st.EFLAGS (Z_AF) = SOME aflag``,
        ``^st.EFLAGS (Z_ZF) = SOME zflag``,
        ``^st.EFLAGS (Z_SF) = SOME sflag``,
        ``^st.EFLAGS (Z_OF) = SOME oflag``]]
      (mapl (`c`, conds))
      ``read_cond c``
Theorem read_cond_rwts = LIST_CONJ (map DISCH_ALL read_cond_rwt)

val SignExtension_rwt =
   EV [SignExtension_def] []
      [[`s1` |-> ``Z8 (b)``, `s2` |-> ``Z16``],
       [`s1` |-> ``Z8 (b)``, `s2` |-> ``Z32``],
       [`s1` |-> ``Z8 (b)``, `s2` |-> ``Z64``],
       [`s1` |-> ``Z16``, `s2` |-> ``Z32``],
       [`s1` |-> ``Z16``, `s2` |-> ``Z64``],
       [`s1` |-> ``Z32``, `s2` |-> ``Z64``]]
      ``SignExtension (w, s1, s2)``
Theorem SignExtension_rwts = LIST_CONJ SignExtension_rwt

val SignExtension64_rwt =
   EV (SignExtension64_def :: SignExtension_rwt) []
      [[`sz` |-> ``Z8 (b)``], [`sz` |-> ``Z16``],
       [`sz` |-> ``Z32``], [`sz` |-> ``Z64``]]
      ``SignExtension64 (w, sz)``
Theorem SignExtension64_rwts = LIST_CONJ SignExtension64_rwt

(* ------------------------------------------------------------------------ *)

val rm =
   [[`rm` |-> ``Zr r``],
    [`rm` |-> ``Zm (NONE, ZnoBase, d)``],
    [`rm` |-> ``Zm (NONE, ZripBase, d)``],
    [`rm` |-> ``Zm (NONE, ZregBase r, d)``],
    [`rm` |-> ``Zm (SOME (scale, ix), ZnoBase, d)``],
    [`rm` |-> ``Zm (SOME (scale, ix), ZripBase, d)``],
    [`rm` |-> ``Zm (SOME (scale, ix), ZregBase r, d)``]]: cover

val r_rm =
   [[`ds` |-> ``Zr_rm (r1, Zr r2)``],
    [`ds` |-> ``Zr_rm (r, Zm (NONE, ZnoBase, d))``],
    [`ds` |-> ``Zr_rm (r, Zm (NONE, ZripBase, d))``],
    [`ds` |-> ``Zr_rm (r1, Zm (NONE, ZregBase r2, d))``],
    [`ds` |-> ``Zr_rm (r, Zm (SOME (scale, ix), ZnoBase, d))``],
    [`ds` |-> ``Zr_rm (r, Zm (SOME (scale, ix), ZripBase, d))``],
    [`ds` |-> ``Zr_rm (r1, Zm (SOME (scale, ix), ZregBase r2, d))``]]
    : cover

val rm_i =
   [[`ds` |-> ``Zrm_i (Zr r, i)``],
    [`ds` |-> ``Zrm_i (Zm (NONE, ZnoBase, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (NONE, ZripBase, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (NONE, ZregBase r, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (SOME (scale, ix), ZnoBase, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (SOME (scale, ix), ZripBase, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (SOME (scale, ix), ZregBase r, d), i)``]]
    : cover

val rm_r =
   [[`ds` |-> ``Zrm_r (Zr r1, r2)``],
    [`ds` |-> ``Zrm_r (Zm (NONE, ZnoBase, d), r)``],
    [`ds` |-> ``Zrm_r (Zm (NONE, ZripBase, d), r)``],
    [`ds` |-> ``Zrm_r (Zm (NONE, ZregBase r1, d), r2)``],
    [`ds` |-> ``Zrm_r (Zm (SOME (scale, ix), ZnoBase, d), r)``],
    [`ds` |-> ``Zrm_r (Zm (SOME (scale, ix), ZripBase, d), r)``],
    [`ds` |-> ``Zrm_r (Zm (SOME (scale, ix), ZregBase r1, d), r2)``]]
    : cover

local
  val l = rm_i @ rm_r @ r_rm
  val aug_size = utilsLib.augment (`size`, sizes)
  val aug_size_not8 = utilsLib.augment (`size`, tl sizes)
in
  val src_dst = aug_size l
  val src_dst_not8 = aug_size_not8 l
  val src_dst_not8_or_r_rm = aug_size_not8 (rm_i @ rm_r)
  val lea = aug_size_not8 (tl r_rm)
  val rm_cases = aug_size rm
  val rm_cases_not8 = aug_size_not8 rm
end

val extends =
 (* 8 -> 16, 32, 64 *)
 utilsLib.augment (`size2`, tl sizes)
    (utilsLib.augment (`size`, [hd sizes]) r_rm) @
 (* 16 -> 32, 64 *)
 utilsLib.augment (`size2`, List.drop (sizes, 2))
    (utilsLib.augment (`size`, [List.nth(sizes, 1)]) r_rm) @
 (* 32 -> 64 *)
 utilsLib.augment (`size2`, List.drop (sizes, 3))
    (utilsLib.augment (`size`, [List.nth(sizes, 2)]) r_rm)

(* ------------------------------------------------------------------------ *)

(* TODO: CMPXCHG, XADD *)

val data_hyp_rule =
   List.map (utilsLib.ALL_HYP_CONV_RULE
                (INST_REWRITE_CONV EA_rwt THENC DATATYPE_CONV))

val flags_override_rule =
   List.map
    (CONV_RULE
       (Conv.DEPTH_CONV
         (OVERRIDE_UPDATES_CONV ``:Zeflags -> bool option``
           (SIMP_CONV (srw_ss()) []))))

val cond_update_rule = List.map (Conv.CONV_RULE COND_UPDATE_CONV)

local
  val state_with_pre = (st |-> ``^st with RIP := ^st.RIP + n2w len``)
in
  fun ADD_PRECOND_RULE thm =
    thm |> Thm.INST [state_with_pre]
        |> ALL_HYP_CONV_RULE DATATYPE_CONV
        |> Conv.CONV_RULE DATATYPE_CONV
end

(*
val is_some_hyp_rule =
   List.map
      (utilsLib.MATCH_HYP_CONV_RULE (REWRITE_CONV [optionTheory.IS_SOME_DEF])
          ``IS_SOME (x: 'a word option)`` o
       utilsLib.MATCH_HYP_RULE (ASM_REWRITE_RULE [])
          ``IS_SOME (x: 'a word option)``)
*)

val bit_test_rwt =
   EV ([bit_test_def, write'CF_def, Cflag_rwt, write'Eflag_rwt] @
       EA_rwt @ write'EA_rwt) []
      (utilsLib.augment
         (`bt`, [``Zbt``, ``Zbts``, ``Zbtr``, ``Zbtc``])
         (List.take (tl no_imm_ea, 4)))
     ``bit_test (bt, ea, offset)``
   |> data_hyp_rule
   |> wv_to_v

val Zbit_test_rwt =
   EV ([dfn'Zbit_test_def, modSize_def] @ SignExtension64_rwt @ bit_test_rwt @
       ea_Zrm_rwt @ EA_rwt @ write'EA_rwt @ ea_Zsrc_rwt @ ea_Zdest_rwt) []
      (utilsLib.augment
       (`bt`, [``Zbt``, ``Zbts``, ``Zbtr``, ``Zbtc``]) src_dst_not8_or_r_rm)
     ``dfn'Zbit_test (bt, size, ds)``
   |> data_hyp_rule
   |> map ADD_PRECOND_RULE
Theorem Zbit_test_rwts = LIST_CONJ (map DISCH_ALL Zbit_test_rwt)

(* val Znop_rwt = EV [dfn'Znop_def] [] [] ``dfn'Znop n`` *)

val Zcmc_rwt =
   EV [dfn'Zcmc_def, CF_def, write'CF_def, Cflag_rwt, write'Eflag_rwt] [] []
      ``dfn'Zcmc``
   |> map ADD_PRECOND_RULE
Theorem Zcmc_rwts = LIST_CONJ (map DISCH_ALL Zcmc_rwt)

val Zclc_rwt =
   EV [dfn'Zclc_def, CF_def, write'CF_def, write'Eflag_rwt] [] []
      ``dfn'Zclc``
   |> map ADD_PRECOND_RULE
Theorem Zclc_rwts = LIST_CONJ Zclc_rwt

val Zstc_rwt =
   EV [dfn'Zstc_def, CF_def, write'CF_def, write'Eflag_rwt] [] []
      ``dfn'Zstc``
   |> map ADD_PRECOND_RULE
Theorem Zstc_rwts = LIST_CONJ Zstc_rwt

val Zbinop_rwt =
   EV ([dfn'Zbinop_def, read_dest_src_ea_def] @
       ea_Zsrc_rwt @ ea_Zdest_rwt @ EA_rwt) [] src_dst
      ``dfn'Zbinop (bop, size, ds)``
   |> map ADD_PRECOND_RULE
Theorem Zbinop_rwts = LIST_CONJ (map DISCH_ALL Zbinop_rwt)

val Zcall_imm_rwt =
   EV ([dfn'Zcall_def, x64_push_rip_def, x64_push_aux_def, jump_to_ea_def,
        call_dest_from_ea_def, write'mem64_rwt] @ ea_Zimm_rm_rwt) [] []
      ``dfn'Zcall (Zimm imm)``
   |> data_hyp_rule
   |> map ADD_PRECOND_RULE
Theorem Zcall_imm_rwts = LIST_CONJ (map DISCH_ALL Zcall_imm_rwt)

val Zcall_rm_rwt =
   EV ([dfn'Zcall_def, x64_push_rip_def, x64_push_aux_def, jump_to_ea_def,
        call_dest_from_ea_def, write'mem64_rwt, mem64_rwt] @
       ea_Zimm_rm_rwt) [] rm
      ``dfn'Zcall (Zrm rm)``
   |> data_hyp_rule
   |> map ADD_PRECOND_RULE
Theorem Zcall_rm_rwts = LIST_CONJ (map DISCH_ALL Zcall_rm_rwt)

val Zjcc_rwt =
   EV ([dfn'Zjcc_def] @ read_cond_rwt) [] (mapl (`c`, conds))
      ``dfn'Zjcc (c, imm)``
   |> cond_update_rule
   |> map ADD_PRECOND_RULE
Theorem Zjcc_rwts = LIST_CONJ (map DISCH_ALL Zjcc_rwt)

val Zjmp_rwt =
   EV ([dfn'Zjmp_def] @ ea_Zrm_rwt @ EA_rwt) [] rm
      ``dfn'Zjmp rm``
   |> map ADD_PRECOND_RULE
Theorem Zjmp_rwts = LIST_CONJ (map DISCH_ALL Zjmp_rwt)

val Zlea_rwt =
   EV ([dfn'Zlea_def, get_ea_address_def] @
       ea_Zsrc_rwt @ ea_Zdest_rwt @ EA_rwt @ write'EA_rwt) [] lea
      ``dfn'Zlea (size, ds)``
   |> map ADD_PRECOND_RULE
Theorem Zlea_rwts = LIST_CONJ Zlea_rwt

val Zleave_rwt =
   EV ([dfn'Zleave_def, x64_pop_def, x64_pop_aux_def, mem64_rwt,
        combinTheory.UPDATE_EQ] @ ea_Zrm_rwt @ write'EA_rwt)
      [] []
      ``dfn'Zleave``
   |> map ADD_PRECOND_RULE
Theorem Zleave_rwts = LIST_CONJ (map DISCH_ALL Zleave_rwt)

val Zloop_rwt =
   EV ([dfn'Zloop_def] @ read_cond_rwt) []
      (mapl (`c`, [``Z_NE``, ``Z_E``, ``Z_ALWAYS``]))
      ``dfn'Zloop (c, imm)``
   |> data_hyp_rule
   |> cond_update_rule
   |> map ADD_PRECOND_RULE
Theorem Zloop_rwts = LIST_CONJ (map DISCH_ALL Zloop_rwt)

val Zmonop_rwt =
   EV ([dfn'Zmonop_def] @ ea_Zrm_rwt @ EA_rwt) [] rm_cases
      ``dfn'Zmonop (mop, size, rm)``
   |> map ADD_PRECOND_RULE
Theorem Zmonop_rwts = LIST_CONJ (map DISCH_ALL Zmonop_rwt)

val Zmov_rwt =
   EV ([dfn'Zmov_def] @
       ea_Zsrc_rwt @ ea_Zdest_rwt @ read_cond_rwt @ EA_rwt @ write'EA_rwt)
       [] (utilsLib.augment (`c`, Lib.butlast conds) src_dst_not8 @
           utilsLib.augment (`c`, [``Z_ALWAYS``]) src_dst)
      ``dfn'Zmov (c, size, ds)``
   (* |> is_some_hyp_rule *)
   |> cond_update_rule
   |> map ADD_PRECOND_RULE
Theorem Zmov_rwts = LIST_CONJ (map DISCH_ALL Zmov_rwt)

val Zmovzx_rwt =
   EV ([dfn'Zmovzx_def, cond_rand_thms, word_thms] @
      ea_Zsrc_rwt @ ea_Zdest_rwt @ EA_rwt @ write'EA_rwt)
       [] extends
      ``dfn'Zmovzx (size, ds, size2)``
   |> map ADD_PRECOND_RULE
Theorem Zmovzx_rwts = LIST_CONJ (map DISCH_ALL Zmovzx_rwt)

val Zmovsx_rwt =
   EV ([dfn'Zmovsx_def, cond_rand_thms, extension_thms, word_thms] @
       SignExtension_rwt @ ea_Zsrc_rwt @ ea_Zdest_rwt @ EA_rwt @ write'EA_rwt)
      [] extends
      ``dfn'Zmovsx (size, ds, size2)``
   |> map ADD_PRECOND_RULE
Theorem Zmovsx_rwts = LIST_CONJ (map DISCH_ALL Zmovsx_rwt)

val Zmul_rwt =
   EV ([dfn'Zmul_def, erase_eflags, value_width_def, Zsize_width_def,
        word_mul_thms, word_mul_top] @
       ea_Zrm_rwt @ EA_rwt @ write'EA_rwt) [] rm_cases
      ``dfn'Zmul (size, rm)``
   |> map ADD_PRECOND_RULE
Theorem Zmul_rwts = LIST_CONJ (map DISCH_ALL Zmul_rwt)

val Zimul_rwt =
   EV ([dfn'Zimul_def, erase_eflags, value_width_def, Zsize_width_def,
        write'CF_def, write'OF_def, write'Eflag_rwt, word_thms,
        integer_wordTheory.word_mul_i2w] @
       SignExtension64_rwt @ ea_Zrm_rwt @ EA_rwt @ write'EA_rwt) [] rm_cases
      ``dfn'Zimul (size, rm)``
   |> flags_override_rule
   |> map ADD_PRECOND_RULE
Theorem Zimul_rwts = LIST_CONJ (map DISCH_ALL Zimul_rwt)

val Zimul2_rwt =
   EV ([dfn'Zimul2_def, erase_eflags, value_width_def, Zsize_width_def,
        write'CF_def, write'OF_def, write'Eflag_rwt, word_thms,
        integer_wordTheory.word_mul_i2w] @ SignExtension64_rwt @ ea_Zrm_rwt @
       EA_rwt @ write'EA_rwt) [] rm_cases_not8
      ``dfn'Zimul2 (size, d, rm)``
   |> flags_override_rule
   |> map ADD_PRECOND_RULE
Theorem Zimul2_rwts = LIST_CONJ (map DISCH_ALL Zimul2_rwt)

val Zimul3_rwt =
   EV ([dfn'Zimul3_def, erase_eflags, value_width_def, Zsize_width_def,
        write'CF_def, write'OF_def, write'Eflag_rwt, word_thms,
        integer_wordTheory.word_mul_i2w] @ SignExtension64_rwt @ ea_Zrm_rwt @
       EA_rwt @ write'EA_rwt) [] rm_cases_not8
      ``dfn'Zimul3 (size, d, rm, imm)``
   |> flags_override_rule
   |> map ADD_PRECOND_RULE
Theorem Zimul3_rwts = LIST_CONJ (map DISCH_ALL Zimul3_rwt)

val Zpop_rwt =
   EV ([dfn'Zpop_def, x64_pop_def, x64_pop_aux_def, mem64_rwt] @
        ea_Zrm_rwt @ write'EA_rwt)
      [] rm
      ``dfn'Zpop rm``
   |> data_hyp_rule
   |> map ADD_PRECOND_RULE
Theorem Zpop_rwts = LIST_CONJ (map DISCH_ALL Zpop_rwt)

val Zpush_imm_rwt =
   EV ([dfn'Zpush_def, x64_push_def, x64_push_aux_def, write'mem64_rwt] @
       ea_Zimm_rm_rwt @ EA_rwt) [] []
      ``dfn'Zpush (Zimm imm)``
   |> data_hyp_rule
   |> map ADD_PRECOND_RULE
Theorem Zpush_imm_rwts = LIST_CONJ (map DISCH_ALL Zpush_imm_rwt)

val Zpush_rm_rwt =
   EV ([dfn'Zpush_def, x64_push_def, x64_push_aux_def, write'mem64_rwt] @
       ea_Zimm_rm_rwt @ EA_rwt) [] rm
      ``dfn'Zpush (Zrm rm)``
   |> data_hyp_rule
   |> map ADD_PRECOND_RULE
Theorem Zpush_rm_rwts = LIST_CONJ (map DISCH_ALL Zpush_rm_rwt)

val Zret_rwt =
   EV [dfn'Zret_def, x64_pop_rip_def, x64_pop_aux_def, x64_drop_def, mem64_rwt,
       combinTheory.UPDATE_EQ]
      [[``(7 >< 0) (imm: word64) = 0w: word8``]] []
      ``dfn'Zret imm``
   |> map ADD_PRECOND_RULE
Theorem Zret_rwts = LIST_CONJ (map DISCH_ALL Zret_rwt)

val Zset_rwt =
   EV ([dfn'Zset_def, word_thms] @
       read_cond_rwt @ ea_Zrm_rwt @ write'EA_rwt) []
      (utilsLib.augment (`c`, Lib.butlast conds) rm)
      ``dfn'Zset (c, have_rex, rm)``
   |> map ADD_PRECOND_RULE
Theorem Zset_rwts = LIST_CONJ (map DISCH_ALL Zset_rwt)

val Zxchg_rwt =
   EV ([dfn'Zxchg_def] @ ea_Zrm_rwt @ EA_rwt @ write'EA_rwt_r)
      [] rm_cases
      ``dfn'Zxchg (size, rm, r2)``
   |> data_hyp_rule
   (* |> is_some_hyp_rule *)
   |> map ADD_PRECOND_RULE
Theorem Zxchg_rwts = LIST_CONJ (map DISCH_ALL Zxchg_rwt)

val () = setEvConv (Conv.DEPTH_CONV wordsLib.SIZES_CONV)

val div_ev =
   EV ([dfn'Zdiv_def, dfn'Zidiv_def, erase_eflags, value_width_def,
        Zsize_width_def, word_thms, wordsTheory.w2n_w2w,
        utilsLib.map_conv EVAL
          [``256 / 2i``, ``65536 / 2i``, ``4294967296 / 2i``,
           ``18446744073709551616 / 2i``],
        wordsTheory.w2n_eq_0, integer_wordTheory.w2i_eq_0] @
       SignExtension64_rwt @ ea_Zrm_rwt @ EA_rwt @ write'EA_rwt)

fun avoid_error_rule th =
  let
    val ths = th |> rhsc
                 |> boolSyntax.dest_cond
                 |> #1
                 |> boolSyntax.strip_disj
                 |> List.map (Thm.ASSUME o boolSyntax.mk_neg)
  in
    REWRITE_RULE ths th
  end

val Zdiv_rwt =
  div_ev [] (tl rm_cases)
      ``dfn'Zdiv (size, rm)``
   |> List.map avoid_error_rule
   |> map ADD_PRECOND_RULE
Theorem Zdiv_rwts = LIST_CONJ (map DISCH_ALL Zdiv_rwt)

val Zidiv_rwt =
  div_ev [] (tl rm_cases)
      ``dfn'Zidiv (size, rm)``
   |> List.map avoid_error_rule
   |> map ADD_PRECOND_RULE
Theorem Zidiv_rwts = LIST_CONJ (map DISCH_ALL Zidiv_rwt)

val Zdiv_byte_reg_rwt_1 =
  div_ev [] [] ``dfn'Zdiv (Z8 T, Zr r)``
   |> List.map avoid_error_rule
   |> map ADD_PRECOND_RULE
Theorem Zdiv_byte_reg_rwts_1 = LIST_CONJ (map DISCH_ALL Zdiv_byte_reg_rwt_1)

val Zidiv_byte_reg_rwt_1 =
  div_ev [] [] ``dfn'Zidiv (Z8 T, Zr r)``
   |> List.map avoid_error_rule
   |> map ADD_PRECOND_RULE
Theorem Zidiv_byte_reg_rwts_1 = LIST_CONJ (map DISCH_ALL Zidiv_byte_reg_rwt_1)

val Zdiv_byte_reg_rwt_2 =
  div_ev []
   [[`r` |-> ``RAX``], [`r` |-> ``RCX``], [`r` |-> ``RDX``], [`r` |-> ``RBX``],
    [`r` |-> ``RSP``], [`r` |-> ``RBP``], [`r` |-> ``RSI``], [`r` |-> ``RDI``]]
      ``dfn'Zdiv (Z8 F, Zr r)``
   |> List.map avoid_error_rule
   |> map ADD_PRECOND_RULE
Theorem Zdiv_byte_reg_rwts_2 = LIST_CONJ (map DISCH_ALL Zdiv_byte_reg_rwt_2)

val Zidiv_byte_reg_rwt_2 =
  div_ev []
   [[`r` |-> ``RAX``], [`r` |-> ``RCX``], [`r` |-> ``RDX``], [`r` |-> ``RBX``],
    [`r` |-> ``RSP``], [`r` |-> ``RBP``], [`r` |-> ``RSI``], [`r` |-> ``RDI``]]
      ``dfn'Zidiv (Z8 F, Zr r)``
   |> List.map avoid_error_rule
   |> map ADD_PRECOND_RULE
Theorem Zidiv_byte_reg_rwts_2 = LIST_CONJ (map DISCH_ALL Zidiv_byte_reg_rwt_2)

(* ------------------------------------------------------------------------ *)

(* SSE *)

(* Assume:
   - all SSE exceptions are masked
   - don't flush to zero
   - denormals are not treated as zero
*)
val mxcsr =
  [``~^st.MXCSR.FZ``, ``^st.MXCSR.PM``, ``^st.MXCSR.UM``, ``^st.MXCSR.OM``,
   ``^st.MXCSR.ZM``, ``^st.MXCSR.DM``, ``^st.MXCSR.IM``, ``~^st.MXCSR.DAZ``]

fun process_float_flags q =
  process_float_flags_def
  |> Q.ISPEC q
  |> (fn th => Thm.AP_THM th st)
  |> SIMP_RULE (srw_ss()++boolSimps.LET_ss)
       [Ntimes state_transformerTheory.FOREACH_def 5,
        state_transformerTheory.BIND_DEF,
        state_transformerTheory.UNIT_DEF,
        pairTheory.UNCURRY, cond_rand_thms,
        XM_exception_def, initial_ieee_flags_def]
  |> CONV_RULE (utilsLib.INST_REWRITE_CONV (List.map ASSUME mxcsr))
  |> FULL_CONV_RULE DATATYPE_CONV

val process_float_flags1 = process_float_flags `[f : bool # flags]`
val process_float_flags2 = process_float_flags `[f1 : bool # flags; f2]`
val process_float_flags4 = process_float_flags `[f1 : bool # flags; f2; f3; f4]`

Theorem lem1[local]:
  (!x y.
   (if IS_SOME x then i2w (THE x) else y) =
    case x of SOME a => i2w a | _ => y) /\
  (!x y.
   (if IS_SOME x then w2w (i2w (THE x) : 'c word) else y) =
    case x of SOME a => w2w (i2w a : 'c word) | _ => y)
Proof
  strip_tac \\ Cases \\ rw []
QED

Theorem lem2[local]:
  (case x of
       LT => s with EFLAGS := a
     | EQ => s with EFLAGS := b
     | GT => s with EFLAGS := c
     | UN => s with EFLAGS := d)
   with EFLAGS :=
     (Z_SF =+ SOME F)
       ((Z_AF =+ SOME F)
         ((Z_OF =+ SOME F)
           (case x of
               LT => s with EFLAGS :=
                 (Z_CF =+ SOME T) ((Z_PF =+ SOME F) ((Z_ZF =+ SOME F) s.EFLAGS))
             | EQ => s with EFLAGS :=
                 (Z_CF =+ SOME F) ((Z_PF =+ SOME F) ((Z_ZF =+ SOME T) s.EFLAGS))
             | GT => s with EFLAGS :=
                 (Z_CF =+ SOME F) ((Z_PF =+ SOME F) ((Z_ZF =+ SOME F) s.EFLAGS))
             | UN => s with EFLAGS :=
                 (Z_CF =+ SOME T) ((Z_PF =+ SOME T) ((Z_ZF =+ SOME T) s.EFLAGS))
           ).EFLAGS)) =
  s with EFLAGS :=
    (Z_SF =+ SOME F)
      ((Z_AF =+ SOME F)
        ((Z_OF =+ SOME F)
          ((Z_CF =+ SOME (x IN {LT; UN}))
            ((Z_PF =+ SOME (x = UN))
              ((Z_ZF =+ SOME (x IN {EQ; UN})) s.EFLAGS)))))
Proof
  Cases_on `x` \\ simp []
QED

val rule = List.map (REWRITE_RULE [lem1])

fun fpEV aug =
  let
    val c = case aug of
               SOME [] => rm
             | SOME a => utilsLib.augment (`f`, a) xmm
             | NONE => xmm
  in
    EV ([dfn'bin_PD_def, dfn'bin_SD_def, dfn'bin_PS_def, dfn'bin_SS_def,
         dfn'logic_PD_def, dfn'logic_PS_def, sse_logic_def,
         dfn'CMPPD_def, dfn'CMPSD_def, dfn'CMPPS_def, dfn'CMPSS_def,
         dfn'SQRTPD_def, dfn'SQRTSD_def, dfn'SQRTPS_def, dfn'SQRTSS_def,
         dfn'CVTDQ2PD_def, dfn'CVTDQ2PS_def, dfn'CVTPD2DQ_def,
         dfn'CVTPD2PS_def, dfn'CVTPS2DQ_def, dfn'CVTPS2PD_def,
         dfn'CVTSD2SS_def, dfn'CVTSS2SD_def, dfn'MOVUP_D_S_def,
         dfn'CVTSD2SI_def, dfn'CVTSI2SD_def,
         dfn'CVTSI2SS_def, dfn'CVTSS2SI_def,
         dfn'COMISD_def, dfn'COMISS_def, dfn'MOV_D_Q_def, dfn'MOVQ_def,
         dfn'MOVSD_def, dfn'MOVSS_def, dfn'PCMPEQQ_def,
         write'SF_def, write'AF_def, write'OF_def, write'CF_def,
         write'PF_def, write'ZF_def, write'Eflag_rwt,
         RoundingMode_def, rounding_mode, sse_compare_signalling_def,
         process_float_flags1, process_float_flags2, process_float_flags4,
         sse_binop32_def, sse_sqrt32_def, sse_compare32_def, sse_from_int32_def,
         sse_to_int32_def, flush_to_zero32, denormal_to_zero32_def,
         sse_binop64_def, sse_sqrt64_def, sse_compare64_def, sse_from_int64_def,
         sse_to_int64_def, flush_to_zero64, denormal_to_zero64_def,
         initial_ieee_flags_def, set_precision_def, snd_with_flags,
         pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY,
         ConseqConvTheory.COND_CLAUSES_FT, ConseqConvTheory.COND_CLAUSES_FF,
         pairTheory.pair_CASE_def, word_thms, lem2] @
       XMM_rwt @ write'XMM_rwt @ EA_rwt @ write'EA_rwt @ ea_Zrm_rwt) [mxcsr] c
  end

val pshift = LIST_CONJ o map (DISCH_ALL o ADD_PRECOND_RULE) o
  EV ([dfn'PSRLW_imm_def, dfn'PSRAW_imm_def, dfn'PSLLW_imm_def,
       dfn'PSRLD_imm_def, dfn'PSRAD_imm_def, dfn'PSLLD_imm_def,
       dfn'PSRLQ_imm_def, dfn'PSLLQ_imm_def, dfn'PSRLDQ_def, dfn'PSLLDQ_def] @
      XMM_rwt @ write'XMM_rwt) [] []

val sse_bin = LIST_CONJ o map (DISCH_ALL o ADD_PRECOND_RULE) o
  fpEV (SOME [``sse_add``, ``sse_sub``, ``sse_mul``, ``sse_div``,
              ``sse_min``, ``sse_max``])

val sse_logic = LIST_CONJ o map (DISCH_ALL o ADD_PRECOND_RULE) o
  fpEV (SOME [``sse_and``, ``sse_andn``, ``sse_or``, ``sse_xor``])

val sse_compare = LIST_CONJ o map (DISCH_ALL o ADD_PRECOND_RULE) o
  fpEV (SOME [``sse_eq_oq``, ``sse_lt_os``, ``sse_le_os``, ``sse_unord_q``,
              ``sse_neq_uq``, ``sse_nlt_us``, ``sse_nle_us``, ``sse_ord_q``])

fun sse f = LIST_CONJ o map (DISCH_ALL o ADD_PRECOND_RULE) o f o rule o fpEV NONE
val sse_rm = LIST_CONJ o map (DISCH_ALL o ADD_PRECOND_RULE) o fpEV (SOME [])

Theorem bin_PD = sse_bin ``dfn'bin_PD (f, dst, xmm)``
Theorem bin_SD = sse_bin ``dfn'bin_SD (f, dst, xmm)``
Theorem bin_PS = sse_bin ``dfn'bin_PS (f, dst, xmm)``
Theorem bin_SS = sse_bin ``dfn'bin_SS (f, dst, xmm)``

Theorem logic_PD = sse_logic ``dfn'logic_PD (f, dst, xmm)``
Theorem logic_PS = sse_logic ``dfn'logic_PS (f, dst, xmm)``

Theorem CMPPD = sse_compare ``dfn'CMPPD (f, dst, xmm)``
Theorem CMPSD = sse_compare ``dfn'CMPSD (f, dst, xmm)``
Theorem CMPPS = sse_compare ``dfn'CMPPS (f, dst, xmm)``
Theorem CMPSS = sse_compare ``dfn'CMPSS (f, dst, xmm)``

Theorem COMISD = sse I ``dfn'COMISD (src1, xmm)``
Theorem COMISS = sse I ``dfn'COMISS (src1, xmm)``

Theorem SQRTPD = sse I ``dfn'SQRTPD (dst, xmm)``
Theorem SQRTSD = sse I ``dfn'SQRTSD (dst, xmm)``
Theorem SQRTPS = sse I ``dfn'SQRTPS (dst, xmm)``
Theorem SQRTSS = sse I ``dfn'SQRTSS (dst, xmm)``

Theorem CVTDQ2PD = sse I ``dfn'CVTDQ2PD (dst, xmm)``
Theorem CVTDQ2PS = sse I ``dfn'CVTDQ2PS (dst, xmm)``
Theorem CVTPD2DQ = sse I ``dfn'CVTPD2DQ (F, dst, xmm)``
Theorem CVTTPD2DQ = sse I ``dfn'CVTPD2DQ (T, dst, xmm)``
Theorem CVTPD2PS = sse I ``dfn'CVTPD2PS (dst, xmm)``
Theorem CVTPS2DQ = sse I ``dfn'CVTPS2DQ (F, dst, xmm)``
Theorem CVTTPS2DQ = sse I ``dfn'CVTPS2DQ (T, dst, xmm)``
Theorem CVTPS2PD = sse I ``dfn'CVTPS2PD (dst, xmm)``
Theorem CVTSD2SS = sse I ``dfn'CVTSD2SS (dst, xmm)``
Theorem CVTSS2SD = sse I ``dfn'CVTSS2SD (dst, xmm)``
Theorem CVTSD2SI_0 = sse I ``dfn'CVTSD2SI (F, T, r, xmm)``
Theorem CVTSD2SI_1 = sse I ``dfn'CVTSD2SI (F, F, r, xmm)``
Theorem CVTTSD2SI_0 = sse I ``dfn'CVTSD2SI (T, T, r, xmm)``
Theorem CVTTSD2SI_1 = sse I ``dfn'CVTSD2SI (T, F, r, xmm)``
Theorem CVTSI2SD_0 = sse_rm ``dfn'CVTSI2SD (T, x, rm)``
Theorem CVTSI2SD_1 = sse_rm ``dfn'CVTSI2SD (F, x, rm)``
Theorem CVTSI2SS_0 = sse_rm ``dfn'CVTSI2SS (T, x, rm)``
Theorem CVTSI2SS_1 = sse_rm ``dfn'CVTSI2SS (F, x, rm)``
Theorem CVTSS2SI_0 = sse I ``dfn'CVTSS2SI (F, T, r, xmm)``
Theorem CVTSS2SI_1 = sse I ``dfn'CVTSS2SI (F, F, r, xmm)``
Theorem CVTTSS2SI_0 = sse I ``dfn'CVTSS2SI (T, T, r, xmm)``
Theorem CVTTSS2SI_1 = sse I ``dfn'CVTSS2SI (T, F, r, xmm)``

(* TODO: MOVAP_D_S *)

Theorem MOVUP_D_S_0 = sse I ``dfn'MOVUP_D_S (double, xmm_reg (dst), xmm)``
Theorem MOVUP_D_S_1 = sse List.tl ``dfn'MOVUP_D_S (double, xmm, xmm_reg (src))``

Theorem MOVSD_0 = sse I ``dfn'MOVSD (xmm_reg (dst), xmm)``
Theorem MOVSD_1 = sse (wv_to_v o List.tl) ``dfn'MOVSD (xmm, xmm_reg (src))``
Theorem MOVSS_0 = sse I ``dfn'MOVSS (xmm_reg (dst), xmm)``
Theorem MOVSS_1 = sse (wv_to_v o List.tl) ``dfn'MOVSS (xmm, xmm_reg (src))``

Theorem MOV_D_Q_0 = sse_rm ``dfn'MOV_D_Q (T, T, dst, rm)``
Theorem MOV_D_Q_1 = sse_rm ``dfn'MOV_D_Q (T, F, dst, rm)``
Theorem MOV_D_Q_2 = sse_rm ``dfn'MOV_D_Q (F, T, dst, rm)``
Theorem MOV_D_Q_3 = sse_rm ``dfn'MOV_D_Q (F, F, dst, rm)``

Theorem MOVQ_0 = sse I ``dfn'MOVQ (xmm_reg (dst), xmm)``
Theorem MOVQ_1 = sse List.tl ``dfn'MOVQ (xmm, xmm_reg (src))``

Theorem PCMPEQQ = sse I ``dfn'PCMPEQQ (dst, xmm)``

Theorem PSRLW_imm = pshift ``dfn'PSRLW_imm (r, i)``
Theorem PSRAW_imm = pshift ``dfn'PSRAW_imm (r, i)``
Theorem PSLLW_imm = pshift ``dfn'PSLLW_imm (r, i)``
Theorem PSRLD_imm = pshift ``dfn'PSRLD_imm (r, i)``
Theorem PSRAD_imm = pshift ``dfn'PSRAD_imm (r, i)``
Theorem PSLLD_imm = pshift ``dfn'PSLLD_imm (r, i)``
Theorem PSRLQ_imm = pshift ``dfn'PSRLQ_imm (r, i)``
Theorem PSLLQ_imm = pshift ``dfn'PSLLQ_imm (r, i)``
Theorem PSRLDQ = pshift ``dfn'PSRLDQ (r, i)``
Theorem PSLLDQ = pshift ``dfn'PSLLDQ (r, i)``
