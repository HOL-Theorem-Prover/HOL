(* ------------------------------------------------------------------------
   Support for x86 step evaluator
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib

open wordsLib blastLib
open x64Theory
open lcsymtacs utilsLib

val _ = new_theory "x64_step"

(* ------------------------------------------------------------------------ *)

val () = (numLib.prefer_num ()
          ; wordsLib.prefer_word ()
          ; wordsLib.guess_lengths ())

infix \\
val op \\ = op THEN;

(* ------------------------------------------------------------------------ *)

val NextStateX64_def = Define`
   NextStateX64 s0 =
     let s1 = SND (x64_next s0) in
       if s1.exception = NoException then SOME s1 else NONE`

val NextStateX64_0 = utilsLib.ustore_thm("NextStateX64_0",
  `(s.exception = NoException) ==>
   (x64_decode (FST (x64_fetch s)) = Zfull_inst (p, ast, strm1)) /\
   (20 - LENGTH strm1 = len) /\
   (checkIcache len s = ((), s)) /\
   (!s. Run ast s = f s) /\
   (f (s with RIP := s.RIP + n2w len) = ((), s1)) /\
   (s1.exception = s.exception) ==>
   (NextStateX64 s = SOME s1)`,
   lrw [NextStateX64_def, x64_next_def] \\ lrw [])

val NextStateX64 = utilsLib.ustore_thm("NextStateX64",
  `(s.exception = NoException) ==>
   (x64_decode (FST (x64_fetch s)) = Zfull_inst (p, ast, strm1)) /\
   (20 - LENGTH strm1 = len) /\
   (checkIcache len s = ((), s)) /\
   (!s. Run ast s = f x s) /\
   (f x (s with RIP := s.RIP + n2w len) = ((), s1)) /\
   (s1.exception = s.exception) ==>
   (NextStateX64 s = SOME s1)`,
   lrw [NextStateX64_def, x64_next_def] \\ lrw [])

(* ------------------------------------------------------------------------ *)

val read_mem16_def = Lib.with_flag (Feedback.emit_MESG, false) Define`
   read_mem16 (m: word64 -> word8 option) a =
     case (m a, m (a + 1w)) of
        (SOME v1, SOME v2) => SOME (v2 @@ v1)
      | _ => NONE`;

val read_mem32_def = Lib.with_flag (Feedback.emit_MESG, false) Define`
   read_mem32 (m: word64 -> word8 option) a =
     case (m a, m (a + 1w), m (a + 2w), m (a + 3w)) of
        (SOME v1, SOME v2, SOME v3, SOME v4) => SOME (v4 @@ v3 @@ v2 @@ v1)
      | _ => NONE`;

val read_mem64_def = Lib.with_flag (Feedback.emit_MESG, false) Define`
   read_mem64 (m: word64 -> word8 option) a =
     case (m a, m (a + 1w), m (a + 2w), m (a + 3w),
           m (a + 4w), m (a + 5w), m (a + 6w), m (a + 7w)) of
        (SOME v1, SOME v2, SOME v3, SOME v4,
         SOME v5, SOME v6, SOME v7, SOME v8) =>
            SOME (v8 @@ v7 @@ v6 @@ v5 @@ v4 @@ v3 @@ v2 @@ v1)
      | _ => NONE`;

val write_mem16_def = Define`
   write_mem16 (m: word64 -> word8 option) a (v: word16) =
     (a + 1w =+ SOME ((15 >< 8) v))
        ((a =+ SOME ((7 >< 0) v)) m)`;

val write_mem32_def = Define`
   write_mem32 (m: word64 -> word8 option) a (v: word32) =
     (a + 3w =+ SOME ((31 >< 24) v))
        ((a + 2w =+ SOME ((23 >< 16) v))
           ((a + 1w =+ SOME ((15 >< 8) v))
              ((a =+ SOME ((7 >< 0) v)) m)))`;

val write_mem64_def = Define`
   write_mem64 (m: word64 -> word8 option) a (v: word64) =
     (a + 7w =+ SOME ((63 >< 56) v))
        ((a + 6w =+ SOME ((55 >< 48) v))
           ((a + 5w =+ SOME ((47 >< 40) v))
              ((a + 4w =+ SOME ((39 >< 32) v))
                 ((a + 3w =+ SOME ((31 >< 24) v))
                    ((a + 2w =+ SOME ((23 >< 16) v))
                       ((a + 1w =+ SOME ((15 >< 8) v))
                          ((a =+ SOME ((7 >< 0) v)) m)))))))`;

val mem16_rwt = ustore_thm("mem16_rwt",
   `(read_mem16 s.MEM a = SOME v) ==> (mem16 a s = (v, s))`,
   Cases_on `s.MEM a`
   \\ Cases_on `s.MEM (a + 1w)`
   \\ simp [mem16_def, mem8_def, read_mem16_def]
   )

val mem32_rwt = ustore_thm("mem32_rwt",
   `(read_mem32 s.MEM a = SOME v) ==> (mem32 a s = (v, s))`,
   Cases_on `s.MEM a`
   \\ Cases_on `s.MEM (a + 1w)`
   \\ Cases_on `s.MEM (a + 2w)`
   \\ Cases_on `s.MEM (a + 3w)`
   \\ simp [mem32_def, mem16_def, mem8_def, read_mem32_def]
   \\ blastLib.BBLAST_TAC
   )

val mem64_rwt = ustore_thm("mem64_rwt",
   `(read_mem64 s.MEM a = SOME v) ==> (mem64 a s = (v, s))`,
   Cases_on `s.MEM a`
   \\ Cases_on `s.MEM (a + 1w)`
   \\ Cases_on `s.MEM (a + 2w)`
   \\ Cases_on `s.MEM (a + 3w)`
   \\ Cases_on `s.MEM (a + 4w)`
   \\ Cases_on `s.MEM (a + 5w)`
   \\ Cases_on `s.MEM (a + 6w)`
   \\ Cases_on `s.MEM (a + 7w)`
   \\ simp [mem64_def, mem32_def, mem16_def, mem8_def, read_mem64_def]
   \\ blastLib.BBLAST_TAC
   )

val write'mem16_rwt = ustore_thm("write'mem16_rwt",
   `(read_mem16 s.MEM a = SOME wv) ==>
    (write'mem16 (d, a) s = ((), s with MEM := write_mem16 s.MEM a d))`,
   Cases_on `s.MEM a`
   \\ Cases_on `s.MEM (a + 1w)`
   \\ simp [combinTheory.APPLY_UPDATE_THM,
            blastLib.BBLAST_PROVE ``a <> a + 1w: word64``,
            write'mem16_def, write'mem8_def, write_mem16_def, read_mem16_def]
   )

val write'mem32_rwt = ustore_thm("write'mem32_rwt",
   `(read_mem32 s.MEM a = SOME wv) ==>
    (write'mem32 (d, a) s = ((), s with MEM := write_mem32 s.MEM a d))`,
   Cases_on `s.MEM a`
   \\ Cases_on `s.MEM (a + 1w)`
   \\ Cases_on `s.MEM (a + 2w)`
   \\ Cases_on `s.MEM (a + 3w)`
   \\ simp [combinTheory.APPLY_UPDATE_THM,
            blastLib.BBLAST_PROVE ``a <> a + 1w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 2w: word64``,
            blastLib.BBLAST_PROVE ``a <> a + 3w: word64``,
            write'mem32_def, write'mem16_def, write'mem8_def,
            write_mem32_def, read_mem32_def]
   \\ srw_tac [wordsLib.WORD_EXTRACT_ss] []
   )

val write'mem64_rwt = ustore_thm("write'mem64_rwt",
   `(read_mem64 s.MEM a = SOME wv) ==>
    (write'mem64 (d, a) s = ((), s with MEM := write_mem64 s.MEM a d))`,
   simp [write'mem64_def, write'mem32_def, write'mem16_def,
         write_mem64_def, read_mem64_def]
   \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
   \\ Cases_on `s.MEM a`
   \\ Cases_on `s.MEM (a + 1w)`
   \\ Cases_on `s.MEM (a + 2w)`
   \\ Cases_on `s.MEM (a + 3w)`
   \\ Cases_on `s.MEM (a + 4w)`
   \\ Cases_on `s.MEM (a + 5w)`
   \\ Cases_on `s.MEM (a + 6w)`
   \\ Cases_on `s.MEM (a + 7w)`
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

val read_mem16 = Q.store_thm("read_mem16",
   `!m a v.
      (read_mem16 m a = SOME v) =
      (m a = SOME ((7 >< 0) v)) /\
      (m (a + 1w) = SOME ((15 ><  8) v))`,
   REPEAT strip_tac
   \\ Cases_on `m a`
   \\ Cases_on `m (a + 1w)`
   \\ simp [read_mem16_def]
   \\ blastLib.BBLAST_TAC
   )

val read_mem32 = Q.store_thm("read_mem32",
   `!m a v.
      (read_mem32 m a = SOME v) =
      (m a = SOME ((7 >< 0) v)) /\
      (m (a + 1w) = SOME ((15 ><  8) v)) /\
      (m (a + 2w) = SOME ((23 >< 16) v)) /\
      (m (a + 3w) = SOME ((31 >< 24) v))`,
   REPEAT strip_tac
   \\ Cases_on `m a`
   \\ Cases_on `m (a + 1w)`
   \\ Cases_on `m (a + 2w)`
   \\ Cases_on `m (a + 3w)`
   \\ simp [read_mem32_def]
   \\ blastLib.BBLAST_TAC
   )

val read_mem64 = Q.store_thm("read_mem64",
   `!m a v.
      (read_mem64 m a = SOME v) =
      (m a = SOME ((7 >< 0) v)) /\
      (m (a + 1w) = SOME ((15 ><  8) v)) /\
      (m (a + 2w) = SOME ((23 >< 16) v)) /\
      (m (a + 3w) = SOME ((31 >< 24) v)) /\
      (m (a + 4w) = SOME ((39 >< 32) v)) /\
      (m (a + 5w) = SOME ((47 >< 40) v)) /\
      (m (a + 6w) = SOME ((55 >< 48) v)) /\
      (m (a + 7w) = SOME ((63 >< 56) v))`,
   REPEAT strip_tac
   \\ Cases_on `m a`
   \\ Cases_on `m (a + 1w)`
   \\ Cases_on `m (a + 2w)`
   \\ Cases_on `m (a + 3w)`
   \\ Cases_on `m (a + 4w)`
   \\ Cases_on `m (a + 5w)`
   \\ Cases_on `m (a + 6w)`
   \\ Cases_on `m (a + 7w)`
   \\ simp [read_mem64_def]
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
   `!b1 l. immediate8 (b1 :: l) =
          (if b1 <+ 128w then
              n2w (w2n b1)
           else
              n2w (2 ** 64 - 2 ** 8 + w2n b1), l)`,
   simp [GSYM wordsTheory.word_add_n2w, n2w_w2n_lem]
   \\ rw [immediate8_def]
   \\ blastLib.FULL_BBLAST_TAC
   )) |> utilsLib.save_as "immediate8_rwt";

val immediate16_rwt = to_n2w [`n2w n2`, `n2w n1`] (Q.prove(
   `!b2 b1 l.
          immediate16 (b2 :: b1 :: l) =
          (if b1 <+ 128w then
              n2w (w2n b1 * 2 ** 8 + w2n b2)
           else
              n2w (2 ** 64 - 2 ** 16 + w2n b1 * 2 ** 8 + w2n b2), l)`,
   simp [GSYM wordsTheory.word_add_n2w, n2w_w2n_lem,
         GSYM wordsTheory.word_mul_n2w]
   \\ rw [immediate16_def]
   \\ blastLib.FULL_BBLAST_TAC
   )) |> utilsLib.save_as "immediate16_rwt";

val immediate32_rwt = to_n2w [`n2w n4`, `n2w n3`, `n2w n2`, `n2w n1`] (Q.prove(
   `!b4 b3 b2 b1 l.
          immediate32 (b4 :: b3 :: b2 :: b1 :: l) =
          (if b1 <+ 128w then
              n2w (w2n b1 * 2 ** 24 + w2n b2 * 2 ** 16 +
                   w2n b3 * 2 ** 8 + w2n b4)
           else
              n2w (2 ** 64 - 2 ** 32 +
                   w2n b1 * 2 ** 24 + w2n b2 * 2 ** 16 +
                   w2n b3 * 2 ** 8 + w2n b4), l)`,
   simp [GSYM wordsTheory.word_add_n2w, n2w_w2n_lem,
         GSYM wordsTheory.word_mul_n2w]
   \\ rw [immediate32_def]
   \\ blastLib.FULL_BBLAST_TAC
   )) |> utilsLib.save_as "immediate32_rwt";

val immediate64_rwt =
   to_n2w [`n2w n8`, `n2w n7`, `n2w n6`, `n2w n5`,
           `n2w n4`, `n2w n3`, `n2w n2`, `n2w n1`] (Q.prove(
   `!b8 b7 b6 b5 b4 b3 b2 b1 l.
          immediate64 (b8 :: b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: l) =
          (n2w (w2n b1 * 2 ** 56 + w2n b2 * 2 ** 48 +
                w2n b3 * 2 ** 40 + w2n b4 * 2 ** 32 +
                w2n b5 * 2 ** 24 + w2n b6 * 2 ** 16 +
                w2n b7 * 2 ** 8 + w2n b8), l)`,
   rw [GSYM wordsTheory.word_add_n2w, n2w_w2n_lem,
       GSYM wordsTheory.word_mul_n2w, immediate64_def]
   \\ blastLib.FULL_BBLAST_TAC
   )) |> utilsLib.save_as "immediate64_rwt";

fun imm l = utilsLib.SRW_RULE [immediate8_rwt, immediate16_rwt, immediate32_rwt]
               (Q.SPECL l immediate_def)

val immediate_rwt =
  LIST_CONJ (List.map imm [[`Z8 have_rex`, `n2w n::t`],
                           [`Z16`, `n2w n2::n2w n1::t`],
                           [`Z32`, `n2w n4::n2w n3::n2w n2::n2w n1::t`],
                           [`Z64`, `n2w n4::n2w n3::n2w n2::n2w n1::t`]])
  |> utilsLib.save_as "immediate_rwt";

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

val unit_state_cond = Q.store_thm("unit_state_cond",
  `!b s1 s2. (if b then ((), s1: x64_state) else ((), s2)) =
             ((), if b then s1 else s2)`, rw [])

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
    (!a: word64. (31 >< 0) (~(a && 0xFFFFFFFFw)) = ~a && 0xFFFFFFFFw)
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

val () = export_theory ()
