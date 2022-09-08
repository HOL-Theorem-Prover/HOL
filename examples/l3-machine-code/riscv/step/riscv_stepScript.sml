(* ------------------------------------------------------------------------
   Definitions and theorems used by RISC-V step evaluator (riscv_stepLib)
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib

open utilsLib
open wordsLib blastLib alignmentTheory
open riscvTheory

val () = Theory.new_theory "riscv_step"
val _ = ParseExtras.temp_loose_equality()

val ERR = mk_HOL_ERR "riscv_stepTheory";

val () =
  ( List.app (fn f => f ())
      [numLib.prefer_num, wordsLib.prefer_word, wordsLib.guess_lengths]
  ; show_assums := true
  ; General.ignore (Parse.hide "imm")
  )

fun uprove a b = utilsLib.STRIP_UNDISCH (Q.prove (a, b))

(* ------------------------------------------------------------------------
   Simplified Fetch and Next functions
   ------------------------------------------------------------------------ *)

val Fetch_def = Define`
  Fetch s =
  let (w, s) = translateAddr (PC s, Instruction, Read) s in
    (rawReadInst (THE w) s)`

val update_pc_def = Define `update_pc v s = SOME (write'PC v s)`

val DecodeAny_def = Define `
  DecodeAny f = case f of Half h => DecodeRVC h | Word w => Decode w`

val NextRISCV_def = Define`
  NextRISCV s =
  let (f, s) = Fetch s in
  let s = Run (DecodeAny f) s in
  if s.exception <> NoException then
    NONE
  else
    let pc = PC s in
    case NextFetch s of
       NONE => update_pc (pc + Skip s) s
     | SOME (BranchTo a) => update_pc a (write'NextFetch NONE s)
     | _ => NONE`

(* ------------------------------------------------------------------------
   Evaluation theorem
   ------------------------------------------------------------------------ *)

val NextRISCV = Q.store_thm("NextRISCV",
  `(Fetch s = (w, s')) /\
   (DecodeAny w = i) /\
   (Run i s' = nxt) /\
   (nxt.exception = NoException) /\
   (nxt.c_NextFetch nxt.procID = NONE) ==>
   (NextRISCV s = update_pc (nxt.c_PC nxt.procID + Skip nxt) nxt)`,
  lrw [NextRISCV_def, PC_def, NextFetch_def, write'NextFetch_def]
  )

val NextRISCV_branch = Q.store_thm("NextRISCV_branch",
  `(Fetch s = (w, s')) /\
   (DecodeAny w = i) /\
   (Run i s' = nxt) /\
   (nxt.exception = NoException) /\
   (nxt.c_NextFetch nxt.procID = SOME (BranchTo a)) ==>
   (NextRISCV s =
      update_pc a
        (nxt with c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch))`,
  lrw [NextRISCV_def, PC_def, NextFetch_def, write'NextFetch_def]
  \\ Cases_on `Run (Decode w) s'`
  \\ fs []
  )

val NextRISCV_cond_branch = Q.store_thm("NextRISCV_cond_branch",
  `(Fetch s = (w, s')) /\
   (DecodeAny w = i) /\
   (Run i s' = nxt) /\
   (nxt.exception = NoException) /\
   (nxt.c_NextFetch nxt.procID = if b then SOME (BranchTo a) else NONE) ==>
   (NextRISCV s =
      update_pc (if b then a else nxt.c_PC nxt.procID + Skip nxt)
        (nxt with c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch))`,
  lrw [NextRISCV_def, PC_def, NextFetch_def, write'NextFetch_def]
  \\ Cases_on `Run (DecodeAny w) s'`
  \\ fs [update_pc_def, write'PC_def, riscv_state_component_equality,
         combinTheory.UPDATE_APPLY_IMP_ID]
  )

(* ------------------------------------------------------------------------
   Sub-word select operation (temporary)
   ------------------------------------------------------------------------ *)

val select_def = zDefine`
  select (p:'a word) (w: word64) =
  let sz = 64 DIV (2 ** dimindex(:'a)) in
  let l = w2n p * sz in
    (l + sz - 1 >< l) w : 'b word`

(* ------------------------------------------------------------------------
   Word extend abbreviations
   ------------------------------------------------------------------------ *)

val () = List.app Parse.temp_overload_on
   [
    ("s_extend32", ``\w: word64. sw2sw ((31 >< 0) w : word32) : word64``),
    ("z_extend32", ``\w: word64. w2w ((31 >< 0) w : word32) : word64``),
    ("s_extend16", ``\w: word64. sw2sw ((15 >< 0) w : word16) : word64``),
    ("z_extend16", ``\w: word64. w2w ((15 >< 0) w : word16) : word64``),
    ("s_extend8",  ``\w: word64. sw2sw ((7 >< 0) w : word8) : word64``),
    ("z_extend8",  ``\w: word64. w2w ((7 >< 0) w : word8) : word64``)
   ]

(* ------------------------------------------------------------------------
   Simplifying Rewrites
   ------------------------------------------------------------------------ *)

val word_bit_1_0 = store_thm("word_bit_1_0[simp]",
  ``(word_bit 1 ((v2w [x0; x1; x2; x3; x4; x5; x6; x7]):word8) = x6) /\
    (word_bit 0 ((v2w [x0; x1; x2; x3; x4; x5; x6; x7]):word8) = x7)``,
  blastLib.BBLAST_TAC);

val cond_lem1 = Q.prove(
  `(if b1 then (if b2 then x else y1) else (if b2 then x else y2)) =
   (if b2 then x else if b1 then y1 else y2)`,
  rw []
  )

val cond_rand_shift = Q.prove(
  `((if b then x else y) << n = if b then x << n else y << n) /\
   ((if b then x else y) >>> n = if b then x >>> n else y >>> n)`,
  rw []
  )

val word_bit_0_lemmas = Q.store_thm("word_bit_0_lemmas",
  `!w. ¬word_bit 0 (0xFFFFFFFFFFFFFFFEw && w:word64) /\
       word_bit 0 ((0xFFFFFFFFFFFFFFFEw && w:word64) + v) = word_bit 0 v`,
  blastLib.BBLAST_TAC)

val cond_rand_thms =
  utilsLib.mk_cond_rand_thms
    [pairSyntax.fst_tm,
     pairSyntax.snd_tm,
     wordsSyntax.sw2sw_tm,
     wordsSyntax.w2w_tm,
     wordsSyntax.word_add_tm,
     wordsSyntax.word_and_tm,
     wordsSyntax.word_or_tm,
     wordsSyntax.word_xor_tm,
     ``(=):Architecture -> Architecture -> bool``,
     ``(=):'a word -> 'a word -> bool``,
     ``(h >< l) : 'a word -> 'b word``
    ]

val ifTF = Q.prove(`(if b then T else F) = b`, rw [])

val v2w_0_rwts = Q.store_thm("v2w_0_rwts",
  `((v2w [F; F; F; F; T] = 1w: word5)) /\
   ((v2w [F; F; F; F; F] = 0w: word5)) /\
   ((v2w [T; b3; b2; b1; b0] = 0w: word5) = F) /\
   ((v2w [b3; T; b2; b1; b0] = 0w: word5) = F) /\
   ((v2w [b3; b2; T; b1; b0] = 0w: word5) = F) /\
   ((v2w [b3; b2; b1; T; b0] = 0w: word5) = F) /\
   ((v2w [b3; b2; b1; b0; T] = 0w: word5) = F)`,
   blastLib.BBLAST_TAC
   )

val aligned2 = Q.prove(
  `(!w: word64. ((1 >< 0) w = 0w: word2) = aligned 2 w)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val aligned3 = Q.prove(
  `(!w: word64. (w2n ((2 >< 0) w: word3) = 0) = aligned 3 w)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val address_align = blastLib.BBLAST_PROVE
  ``w2w ((63 >< 3) a : 61 word) << 3 = (63 '' 3) (a: word64)``

val address_align2 = blastLib.BBLAST_PROVE
  ``w2w ((63 >< 3) a + 1w: 61 word) << 3 = (63 '' 3) (a: word64) + 8w``

val address_aligned3 = uprove
  `aligned 3 (a: word64) ==> ((63 '' 3) a = a)`
  (
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val words_of_dword = Q.prove(
  `!b7:word8 b6:word8 b5:word8 b4:word8 b3:word8 b2:word8 b1:word8 b0:word8.
     ((63 >< 32) ( b7 @@ b6 @@ b5 @@ b4 @@ b3 @@ b2 @@ b1 @@ b0 ) =
                   b7 @@ b6 @@ b5 @@ b4) /\
     ((31 >< 0 ) ( b7 @@ b6 @@ b5 @@ b4 @@ b3 @@ b2 @@ b1 @@ b0 ) =
                   b3 @@ b2 @@ b1 @@ b0)`,
  simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  )

val read_word = uprove
  `aligned 2 (a: word64) ==>
   ((if word_bit 2 a then
       (63 >< 32)
         (mem ((63 '' 3) a + 7w) @@
          mem ((63 '' 3) a + 6w) @@
          mem ((63 '' 3) a + 5w) @@
          mem ((63 '' 3) a + 4w) @@
          mem ((63 '' 3) a + 3w) @@
          mem ((63 '' 3) a + 2w) @@
          mem ((63 '' 3) a + 1w) @@
          mem ((63 '' 3) a)) : word32
     else
       (31 >< 0)
         (mem ((63 '' 3) a + 7w) @@
          mem ((63 '' 3) a + 6w) @@
          mem ((63 '' 3) a + 5w) @@
          mem ((63 '' 3) a + 4w) @@
          mem ((63 '' 3) a + 3w) @@
          mem ((63 '' 3) a + 2w) @@
          mem ((63 '' 3) a + 1w) @@
          mem ((63 '' 3) a))) =
    mem (a + 3w) @@ mem (a + 2w) @@ mem (a + 1w) @@ (mem a : word8))`
  (
  rewrite_tac [GSYM aligned2, words_of_dword]
  \\ strip_tac
  \\ CASE_TAC
  >| [
    `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  )

val tac =
  lrw [select_def, alignmentTheory.aligned_extract]
  >| [
    `(2 >< 2) x = 0w: word1` by blastLib.FULL_BBLAST_TAC,
    `((2 >< 2) x = 1w: word1) /\
     ((2 >< 0) x = 4w: word3)` by blastLib.FULL_BBLAST_TAC,
    `(2 >< 2) y = 0w: word1` by blastLib.FULL_BBLAST_TAC,
    `((2 >< 2) y = 1w: word1) /\
     ((2 >< 0) y = 4w: word3)` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  \\ blastLib.FULL_BBLAST_TAC

val aligned_select_word_s = uprove
  `aligned 2 (if b then (x: word64) else y) ==>
   ((if aligned 3 (if b then x else y) then
       s_extend32 w0
     else
       s_extend32
         ((63 >< 0)
            (((w1: word64) @@ w0) >>
              (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
     s_extend32 (select (if b then (2 >< 2) x else (2 >< 2) y : word1) w0))`
   tac

val aligned_select_word_z = uprove
  `aligned 2 (if b then (x: word64) else y) ==>
   ((if aligned 3 (if b then x else y) then
       z_extend32 w0
     else
       z_extend32
         ((63 >< 0)
            (((w1: word64) @@ w0) >>
              (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
     z_extend32 (select (if b then (2 >< 2) x else (2 >< 2) y : word1) w0))`
   tac

val select_word = Q.prove(
  `aligned 2 (a: word64) ==>
   ((31 >< 0)
      (select ((2 >< 2) a : word1)
        (mem ((63 '' 3) a + 7w) @@
         mem ((63 '' 3) a + 6w) @@
         mem ((63 '' 3) a + 5w) @@
         mem ((63 '' 3) a + 4w) @@
         mem ((63 '' 3) a + 3w) @@
         mem ((63 '' 3) a + 2w) @@
         mem ((63 '' 3) a + 1w) @@
         mem ((63 '' 3) a     )) : word64) =
    mem (a + 3w) @@ mem (a + 2w) @@ mem (a + 1w) @@ (mem a : word8))`,
  lrw [alignmentTheory.aligned_extract, select_def]
  \\ wordsLib.Cases_on_word_value `(2 >< 2) a : word1`
  >| [
    `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  )
  |> Q.INST [`a` |-> `if b then x else y`, `mem` |-> `s.MEM8`]
  |> REWRITE_RULE [cond_rand_thms]
  |> utilsLib.STRIP_UNDISCH

val tac =
  lrw [select_def, alignmentTheory.aligned_extract]
  >| [
    `(2 >< 1) x = 0w: word2` by blastLib.FULL_BBLAST_TAC,
    `(2 >< 1) x IN {1w; 2w; 3w: word2}`
    by (wordsLib.Cases_on_word_value `(2 >< 1) x : word2`
        \\ fs []
        \\ blastLib.FULL_BBLAST_TAC
       )
    \\ fs []
    >| [
      `(2 >< 0) x = 2w: word3` by blastLib.FULL_BBLAST_TAC,
      `(2 >< 0) x = 4w: word3` by blastLib.FULL_BBLAST_TAC,
      `(2 >< 0) x = 6w: word3` by blastLib.FULL_BBLAST_TAC
    ],
    `(2 >< 1) y = 0w: word2` by blastLib.FULL_BBLAST_TAC,
    `(2 >< 1) y IN {1w; 2w; 3w: word2}`
    by (wordsLib.Cases_on_word_value `(2 >< 1) y : word2`
        \\ fs []
        \\ blastLib.FULL_BBLAST_TAC
       )
    \\ fs []
    >| [
      `(2 >< 0) y = 2w: word3` by blastLib.FULL_BBLAST_TAC,
      `(2 >< 0) y = 4w: word3` by blastLib.FULL_BBLAST_TAC,
      `(2 >< 0) y = 6w: word3` by blastLib.FULL_BBLAST_TAC
    ]
  ]
  \\ simp []
  \\ blastLib.FULL_BBLAST_TAC

val aligned_select_half_s = uprove
  `aligned 1 (if b then (x: word64) else y) ==>
   ((if aligned 3 (if b then x else y) then
       s_extend16 w0
     else
       s_extend16
         ((63 >< 0)
            (((w1: word64) @@ w0) >>
              (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
     s_extend16 (select (if b then (2 >< 1) x else (2 >< 1) y : word2) w0))`
  tac

val aligned_select_half_z = uprove
  `aligned 1 (if b then (x: word64) else y) ==>
   ((if aligned 3 (if b then x else y) then
       z_extend16 w0
     else
       z_extend16
         ((63 >< 0)
            (((w1: word64) @@ w0) >>
              (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
     z_extend16 (select (if b then (2 >< 1) x else (2 >< 1) y : word2) w0))`
  tac

val select_half = Q.prove(
  `aligned 1 (a: word64) ==>
   ((15 >< 0)
      (select ((2 >< 1) a : word2)
        (mem ((63 '' 3) a + 7w) @@
         mem ((63 '' 3) a + 6w) @@
         mem ((63 '' 3) a + 5w) @@
         mem ((63 '' 3) a + 4w) @@
         mem ((63 '' 3) a + 3w) @@
         mem ((63 '' 3) a + 2w) @@
         mem ((63 '' 3) a + 1w) @@
         mem ((63 '' 3) a     )) : word64) =
    mem (a + 1w) @@ (mem a : word8))`,
  lrw [alignmentTheory.aligned_extract, select_def]
  \\ wordsLib.Cases_on_word_value `(2 >< 1) a : word2`
  >| [
    `(63 '' 3) a = a - 6w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 2w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  )
  |> Q.INST [`a` |-> `if b then x else y`, `mem` |-> `s.MEM8`]
  |> REWRITE_RULE [cond_rand_thms]
  |> utilsLib.STRIP_UNDISCH

val tac =
  lrw [select_def, alignmentTheory.aligned_extract]
  \\ fs []
  >| [
    `(2 >< 0) x : word3 = 0w` by blastLib.FULL_BBLAST_TAC,
    `(2 >< 0) y : word3 = 0w` by blastLib.FULL_BBLAST_TAC,
    wordsLib.Cases_on_word_value `(2 >< 0) x : word3`,
    wordsLib.Cases_on_word_value `(2 >< 0) y : word3`
  ]
  \\ simp []
  \\ blastLib.BBLAST_TAC

val aligned_select_byte_s = Q.prove(
  `(if aligned 3 (if b then (x: word64) else y) then
      s_extend8 w0
    else
      s_extend8
        ((63 >< 0)
           (((w1: word64) @@ w0) >>
             (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
    s_extend8 (select (if b then (2 >< 0) x else (2 >< 0) y : word3) w0)`,
  tac
  )

val aligned_select_byte_z = Q.prove(
  `(if aligned 3 (if b then (x: word64) else y) then
      z_extend8 w0
    else
      z_extend8
        ((63 >< 0)
           (((w1: word64) @@ w0) >>
             (w2n (if b then (2 >< 0) x else (2 >< 0) y : word3) * 8)))) =
    z_extend8 (select (if b then (2 >< 0) x else (2 >< 0) y : word3) w0)`,
  tac
  )

val select_byte = Q.prove(
  `((7 >< 0)
      (select ((2 >< 0) a : word3)
        (mem ((63 '' 3) a + 7w) @@
         mem ((63 '' 3) a + 6w) @@
         mem ((63 '' 3) a + 5w) @@
         mem ((63 '' 3) a + 4w) @@
         mem ((63 '' 3) a + 3w) @@
         mem ((63 '' 3) a + 2w) @@
         mem ((63 '' 3) a + 1w) @@
         mem ((63 '' 3) a     )) : word64) =
    ((mem: word64 -> word8) a))`,
  lrw [alignmentTheory.aligned_extract, select_def]
  \\ wordsLib.Cases_on_word_value `(2 >< 0) a : word3`
  >| [
    `(63 '' 3) a = a - 7w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 6w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 5w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 3w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 2w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a - 1w` by blastLib.FULL_BBLAST_TAC,
    `(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC
  ]
  \\ simp []
  \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  )
  |> Q.INST [`a` |-> `if b then x else y`, `mem` |-> `s.MEM8`]
  |> REWRITE_RULE [cond_rand_thms]

val byte_access = Q.prove(
  `w2n ((2 >< 0) a : word3) + 1 <= 8`,
  wordsLib.n2w_INTRO_TAC 4
  \\ blastLib.FULL_BBLAST_TAC
  )

val aligned1_aligned3 = uprove
  `aligned 1 (a: word64) ==> (aligned 3 a = ((2 >< 1) a = 0w: word2))`
  (simp [alignmentTheory.aligned_extract] \\ blastLib.BBLAST_TAC)

val aligned1_aligned3b = uprove
  `aligned 1 (a: word64) ==> w2n ((2 >< 0) a : word3) + 2 <= 8`
  (
  rw [alignmentTheory.aligned_extract]
  \\ wordsLib.n2w_INTRO_TAC 4
  \\ blastLib.FULL_BBLAST_TAC
  )

val aligned2_aligned3 = uprove
  `aligned 2 (a: word64) ==> (aligned 3 a = ((2 >< 2) a = 0w: word1))`
  (simp [alignmentTheory.aligned_extract] \\ blastLib.BBLAST_TAC)

val aligned2_aligned3b = uprove
  `aligned 2 (a: word64) ==> w2n ((2 >< 0) a : word3) + 4 <= 8`
  (
  rw [alignmentTheory.aligned_extract]
  \\ wordsLib.n2w_INTRO_TAC 4
  \\ blastLib.FULL_BBLAST_TAC
  )

val w =
  List.tabulate (8, fn i => Term.mk_var ("b" ^ Int.toString i, ``:word8``))
val w = List.foldl wordsSyntax.mk_word_concat (hd w) (tl w)

val extract_thms = Q.prove(
  `((7  >< 0 ) ^w = b0) /\ ((15 >< 8 ) ^w = b1) /\ ((23 >< 16) ^w = b2) /\
   ((31 >< 24) ^w = b3) /\ ((39 >< 32) ^w = b4) /\ ((47 >< 40) ^w = b5) /\
   ((55 >< 48) ^w = b6) /\ ((63 >< 56) ^w = b7)`,
  simp_tac (std_ss++wordsLib.SIZES_ss++wordsLib.WORD_EXTRACT_ss)
    [wordsTheory.SHIFT_ZERO, wordsTheory.WORD_OR_CLAUSES]
  )

val not1 = uprove
  `a <> 1w: word2 ==>
    ((if a = 0w then x1
      else if a = 2w then x2
      else if a = 3w then x3
      else x4) =
     (if a = 0w then x1
      else if a = 2w then x2
      else x3))`
  (rw [] \\ blastLib.FULL_BBLAST_TAC)

val extract_over_add =
  wordsTheory.WORD_EXTRACT_OVER_ADD
  |> Q.ISPECL [`a: word64`, `b: word64`, `31n`]
  |> INST_TYPE [Type.beta |-> ``:32``]
  |> SIMP_RULE (srw_ss()) []
  |> GSYM

val jal = uprove
  `aligned 2 (pc: word64) /\ ~word_lsb (imm: word20) ==>
   aligned 2 (pc + sw2sw imm << 1)`
  (
  simp [alignmentTheory.aligned_extract] \\ blastLib.BBLAST_TAC
  )

val jalr = uprove
  `(b \/ aligned 2 x) /\ ~(imm: word12 ' 1) ==>
   aligned 2 (if b then sw2sw imm && 0xFFFFFFFFFFFFFFFEw : word64
              else x + sw2sw imm && 0xFFFFFFFFFFFFFFFEw)`
  (
  rw [alignmentTheory.aligned_extract]
  \\ blastLib.FULL_BBLAST_TAC
  )

val Decode_IMP_DecodeAny = store_thm("Decode_IMP_DecodeAny",
  ``(Decode w = i) ==> (DecodeAny (Word w) = i)``,
  fs [DecodeAny_def]);

val DecodeRVC_IMP_DecodeAny = store_thm("DecodeRVC_IMP_DecodeAny",
  ``(DecodeRVC h = i) ==> (DecodeAny (Half h) = i)``,
  fs [DecodeAny_def]);

val avoid_signalAddressException = store_thm("avoid_signalAddressException",
  ``~b ==> ((if b then signalAddressException t u else s) = s)``,
  fs []);

val word_bit_add_lsl_simp = store_thm("word_bit_add_lsl_simp",
  ``word_bit 0 (x + w << 1) = word_bit 0 (x:word64)``,
  blastLib.BBLAST_TAC);

(* ------------------------------------------------------------------------
   Evaluation setup
   ------------------------------------------------------------------------ *)

val s = ``s:riscv_state``
val rd0 = ``rd = 0w: word5``
val bare = ``(^s.c_MCSR ^s.procID).mstatus.VM = 0w``
val archbase = ``(^s.c_MCSR ^s.procID).mcpuid.ArchBase``
val shift = ``~((^archbase = 0w) /\ word_bit 5n (imm: word6))``
val aligned = ``aligned 2 (^s.c_PC ^s.procID)``
val aligned_d =
  ``aligned 3 (if rs1 = 0w then sw2sw offs
               else ^s.c_gpr ^s.procID rs1 + sw2sw (offs:word12))``

local
  val cond_updates = utilsLib.mk_cond_update_thms [``:riscv_state``]
  val datatype_rwts =
    utilsLib.datatype_rewrites true "riscv"
      ["riscv_state", "VM_Mode", "Architecture"]
  fun riscv_thms thms =
    thms @ cond_updates @ datatype_rwts @
    [wordsTheory.WORD_EXTRACT_ZERO2, wordsTheory.ZERO_SHIFT,
     wordsTheory.WORD_ADD_0, wordsTheory.WORD_MULT_CLAUSES,
     wordsTheory.WORD_AND_CLAUSES, wordsTheory.WORD_OR_CLAUSES,
     wordsTheory.WORD_XOR_CLAUSES, wordsTheory.w2w_0, wordsTheory.sw2sw_0,
     ifTF, cond_lem1, extract_over_add, cond_rand_shift, cond_rand_thms
     ]
in
  fun step_conv b =
    utilsLib.setStepConv
       (if b then
          Conv.DEPTH_CONV wordsLib.SIZES_CONV
          THENC utilsLib.WGROUND_CONV
        else
          ALL_CONV)
  val ev = utilsLib.STEP (riscv_thms, s)
  fun EV a b c d = hd (ev a b c d)
end

local
  val word_eq_ss =
    simpLib.std_conv_ss
      {name = "word_eq", conv = wordsLib.word_EQ_CONV,
       pats = [``n2w a = n2w b: word64``]}
in
  val store_tac =
    asm_simp_tac (std_ss++wordsLib.WORD_ss)
       [GSYM wordsTheory.WORD_EXTRACT_OVER_BITWISE, extract_thms]
    \\ simp_tac (std_ss++wordsLib.SIZES_ss++wordsLib.WORD_EXTRACT_ss)
         [wordsTheory.SHIFT_ZERO, wordsTheory.WORD_OR_CLAUSES]
    \\ simp_tac
         (std_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_CANCEL_ss++word_eq_ss)
         [updateTheory.UPDATE_APPLY_IMP_ID, combinTheory.UPDATE_APPLY]
end

(* ------------------------------------------------------------------------
   Architecture Rewrites
   ------------------------------------------------------------------------ *)

val () = step_conv false

val translateAddr = EV
  [translateAddr_def, MCSR_def, vmType_def, pairTheory.pair_case_thm]
  [[bare]] []
  ``translateAddr (vPC, ft, ac)``

val in32BitMode = EV
  [in32BitMode_def, curArch_def, MCSR_def, architecture_def, not1] [] []
  ``in32BitMode()``

val PC = EV [PC_def] [] [] ``PC``

val Skip = save_thm("Skip",EV [Skip_def,boolify8_def] [] [] ``Skip``);

val rawReadInst = EV
  [rawReadInst_def, MEM_def, address_align, read_word] [] []
  ``rawReadInst a``

val rawReadData = EV
  [rawReadData_def, aligned3, MEM_def, address_align, address_align2]
  [] []
  ``rawReadData a``

val branchTo = EV
  [branchTo_def, write'NextFetch_def] [] []
  ``branchTo newPC``

val GPR = EV [GPR_def, gpr_def] [] [] ``GPR n``

val write'GPR0 =
  ev [write'GPR_def] [[``d = 0w:word5``]] []
  ``write'GPR (n, d)`` |> hd

val write'GPR =
  ev [write'GPR_def, write'gpr_def] [[``d <> 0w:word5``]] []
  ``write'GPR (n, d)`` |> hd

val update_pc = Theory.save_thm("update_pc",
  EV [update_pc_def, write'PC_def] [] [] ``update_pc v``)

val Fetch =
  EV [Fetch_def, PC, translateAddr, rawReadInst, boolify8_def,
      write'Skip_def] [[aligned]] []
    ``Fetch``

val Fetch32 = store_thm("Fetch32",
  ``!xs x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF
        y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 yA yB yC yD yE yF.
       (xs = [y0; y1; y2; y3; y4; y5; y6; y7; y8; y9; yA; yB; yC; yD; yE; yF;
              x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; xA; xB; xC; xD; xE; xF]) /\
       ((s.c_MCSR s.procID).mstatus.VM = 0w) ∧
       (s.MEM8 (s.c_PC s.procID + 3w) = v2w [y0; y1; y2; y3; y4; y5; y6; y7]) ∧
       (s.MEM8 (s.c_PC s.procID + 2w) = v2w [y8; y9; yA; yB; yC; yD; yE; yF]) ∧
       (s.MEM8 (s.c_PC s.procID + 1w) = v2w [x0; x1; x2; x3; x4; x5; x6; x7]) ∧
       (s.MEM8 (s.c_PC s.procID) = v2w [x8; x9; xA; xB; xC; xD; xE; xF]) ∧
       xE ∧ xF ⇒
       (Fetch s =
        (Word (v2w xs), s with c_Skip := (s.procID =+ 4w) s.c_Skip))``,
  simp [Fetch |> DISCH_ALL] \\ rw [] \\ blastLib.BBLAST_TAC);

val Fetch16 = store_thm("Fetch16",
  ``!xs x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF.
       (xs = [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; xA; xB; xC; xD; xE; xF]) /\
       ((s.c_MCSR s.procID).mstatus.VM = 0w) ∧
       (s.MEM8 (s.c_PC s.procID + 1w) = v2w [x0; x1; x2; x3; x4; x5; x6; x7]) ∧
       (s.MEM8 (s.c_PC s.procID) = v2w [x8; x9; xA; xB; xC; xD; xE; xF]) ∧
       ~(xE ∧ xF) ⇒
       (Fetch s =
        (Half (v2w xs), s with c_Skip := (s.procID =+ 2w) s.c_Skip))``,
  simp [Fetch |> DISCH_ALL] \\ rw [] \\ blastLib.BBLAST_TAC);

(* ------------------------------------------------------------------------
   Memory Store Rewrites
   ------------------------------------------------------------------------ *)

val () = step_conv true

val write'MEM = EV [write'MEM_def] [] [] ``write'MEM (d, a)``

fun write_data_ev l1 l2 =
  EV ([rawWriteData_def, aligned3, MEM_def, write'MEM, address_align] @ l1) l2
     []

val rawWriteData8 =
  write_data_ev [address_aligned3] [[``aligned 3 (a: word64)``]]
  ``rawWriteData (a, d, 8)``

fun get_mem8 thm =
  thm |> utilsLib.rhsc
      |> boolSyntax.rator
      |> boolSyntax.rand
      |> boolSyntax.rand

val rawWriteData4 = write_data_ev [aligned2_aligned3, aligned2_aligned3b] []
  ``rawWriteData (a, d, 4)``

val tm = get_mem8 rawWriteData4

val thm = uprove
  `aligned 2 a ==>
   (^tm = (a =+ (7 >< 0) d) ((a + 1w =+ (15 >< 8) d)
             ((a + 2w =+ (23 >< 16) d) ((a + 3w =+ (31 >< 24) d) s.MEM8))))`
  (
  rw [alignmentTheory.aligned_extract]
  \\ qabbrev_tac `mem = s.MEM8`
  >- (`(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC \\ store_tac)
  \\ `(2 >< 0) a : word3 = 4w: word3` by blastLib.FULL_BBLAST_TAC
  \\ `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC
  \\ store_tac
  )

val rawWriteData4 = utilsLib.INST_REWRITE_RULE [thm] rawWriteData4

val rawWriteData2 = write_data_ev [aligned1_aligned3, aligned1_aligned3b] []
  ``rawWriteData (a, d, 2)``

val tm = get_mem8 rawWriteData2

val thm = uprove
  `aligned 1 a ==> (^tm = (a =+ (7 >< 0) d) ((a + 1w =+ (15 >< 8) d) s.MEM8))`
  (
  rw [alignmentTheory.aligned_extract]
  \\ qabbrev_tac `mem = s.MEM8`
  >- (`(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC \\ store_tac)
  \\ `(2 >< 0) a : word3 IN {2w; 4w; 6w: word3}`
  by (simp [] \\ blastLib.FULL_BBLAST_TAC)
  \\ fs []
  >| [
     `(63 '' 3) a = a - 2w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 6w` by blastLib.FULL_BBLAST_TAC
  ]
  \\ store_tac
  )

val rawWriteData2 = utilsLib.INST_REWRITE_RULE [thm] rawWriteData2

val rawWriteData1 = write_data_ev [byte_access] [] ``rawWriteData (a, d, 1)``

val tm = get_mem8 rawWriteData1

val thm = Q.prove(
  `^tm = (a =+ (7 >< 0) d) s.MEM8`,
  rw [alignmentTheory.aligned_extract]
  \\ qabbrev_tac `mem = s.MEM8`
  >- (`(63 '' 3) a = a` by blastLib.FULL_BBLAST_TAC \\ store_tac)
  \\ wordsLib.Cases_on_word_value `(2 >< 0) a: word3`
  \\ fs []
  >| [
     `(63 '' 3) a = a - 7w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 6w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 5w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 4w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 3w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 2w` by blastLib.FULL_BBLAST_TAC,
     `(63 '' 3) a = a - 1w` by blastLib.FULL_BBLAST_TAC,
     blastLib.FULL_BBLAST_TAC
  ]
  \\ store_tac
  )

val rawWriteData1 = REWRITE_RULE [thm] rawWriteData1

(* ------------------------------------------------------------------------
   Instruction Rewrites
   ------------------------------------------------------------------------ *)

local
  val l =
    [GPR, in32BitMode, PC, wordsTheory.word_len_def,
     branchTo, translateAddr, jal, jalr, aligned2,
     aligned_select_word_s, aligned_select_word_z, select_word,
     aligned_select_half_s, aligned_select_half_z, select_half,
     aligned_select_byte_s, aligned_select_byte_z, select_byte,
     rawReadData, rawWriteData8, rawWriteData4, rawWriteData2, rawWriteData1]
  val hyp_eq_rule =
    utilsLib.ALL_HYP_CONV_RULE (Conv.DEPTH_CONV wordsLib.word_EQ_CONV)
in
  val () = utilsLib.reset_thms()
  fun class args avoid n =
    let
      val name = "dfn'" ^ n
      val read = if Lib.mem n ["LD"] then [address_aligned3] else []
      val (write, n) =
        if List.exists (tmem rd0) avoid then
          ([write'GPR0], n ^ "_NOP")
        else
          ([write'GPR], n)
      val thms = DB.fetch "riscv" (name ^ "_def") :: write @ read
    in
      case ev (thms @ l) avoid [] (Parse.Term ([QUOTE name] @ args)) of
         [th] => utilsLib.save_thms n [hyp_eq_rule th]
       | _ => raise ERR "class" ("more than one theorem" ^ n)
    end
end

fun class_rd0 args avoid n =
  let
    val f = class args
  in
    (f avoid n,
     f (case avoid of
          [] => [[rd0]]
        | [l] => [rd0 :: l]
        | _ => raise ERR "" "") n)
  end

val arithi = class_rd0 `(rd, rs1, imm)`

val ADDI  = arithi [] "ADDI"
val ADDIW = arithi [[``^archbase <> 0w``]] "ADDIW"
val SLTI  = arithi [] "SLTI"
val SLTIU = arithi [] "SLTIU"
val ANDI  = arithi [] "ANDI"
val ORI   = arithi [] "ORI"
val XORI  = arithi [] "XORI"
val SLLI  = arithi [[shift]] "SLLI"
val SRLI  = arithi [[shift]] "SRLI"
val SRAI  = arithi [[shift]] "SRAI"
val SLLIW = arithi [[``^archbase <> 0w``]] "SLLIW"
val SRLIW = arithi [[``^archbase <> 0w``]] "SRLIW"
val SRAIW = arithi [[``^archbase <> 0w``]] "SRAIW"

val arithi = class_rd0 `(rd, imm)` []

val LUI   = arithi "LUI"
val AUIPC = arithi "AUIPC"

val arithr = class_rd0 `(rd, rs1, rs2)`

val ADD   = arithr [] "ADD"
val ADDW  = arithr [[``^archbase <> 0w``]] "ADDW"
val SUB   = arithr [] "SUB"
val SUBW  = arithr [[``^archbase <> 0w``]] "SUBW"
val SLT   = arithr [] "SLT"
val SLTU  = arithr [] "SLTU"
val AND   = arithr [] "AND"
val OR    = arithr [] "OR"
val XOR   = arithr [] "XOR"
val SLL   = arithr [] "SLL"
val SRL   = arithr [] "SRL"
val SRA   = arithr [] "SRA"
val SLLW  = arithr [[``^archbase <> 0w``]] "SLLW"
val SRLW  = arithr [[``^archbase <> 0w``]] "SRLW"
val SRAW  = arithr [[``^archbase <> 0w``]] "SRAW"

val MUL    = arithr [] "MUL"
val MULH   = arithr [] "MULH"
val MULHU  = arithr [] "MULHU"
val MULHSU = arithr [] "MULHSU"
val MULW   = arithr [[``^archbase <> 0w``]] "MULW"
val DIV    = arithr [] "DIV"
val REM    = arithr [] "REM"
val DIVU   = arithr [] "DIVU"
val REMU   = arithr [] "REMU"
val DIVW   = arithr [[``^archbase <> 0w``]] "DIVW"
val REMW   = arithr [[``^archbase <> 0w``]] "REMW"
val DIVUW  = arithr [[``^archbase <> 0w``]] "DIVUW"
val REMUW  = arithr [[``^archbase <> 0w``]] "REMUW"

val JAL  = class_rd0 `(rd, imm)` [] "JAL"
val JALR = class_rd0 `(rd, rs1, imm)` [] "JALR"

val cbranch = class `(rs1, rs2, offs)` []

val BEQ  = cbranch "BEQ"
val BNE  = cbranch "BNE"
val BLT  = cbranch "BLT"
val BLTU = cbranch "BLTU"
val BGE  = cbranch "BGE"
val BGEU = cbranch "BGEU"

val load = class_rd0 `(rd, rs1, offs)`

val LD  = load [[``^archbase <> 0w``, aligned_d]] "LD"
val LW  = load [] "LW"
val LH  = load [] "LH"
val LB  = load [] "LB"
val LWU = load [[``^archbase <> 0w``]] "LWU"
val LHU = load [[``^archbase <> 0w``]] "LHU"
val LBU = load [[``^archbase <> 0w``]] "LBU"

val store = class `(rs1, rs2, offs)`

val SD  = store [[``^archbase <> 0w``, aligned_d]] "SD"
val SW  = store [] "SW"
val SH  = store [] "SH"
val SB  = store [] "SB"

(* ------------------------------------------------------------------------ *)

val () = ( Theory.delete_const "select"
         ; utilsLib.adjoin_thms ()
         ; export_theory ()
         )
