(* ------------------------------------------------------------------------
   Definitions and theorems used by MIPS step evaluator (mips_stepLib)
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib

open utilsLib
open wordsLib blastLib
open alignmentTheory mipsTheory

val _ = new_theory "mips_step"

(* ------------------------------------------------------------------------ *)

val _ = List.app (fn f => f ())
   [numLib.prefer_num, wordsLib.prefer_word, wordsLib.guess_lengths]

(* ------------------------------------------------------------------------ *)

val NextStateMIPS_def = Define`
   NextStateMIPS s0 =
   let s1 = Next s0 in if s1.exception = NoException then SOME s1 else NONE`

val exceptionSignalled_id = Q.prove(
   `!s. ~s.exceptionSignalled ==> (s with exceptionSignalled := F = s)`,
   lrw [mips_state_component_equality])

val tac =
   lrw [NextStateMIPS_def, Next_def, AddressTranslation_def,
        exceptionSignalled_id]
   \\ Cases_on `(Run (Decode w) s).BranchTo`
   \\ Cases_on `(Run (Decode w) s).BranchDelay`
   \\ TRY (Cases_on `x`)
   \\ lrw []
   \\ fs [mips_state_component_equality]

val NextStateMIPS_nodelay = utilsLib.ustore_thm("NextStateMIPS_nodelay",
    `(s.exception = NoException) /\
     (s.BranchDelay = NONE) /\
     ~s.exceptionSignalled ==>
     (Fetch s = (SOME w, s)) /\
     (Decode w = i) /\
     (Run i s = next_state) /\
     (next_state.exception = s.exception) /\
     (next_state.BranchDelay = NONE) /\
     (next_state.BranchTo = b) ==>
     (NextStateMIPS s =
      SOME (next_state with
               <| PC := case b of SOME (T, a) => a | _ => next_state.PC + 4w;
                  BranchDelay := case b of SOME (F, a) => SOME (SOME a)
                                         | SOME (T, _) => SOME NONE
                                         | _ => NONE;
                  BranchTo := NONE;
                  exceptionSignalled := F;
                  CP0 := next_state.CP0 with
                         Count := next_state.CP0.Count + 1w |>))`,
    tac
    )

val NextStateMIPS_delay = utilsLib.ustore_thm("NextStateMIPS_delay",
    `(s.exception = NoException) /\
     (s.BranchDelay = SOME d) /\
     ~s.exceptionSignalled ==>
     (Fetch s = (SOME w, s)) /\
     (Decode w = i) /\
     (Run i s = next_state) /\
     (next_state.exception = s.exception) /\
     (next_state.BranchDelay = s.BranchDelay) /\
     (next_state.BranchTo = NONE) ==>
     (NextStateMIPS s =
      SOME (next_state with
            <| PC := case d of SOME a => a | NONE => next_state.PC + 4w;
               BranchDelay := NONE;
               exceptionSignalled := F;
               CP0 := next_state.CP0 with
                      Count := next_state.CP0.Count + 1w |>))`,
    tac
    )

(* exceptions can occur in the branch delay slot *)
val NextStateMIPS_exception = utilsLib.ustore_thm("NextStateMIPS_exception",
    `(s.exception = NoException) /\
     (s.BranchDelay = SOME d) /\
     ~s.exceptionSignalled ==>
     (Fetch s = (SOME w, s)) /\
     (Decode w = i) /\
     (Run i s = next_state) /\
     (next_state.exception = s.exception) /\
     (next_state.BranchDelay = if b then NONE else s.BranchDelay) /\
     (next_state.BranchTo = NONE) ==>
     (NextStateMIPS s =
      SOME (next_state with
            <| PC := if b then
                        next_state.PC + 4w
                     else
                        (case d of SOME a => a | NONE => next_state.PC + 4w);
               BranchDelay := NONE;
               exceptionSignalled := F;
               CP0 := next_state.CP0 with
                      Count := next_state.CP0.Count + 1w |>))`,
    tac
    )

(* ------------------------------------------------------------------------ *)

val not31 = Q.store_thm("not31",
   `x0 /\ x1 /\ x2 /\ x3 /\ x4 = (v2w [x0; x1; x2; x3; x4] = (31w: word5))`,
   blastLib.BBLAST_TAC
   )

val v2w_0_rwts = Q.store_thm("v2w_0_rwts",
   `((v2w [F; F; F; F; F] = 0w: word5)) /\
    ((v2w [T; b3; b2; b1; b0] = 0w: word5) = F) /\
    ((v2w [b3; T; b2; b1; b0] = 0w: word5) = F) /\
    ((v2w [b3; b2; T; b1; b0] = 0w: word5) = F) /\
    ((v2w [b3; b2; b1; T; b0] = 0w: word5) = F) /\
    ((v2w [b3; b2; b1; b0; T] = 0w: word5) = F)`,
    blastLib.BBLAST_TAC
    )

val NotWordValue0 = Q.store_thm("NotWordValue0",
   `!b x. ~NotWordValue 0w`,
   lrw [NotWordValue_def]
   )

val NotWordValueCond = Q.store_thm("NotWordValueCond",
   `!b x. NotWordValue (if b then 0w else x) = ~b /\ NotWordValue x`,
   lrw [NotWordValue0]
   )

val sw16_to_sw64 = Q.store_thm("sw16_to_sw64",
   `!a:word16. sw2sw (sw2sw a : word32) = sw2sw a : word64`,
   rw [wordsTheory.sw2sw_sw2sw]
   )

val get_bytes = Q.store_thm("get_bytes",
   `((31 >< 24)
       (v2w [b31; b30; b29; b28; b27; b26; b25; b24;
             b23; b22; b21; b20; b19; b18; b17; b16;
             b15; b14; b13; b12; b11; b10; b9;  b8;
             b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word32) =
     v2w [b31; b30; b29; b28; b27; b26; b25; b24]: word8) /\
    ((23 >< 16)
       (v2w [b31; b30; b29; b28; b27; b26; b25; b24;
             b23; b22; b21; b20; b19; b18; b17; b16;
             b15; b14; b13; b12; b11; b10; b9;  b8;
             b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word32) =
     v2w [b23; b22; b21; b20; b19; b18; b17; b16]: word8) /\
    ((15 >< 8)
       (v2w [b31; b30; b29; b28; b27; b26; b25; b24;
             b23; b22; b21; b20; b19; b18; b17; b16;
             b15; b14; b13; b12; b11; b10; b9;  b8;
             b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word32) =
     v2w [b15; b14; b13; b12; b11; b10; b9;  b8]: word8) /\
    ((7 >< 0)
       (v2w [b31; b30; b29; b28; b27; b26; b25; b24;
             b23; b22; b21; b20; b19; b18; b17; b16;
             b15; b14; b13; b12; b11; b10; b9;  b8;
             b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word32) =
     v2w [b7;  b6;  b5;  b4;  b3;  b2;  b1;  b0]: word8)`,
   blastLib.BBLAST_TAC
   )

val cast_thms = Q.store_thm("cast_thms",
   `!w: word32. sw2sw ((31 >< 0) (w2w w : word64) : word32) = sw2sw w : word64`,
   blastLib.BBLAST_TAC
   )

(* ------------------------------------------------------------------------ *)

val tac =
   wordsLib.Cases_word_value
   \\ simp []
   \\ ntac 2 strip_tac
   \\ blastLib.BBLAST_TAC

val select_byte_le = Q.store_thm("select_byte_le",
   `!b:word3 a:word64 f:word64->word8.
      (7 + 8 * w2n b >< 8 * w2n b)
      (f (a + 7w) @@
       f (a + 6w) @@
       f (a + 5w) @@
       f (a + 4w) @@
       f (a + 3w) @@
       f (a + 2w) @@
       f (a + 1w) @@
       f a) = f (a + w2w b)`,
   tac
   )

val select_byte_be = Q.store_thm("select_byte_be",
   `!b:word3 a:word64 f:word64->word8.
      (7 + 8 * w2n b >< 8 * w2n b)
      (f a @@
       f (a + 1w) @@
       f (a + 2w) @@
       f (a + 3w) @@
       f (a + 4w) @@
       f (a + 5w) @@
       f (a + 6w) @@
       f (a + 7w)) = f (a + w2w (b ?? 7w))`,
   tac
   )

val select_half_le = Q.prove(
   `!b:word3 f:word64->word8 a:word64.
     ~word_bit 0 b ==>
     ((15 + 8 * w2n b >< 8 * w2n b)
      (f (a + 7w) @@
       f (a + 6w) @@
       f (a + 5w) @@
       f (a + 4w) @@
       f (a + 3w) @@
       f (a + 2w) @@
       f (a + 1w) @@
       f a) = (f (a + w2w b + 1w) @@ f (a + w2w b)) : word16)`,
   tac
   )

val select_half_be = Q.prove(
   `!b:word3 f:word64->word8 a:word64.
     ~word_bit 0 b ==>
     ((15 + 8 * w2n b >< 8 * w2n b)
      (f a @@
       f (a + 1w) @@
       f (a + 2w) @@
       f (a + 3w) @@
       f (a + 4w) @@
       f (a + 5w) @@
       f (a + 6w) @@
       f (a + 7w)) =
     (f (a + w2w (b ?? 6w)) @@ f (a + w2w (b ?? 6w) + 1w)) : word16)`,
   tac
   )

val select_word_le = Q.prove(
   `!b:word3 f:word64->word8 a:word64.
     ((1 >< 0) b = 0w:word2) ==>
     ((31 + 8 * w2n b >< 8 * w2n b)
      (f (a + 7w) @@
       f (a + 6w) @@
       f (a + 5w) @@
       f (a + 4w) @@
       f (a + 3w) @@
       f (a + 2w) @@
       f (a + 1w) @@
       f a) =
       (f (a + w2w b + 3w) @@ f (a + w2w b + 2w) @@
        f (a + w2w b + 1w) @@ f (a + w2w b)) : word32)`,
   tac
   )

val select_word_be = Q.prove(
   `!b:word3 f:word64->word8 a:word64.
     ((1 >< 0) b = 0w:word2) ==>
     ((31 + 8 * w2n b >< 8 * w2n b)
      (f a @@
       f (a + 1w) @@
       f (a + 2w) @@
       f (a + 3w) @@
       f (a + 4w) @@
       f (a + 5w) @@
       f (a + 6w) @@
       f (a + 7w)) =
     (f (a + w2w (b ?? 4w)) @@ f (a + w2w (b ?? 4w) + 1w) @@
      f (a + w2w (b ?? 4w) + 2w) @@ f (a + w2w (b ?? 4w) + 3w)) : word32)`,
   tac
   )

val select_parts = Q.store_thm("select_parts",
   `!a0: word8 a1: word8 a2: word8 a3: word8 a4: word8 a5: word8 a6: word8
     a7: word8.
     let w = a7 @@ a6 @@ a5 @@ a4 @@ a3 @@ a2 @@ a1 @@ a0
     in
     ((7 >< 0) w = a0) /\
     ((15 >< 0) w = (a1 @@ a0) : word16) /\
     ((23 >< 0) w = (a2 @@ a1 @@ a0) : word24) /\
     ((31 >< 0) w = (a3 @@ a2 @@ a1 @@ a0) : word32) /\
     ((39 >< 0) w = (a4 @@ a3 @@ a2 @@ a1 @@ a0) : 40 word) /\
     ((47 >< 0) w = (a5 @@ a4 @@ a3 @@ a2 @@ a1 @@ a0) : word48) /\
     ((55 >< 0) w = (a6 @@ a5 @@ a4 @@ a3 @@ a2 @@ a1 @@ a0) : 56 word) /\
     ((63 >< 0) w = w) /\
     ((39 >< 32) w = a4) /\
     ((47 >< 32) w = (a5 @@ a4) : word16) /\
     ((55 >< 32) w = (a6 @@ a5 @@ a4) : word24) /\
     ((63 >< 32) w = (a7 @@ a6 @@ a5 @@ a4) : word32) /\
     ((31 >< 8) w = (a3 @@ a2 @@ a1) : word24) /\
     ((31 >< 16) w = (a3 @@ a2) : word16) /\
     ((31 >< 24) w = a3) /\
     ((63 >< 8) w = (a7 @@ a6 @@ a5 @@ a4 @@ a3 @@ a2 @@ a1) : 56 word) /\
     ((63 >< 16) w = (a7 @@ a6 @@ a5 @@ a4 @@ a3 @@ a2) : word48) /\
     ((63 >< 24) w = (a7 @@ a6 @@ a5 @@ a4 @@ a3) : 40 word) /\
     ((63 >< 32) w = (a7 @@ a6 @@ a5 @@ a4) : word32) /\
     ((63 >< 40) w = (a7 @@ a6 @@ a5) : word24) /\
     ((63 >< 48) w = (a7 @@ a6) : word16) /\
     ((63 >< 56) w = a7 : word8)`,
   SIMP_TAC (srw_ss()++boolSimps.LET_ss++wordsLib.WORD_EXTRACT_ss) []
   )

(* ------------------------------------------------------------------------ *)

val bit_0_2_0 = Theory.save_thm("bit_0_2_0",
   blastLib.BBLAST_PROVE
      ``word_bit 0 (((2 >< 0) (a:word64)) : word3) = word_bit 0 a``
   )

val bit_0_2_0_6 = Theory.save_thm("bit_0_2_0_6",
   blastLib.BBLAST_PROVE
      ``word_bit 0 (((2 >< 0) (a:word64)) : word3 ?? 6w) = word_bit 0 a``
   )

val bit_1_0_2_0 = Theory.save_thm("bit_1_0_2_0",
   blastLib.BBLAST_PROVE
      ``(1 >< 0) (((2 >< 0) (a:word64)) : word3) = ((1 >< 0) a) : word2``
   )

val bit_1_0_2_0_4 = Theory.save_thm("bit_1_0_2_0_4",
   blastLib.BBLAST_PROVE
      ``(1 >< 0) (((2 >< 0) (a:word64)) : word3 ?? 4w) =
        ((1 >< 0) a) : word2``
   )

val st = ``s:mips_state``
val addr = ``sw2sw (offset:word16) + if base = 0w then 0w else ^st.gpr base``

local
   val tm_le = ``(2 >< 0) ^addr : word3``
   val pctm_le = ``(2 >< 0) ^st.PC : word3``
   fun select s tm thm =
      Theory.save_thm(s,
        (Drule.UNDISCH o
         REWRITE_RULE
            [wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_XOR_CLAUSES,
             bit_0_2_0, bit_0_2_0_6, bit_1_0_2_0, bit_1_0_2_0_4] o
         Drule.SPECL [tm, ``^st.MEM``, ``a:word64``]) thm)
in
   val select_half_le = select "select_half_le" tm_le select_half_le
   val select_half_be = select "select_half_be" ``^tm_le ?? 6w`` select_half_be
   val select_pc_le = select "select_pc_le" pctm_le select_word_le
   val select_pc_be = select "select_pc_be" ``^pctm_le ?? 4w`` select_word_be
   val select_word_le = select "select_word_le" tm_le select_word_le
   val select_word_be = select "select_word_be" ``^tm_le ?? 4w`` select_word_be
end

val address_align = Q.store_thm("address_align",
  `!a:word64 b:word3.
      ((((63 >< 3) a) : 61 word) @@ (b : word3)) && ~7w = a && ~7w`,
  blastLib.BBLAST_TAC)

val address_align2 = Q.store_thm("address_align2",
  `!a:word64. (((63 >< 3) a) : 61 word) @@ ((2 >< 0) a : word3) = a`,
  blastLib.BBLAST_TAC)

val cond_sign_extend = Q.store_thm("cond_sign_extend",
   `!a b. (if b then w2w a else sw2sw a) = (if b then w2w else sw2sw) a`,
   rw [])

val byte_address = Q.store_thm("byte_address",
   `!a:word64. (a && ~7w) + w2w (((2 >< 0) a) : word3) = a`,
   blastLib.BBLAST_TAC)

val double_aligned = Theory.save_thm("double_aligned",
   blastLib.BBLAST_PROVE
      ``!a:word64. ((2 >< 0) a = 0w:word3) ==> (a && ~7w = a)``
   |> Thm.SPEC addr
   |> Drule.UNDISCH
   )

val Aligned_thms = Q.store_thm("Aligned_thms",
  `(!w. Aligned (w, 1w) = aligned 1 w) /\
   (!w: word64. ~word_bit 0 w = aligned 1 w) /\
   (!w. Aligned (w, 3w) = aligned 2 w) /\
   (!w: word64. ((1 >< 0) w = 0w: word2) = aligned 2 w) /\
   (!w. Aligned (w, 7w) = aligned 3 w) /\
   (!w: word64. ((2 >< 0) w = 0w: word3) = aligned 3 w)
   `,
  rw [Aligned_def, alignmentTheory.aligned_bitwise_and]
  \\ blastLib.BBLAST_TAC
  )

(* ------------------------------------------------------------------------ *)

(* ------
   Theorems of the form
   |- !w b. ((7 + x) + 8 * w2n b >< x + 8 * w2n b) (w << (8 * w2n b)) =
            (7 + x >< x) w
   ------ *)
local
   fun try_undisch thm = Option.getOpt (Lib.total Drule.UNDISCH thm, thm)
   val undisch_conjuncts =
      List.map (try_undisch o Drule.SPEC_ALL) o Drule.CONJUNCTS
   val tac =
      REPEAT conj_tac
      \\ wordsLib.Cases_word_value
      \\ EVAL_TAC
   val hlem = Q.prove(
      `!b:word3. ~word_bit 0 b ==> 15 + 8 * w2n b < 64`,
      tac
      )
   val wlem = Q.prove(
      `(!b:word3. ((1 >< 0) b = 0w: word2) ==> 15 + 8 * w2n b < 64) /\
       (!b:word3. ((1 >< 0) b = 0w: word2) ==> 23 + 8 * w2n b < 64) /\
       (!b:word3. ((1 >< 0) b = 0w: word2) ==> 31 + 8 * w2n b < 64)`,
      tac
      )
   val tm = ``8 * w2n (b:word3)``
   fun ebyte thm i =
      let
         val a = numSyntax.mk_plus (numLib.term_of_int i, tm)
         val b = numSyntax.mk_plus (numLib.term_of_int (i + 7), tm)
      in
         wordsTheory.WORD_EXTRACT_LSL
         |> Drule.ISPECL [b, a, tm, ``w:word64``]
         |> SIMP_RULE (srw_ss()) [DECIDE ``a - (b + a) = 0n``]
         |> REWRITE_RULE (undisch_conjuncts thm)
      end
in
   val extract_byte = Theory.save_thm("extract_byte",
      ebyte (wordsLib.WORD_DECIDE ``7 + 8 * w2n (b:word3) < 64``) 0)
   val extract_half = Theory.save_thm("extract_half",
      Drule.LIST_CONJ (List.map (ebyte hlem) [8]))
   val extract_word = Theory.save_thm("extract_word",
      Drule.LIST_CONJ (List.map (ebyte wlem) [8, 16, 24]))
end

(* ------------------------------------------------------------------------ *)

val StoreMemory =
   StoreMemory_def
   |> Drule.SPEC_ALL
   |> Conv.CONV_RULE (Conv.X_FUN_EQ_CONV st)
   |> Thm.SPEC st
   |> Conv.RIGHT_CONV_RULE PairedLambda.GEN_BETA_CONV

val ls_thm =
   wordsLib.WORD_DECIDE ``!a b:'a word. a <=+ b /\ b <=+ a = (a = b)``

val ls_lem =
   blastLib.BBLAST_PROVE
     ``((2 >< 0) (a: word64) = (b: word3)) /\ (w2w b = c) ==>
       ((0xFFFFFFFFFFFFFFF8w && a) + c = a)``

val ls_lem0 =
   SIMP_RULE (srw_ss()) [] (Q.INST [`b` |-> `0w`, `c` |-> `0w`] ls_lem)

val ls_lem1 =
   blastLib.BBLAST_PROVE
     ``((2 >< 0) (a: word64) = (b: word3)) /\ (w2w b + 1w = c) ==>
       ((0xFFFFFFFFFFFFFFF8w && a) + c = a + 1w)``

val ls_lem2 =
   blastLib.BBLAST_PROVE
     ``((2 >< 0) (a: word64) = (b: word3)) /\ (w2w b + 2w = c) ==>
       ((0xFFFFFFFFFFFFFFF8w && a) + c = a + 2w)``

val ls_lem3 =
   blastLib.BBLAST_PROVE
     ``((2 >< 0) (a: word64) = (b: word3)) /\ (w2w b + 3w = c) ==>
       ((0xFFFFFFFFFFFFFFF8w && a) + c = a + 3w)``

val ls_lem4 =
   blastLib.BBLAST_PROVE
     ``0xFFFFFFFFFFFFFFF8w && (a ?? w2w (b : word3)) =
       0xFFFFFFFFFFFFFFF8w && a : word64``

val StoreMemory_byte = Q.store_thm("StoreMemory_byte",
   `!s MemElem vAddr.
       ~s.exceptionSignalled ==>
       (StoreMemory (0w,0w,F,MemElem,vAddr,F) s =
        (T, s with
            <|LLbit := NONE;
              MEM :=
                let a = (2 >< 0) vAddr: word3 in
                let b = if BigEndianMem s then a ?? 7w else a in
                let c = 8 * w2n b in
                  (vAddr =+ (7 + c >< c) MemElem) s.MEM|>))`,
   rpt strip_tac
   \\ asm_simp_tac (srw_ss())
        [StoreMemory, AddressTranslation_def, AdjustEndian_def, WriteData_def,
         ls_lem, ls_thm, ls_lem4, wordsTheory.w2w_0, wordsTheory.WORD_ADD_0]
   \\ wordsLib.Cases_on_word_value `(2 >< 0) vAddr: word3`
   \\ lrw [ls_lem, ls_lem0, ls_lem4]
   )

val ls_thm2 =
   blastLib.BBLAST_PROVE
      ``~word_bit 0 (a:word3) ==>
        (a <=+ b /\ b <=+ a + 1w = (a = b) \/ (a + 1w = b))``

val StoreMemory_half = Q.store_thm("StoreMemory_half",
   `Aligned (vAddr,1w) ==> ~s.exceptionSignalled ==>
    (StoreMemory (1w,1w,T,MemElem,vAddr,F) s =
     (T,
      s with
       <|LLbit := NONE;
         MEM :=
           let a = (2 >< 0) vAddr: word3 in
              if BigEndianMem s then
                 let b = 8 * w2n (a ?? 6w) in
                   (vAddr + 1w =+ (7 + b >< b) MemElem)
                     ((vAddr =+ (15 + b >< 8 + b) MemElem) s.MEM)
              else
                 let b = 8 * w2n a in
                   (vAddr + 1w =+ (15 + b >< 8 + b) MemElem)
                     ((vAddr =+ (7 + b >< b) MemElem) s.MEM)|>))`,
   rpt strip_tac
   \\ asm_simp_tac (srw_ss())
        [StoreMemory, AddressTranslation_def, AdjustEndian_def, WriteData_def,
         ls_thm2]
   \\ `~word_bit 0 (((2 >< 0) vAddr) : word3)`
   by (fs [Aligned_def] \\ blastLib.FULL_BBLAST_TAC)
   \\ wordsLib.Cases_on_word_value `(2 >< 0) vAddr: word3`
   \\ fs [ls_lem, ls_lem0, ls_lem1, ls_lem4]
   \\ asm_simp_tac (srw_ss()) []
   \\ lrw []
   )

val ls_thm3 =
   blastLib.BBLAST_PROVE
      ``((1 >< 0) (a:word3) = 0w:word2) ==>
        (a <=+ b /\ b <=+ a + 3w =
        (a = b) \/ (a + 1w = b) \/ (a + 2w = b) \/ (a + 3w = b))``

val StoreMemory_word = Q.store_thm("StoreMemory_word",
   `Aligned (vAddr,3w) ==> ~s.exceptionSignalled ==>
    (StoreMemory (3w,3w,T,MemElem,vAddr,F) s =
     (T,
      s with
       <|LLbit := NONE;
         MEM :=
           let a = (2 >< 0) vAddr: word3 in
              if BigEndianMem s then
                 let b = 8 * w2n (a ?? 4w) in
                   (vAddr + 3w =+ (7 + b >< b) MemElem)
                     ((vAddr + 2w =+ (15 + b >< 8 + b) MemElem)
                        ((vAddr + 1w =+ (23 + b >< 16 + b) MemElem)
                           ((vAddr =+ (31 + b >< 24 + b) MemElem) s.MEM)))
              else
                 let b = 8 * w2n a in
                   (vAddr + 3w =+ (31 + b >< 24 + b) MemElem)
                     ((vAddr + 2w =+ (23 + b >< 16 + b) MemElem)
                        ((vAddr + 1w =+ (15 + b >< 8 + b) MemElem)
                           ((vAddr =+ (7 + b >< b) MemElem) s.MEM)))|>))`,
   rpt strip_tac
   \\ `(1 >< 0) (((2 >< 0) vAddr) : word3) = 0w: word2`
   by (fs [Aligned_def] \\ blastLib.FULL_BBLAST_TAC)
   \\ asm_simp_tac (srw_ss())
        [StoreMemory, AddressTranslation_def, AdjustEndian_def, WriteData_def,
         ls_thm3]
   \\ wordsLib.Cases_on_word_value `(2 >< 0) vAddr: word3`
   \\ fs [ls_lem, ls_lem0, ls_lem1, ls_lem2, ls_lem3, ls_lem4]
   \\ asm_simp_tac (srw_ss()) []
   \\ lrw []
   )

val ls_thm4 =
   blastLib.BBLAST_PROVE
      ``((a:word3) = 0w:word3) ==> (a <=+ b /\ b <=+ a + 7w)``

val StoreMemory_doubleword = Q.store_thm("StoreMemory_doubleword",
   `Aligned (vAddr,7w) ==> ~s.exceptionSignalled ==>
    (StoreMemory (7w,7w,T,MemElem,vAddr,F) s =
     (T,
      s with
       <|LLbit := NONE;
         MEM :=
           if BigEndianMem s then
             (vAddr + 7w =+ (7 >< 0) MemElem)
               ((vAddr + 6w =+ (15 >< 8) MemElem)
                  ((vAddr + 5w =+ (23 >< 16) MemElem)
                     ((vAddr + 4w =+ (31 >< 24) MemElem)
                         ((vAddr + 3w =+ (39 >< 32) MemElem)
                           ((vAddr + 2w =+ (47 >< 40) MemElem)
                              ((vAddr + 1w =+ (55 >< 48) MemElem)
                                 ((vAddr =+ (63 >< 56) MemElem) s.MEM)))))))
           else
             (vAddr + 7w =+ (63 >< 56) MemElem)
               ((vAddr + 6w =+ (55 >< 48) MemElem)
                  ((vAddr + 5w =+ (47 >< 40) MemElem)
                     ((vAddr + 4w =+ (39 >< 32) MemElem)
                        ((vAddr + 3w =+ (31 >< 24) MemElem)
                           ((vAddr + 2w =+ (23 >< 16) MemElem)
                              ((vAddr + 1w =+ (15 >< 8) MemElem)
                                 ((vAddr =+ (7 >< 0) MemElem) s.MEM)))))))|>))`,
   rpt strip_tac
   \\ `(2 >< 0) vAddr = 0w: word3`
   by (fs [Aligned_def] \\ blastLib.FULL_BBLAST_TAC)
   \\ asm_simp_tac (srw_ss())
        [StoreMemory, AddressTranslation_def, AdjustEndian_def, WriteData_def,
         ls_thm4]
   \\ lrw [ls_lem, ls_lem0, ls_lem1, ls_lem2, ls_lem3, ls_lem4]
   )

(* ------------------------------------------------------------------------ *)

val cond_update_memory = Q.store_thm("cond_update_memory",
   `(!a: word64 b x0 x1 x2 x3 m.
       (if b then
          (a + 3w =+ x0) ((a + 2w =+ x1) ((a + 1w =+ x2) ((a =+ x3) m)))
        else m) =
       (a + 3w =+ (if b then x0 else m (a + 3w)))
         ((a + 2w =+ (if b then x1 else m (a + 2w)))
           ((a + 1w =+ (if b then x2 else m (a + 1w)))
             ((a =+ (if b then x3 else m a)) m)))) /\
    (!a: word64 b x0 x1 x2 x3 x4 x5 x6 x7 m.
       (if b then
          (a + 7w =+ x0) ((a + 6w =+ x1) ((a + 5w =+ x2) ((a + 4w =+ x3)
            ((a + 3w =+ x4) ((a + 2w =+ x5) ((a + 1w =+ x6) ((a =+ x7) m)))))))
        else m) =
       (a + 7w =+ (if b then x0 else m (a + 7w)))
         ((a + 6w =+ (if b then x1 else m (a + 6w)))
           ((a + 5w =+ (if b then x2 else m (a + 5w)))
             ((a + 4w =+ (if b then x3 else m (a + 4w)))
               ((a + 3w =+ (if b then x4 else m (a + 3w)))
                 ((a + 2w =+ (if b then x5 else m (a + 2w)))
                   ((a + 1w =+ (if b then x6 else m (a + 1w)))
                     ((a =+ (if b then x7 else m a)) m))))))))`,
   rw [combinTheory.UPDATE_def, FUN_EQ_THM]
   )

(* ------------------------------------------------------------------------ *)

val branch_delay = Q.store_thm("branch_delay",
   `(!b x y.
       (case (if b then (F, x) else (T, y)) of
           (T, a) => SOME NONE
         | (F, a) => SOME (SOME a)) =
       (if b then SOME (SOME x) else SOME NONE)) /\
    (!b x y.
       (case (if b then (F, x) else (T, y)) of
           (T, a) => a
         | (F, a) => y) = y) /\
    (!b x y.
       (if b then
           (case THE (if b then SOME (F, x) else NONE) of
               (T, a) => SOME NONE
             | (F, a) => SOME (SOME a))
        else
           NONE) =
       (if b then SOME (SOME x) else NONE)) /\
    (!b x y.
       (if b then
           (case THE (if b then SOME (F, x) else NONE) of
               (T, a) => a
             | (F, a) => y)
        else
           y) = y) /\
    (!b. (if b then T else F) = b) /\
    (!b x y.
        (if b then x else y) + 4w = (if b then x + 4w else y + 4w)) /\
    (!x. x + 4w + 4w = x + 8w)`,
   rw [] \\ fs [])

(* ------------------------------------------------------------------------ *)


val () = export_theory ()
