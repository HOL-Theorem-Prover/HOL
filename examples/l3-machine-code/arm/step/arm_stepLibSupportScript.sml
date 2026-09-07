(* ------------------------------------------------------------------------
   Theorems used at load time by arm_stepLib.  Landed here so that they
   are proved inside a Script (with a current theory) rather than firing
   Tactical.prove during arm_stepLib's load.

   The Support Script duplicates enough of arm_stepLib's setup (the
   state variable `st`, the datatype-rewrite bundle, and utilsLib's EV
   / STEP) to derive whichever intermediates each Q.prove tactic needs.
   arm_stepLib pulls the saved theorems back via arm_stepLibSupportTheory.
   ------------------------------------------------------------------------ *)
Theory arm_stepLibSupport
Ancestors
  arm_step arm
Libs
  arm_configLib utilsLib wordsLib blastLib bitstringLib

val ambient_grammars = (type_grammar(), term_grammar())
val _ = temp_set_grammars
          (valOf (grammarDB{thyname="arm_step"})
             |> apsnd (#1 o term_grammar.mfupdate_overload_info
                              (Overload.remove_overloaded_form "add") o
                       ParseExtras.grammar_loose_equality))

val ERR = Feedback.mk_HOL_ERR "arm_stepLibSupport"

val () = show_assums := true

(* ------------------------------------------------------------------------
   Setup mirroring arm_stepLib.sml (same st, datatype bundle, EV).
   ------------------------------------------------------------------------ *)

val a_of = utilsLib.accessor_fns o arm_configLib.mk_arm_type
val u_of = utilsLib.update_fns o arm_configLib.mk_arm_type

local
   val state_fns = a_of "arm_state"
   val other_fns =
      [pairSyntax.fst_tm, pairSyntax.snd_tm, bitstringSyntax.v2w_tm,
       ``IncPC ()``, ``PSR_IT``, ``(h >< l) : 'a word -> 'b word``] @
      u_of "arm_state"
   val exc = ``SND (raise'exception e s : 'a # arm_state)``
in
   val cond_thms =
      [SIMP_CONV std_ss [] ``if a then b else if a then c else d : 'a``,
       boolTheory.COND_ID]
   val cond_rand_thms = utilsLib.mk_cond_rand_thms (other_fns @ state_fns)
   val snd_exception_thms =
      utilsLib.map_conv
         (Drule.GEN_ALL o
          utilsLib.SRW_CONV [cond_rand_thms, armTheory.raise'exception_def] o
          (fn tm => Term.mk_comb (tm, exc))) state_fns
end

val not_novfp =
  GSYM (LIST_CONJ (List.take (CONJUNCTS armTheory.VFPExtension_distinct, 3)))

fun datatype_thms thms =
   [cond_rand_thms, snd_exception_thms, FST_SWAP, not_novfp,
    arm_stepTheory.Align, arm_stepTheory.Aligned] @ thms @ cond_thms @
   utilsLib.datatype_rewrites true "arm"
     ["arm_state", "Architecture", "RName", "InstrSet", "SRType", "Encoding",
      "PSR", "VFPNegMul", "FP"]

val DATATYPE_CONV = REWRITE_CONV (datatype_thms [])
val DATATYPE_RULE = Conv.CONV_RULE DATATYPE_CONV

val EV = utilsLib.STEP (datatype_thms, st)

(* ------------------------------------------------------------------------
   R_rwt / write'R_rwt / R15_rwt: EV pipeline through BankSelect and
   LookUpRName, then the three Q.proves.
   ------------------------------------------------------------------------ *)

local
   val RBankSelect_rwt =
     EV [RBankSelect_def, BadMode] [] []
       ``RBankSelect (mode,usr,fiq,irq,svc,abt,und,mon,hyp)`` |> hd

   val RfiqBankSelect_rwt =
     EV [RfiqBankSelect_def, RBankSelect_rwt] [] []
       ``RfiqBankSelect (mode,usr,fiq)`` |> hd

   val LookUpRName_rwt =
     EV [LookUpRName_def, mustbe15, RfiqBankSelect_rwt, RBankSelect_rwt] [] []
       ``LookUpRName (n,mode)`` |> hd

   val thms = [merge_cond, cond_rand_thms, isnot15, IsSecure_def,
               CurrentInstrSet_rwt, NotMon, HaveSecurityExt_def, Rmode_def,
               write'Rmode_def, LookUpRName_rwt, arm_stepTheory.aligned_23]

   val Rmode_rwt =
      EV thms [[``Extension_Security NOTIN ^st.Extensions``]] []
        ``Rmode (n, m)`` |> hd

   val write'Rmode_rwt =
      EV thms
         [[``Extension_Security NOTIN ^st.Extensions``, ``n <> 15w: word4``,
           ``~((n = 13w: word4) /\ ~aligned 2 (v: word32) /\ ^st.CPSR.T)``]]
         []
        ``write'Rmode (v, n, m)``
        |> hd
        |> utilsLib.ALL_HYP_CONV_RULE
              (REWRITE_CONV [boolTheory.DE_MORGAN_THM,
                             GSYM boolTheory.DISJ_ASSOC])

   val in_ext = GSYM (Q.ISPEC `^st.Extensions` pred_setTheory.SPECIFICATION)
in
   val R_rwt = save_thm ("R_rwt",
      Q.prove(
        `GoodMode (^st.CPSR.M) ==>
         ~^st.Extensions Extension_Security ==>
         ~^st.CPSR.J ==>
         (R n ^st = (if n = 15w then
                       ^st.REG RName_PC + if ^st.CPSR.T then 4w else 8w
                     else ^st.REG (R_mode (^st.CPSR.M) n), ^st))`,
        lrw [R_def, R_mode_def, CurrentInstrSet_rwt, in_ext,
             DISCH_ALL Rmode_rwt]
        \\ rfs [GoodMode_def]
        \\ blastLib.FULL_BBLAST_TAC)
      |> funpow 3 Drule.UNDISCH)

   val write'R_rwt = save_thm ("write'R_rwt",
      Q.prove(
        `GoodMode (^st.CPSR.M) ==>
         ~^st.Extensions Extension_Security==>
         ~^st.CPSR.J ==>
         n <> 15w ==>
         ((n <> 13w) \/ aligned 2 v \/ ~^st.CPSR.T) ==>
         (write'R (v, n) ^st =
          ^st with REG := (R_mode (^st.CPSR.M) n =+ v) ^st.REG)`,
        rewrite_tac [in_ext]
        \\ ntac 4 strip_tac
        \\ DISCH_THEN
             (fn th => IMP_RES_TAC (MATCH_MP (DISCH_ALL write'Rmode_rwt) th))
        \\ simp [write'R_def]
        \\ pop_assum kall_tac
        \\ lrw [R_mode_def, CurrentInstrSet_rwt]
        \\ fs [GoodMode_def]
        \\ blastLib.FULL_BBLAST_TAC)
      |> funpow 5 Drule.UNDISCH)

   val R15_rwt = save_thm ("R15_rwt",
      Q.prove(
        `~^st.CPSR.J ==>
         (R 15w ^st = (^st.REG RName_PC + if ^st.CPSR.T then 4w else 8w, ^st))`,
        lrw [R_def, CurrentInstrSet_rwt] \\ fs [])
      |> Drule.UNDISCH)
end

(* ------------------------------------------------------------------------
   cond_write'R_13_rwt: rewrites a conditional write to register 13 into
   an explicit REG-update on the state; depends on write'R_rwt above.
   ------------------------------------------------------------------------ *)

val cond_write'R_13_rwt = save_thm ("cond_write'R_13_rwt",
   Q.prove(
     `~^st.CPSR.J ==> GoodMode (^st.CPSR.M) ==>
      ~^st.Extensions Extension_Security ==>
      (p ==> (aligned 2 w \/ ~^st.CPSR.T)) ==>
      ((if p then
           ((), a, write'R (w, 13w) s)
        else
           ((), s2)) =
       (if p then
           ((), a, s with REG := (R_mode ^st.CPSR.M 13w =+ w) ^st.REG)
        else
           ((), s2)))`,
     lrw [] \\ lrw [DISCH_ALL write'R_rwt])
   |> Drule.UNDISCH_ALL)

(* ------------------------------------------------------------------------
   SND_Shift_C_rwt: depends on the EV-derived Shift_C_rwt.
   ------------------------------------------------------------------------ *)

local
   val Shift_C_rwt =
      EV [Shift_C_def, LSL_C_def, LSR_C_def, ASR_C_def, ROR_C_def, RRX_C_def]
         [] []
         ``Shift_C (value,typ,amount,carry_in)
           : arm_state -> ('a word # bool) # arm_state``
         |> hd
         |> SIMP_RULE std_ss []
in
   val SND_Shift_C_rwt = save_thm ("SND_Shift_C_rwt",
      Q.prove(
        `!s. SND (Shift_C (value,typ,amount,carry_in) s) = s`,
        Cases_on `typ` \\ lrw [Shift_C_rwt]) |> Drule.GEN_ALL)
end

(* ------------------------------------------------------------------------
   cond_lsb: STM-loop lemma, standalone tactic against theory constants.
   ------------------------------------------------------------------------ *)

val cond_lsb = save_thm ("cond_lsb",
   Q.prove(
     `i < 16 ==>
      (wb /\ word_bit (w2n n) r ==>
       (n2w (LowestSetBit (r: word16)) = n: word4)) ==>
      ((if word_bit i r then
          ((), x1,
           if (n2w i = n) /\ wb /\ (i <> LowestSetBit r) then x2 else x3)
        else
          ((), x4)) =
       (if word_bit i r then ((), x1, x3) else ((), x4)))`,
     lrw [armTheory.LowestSetBit_def, wordsTheory.word_reverse_thm,
          arm_stepTheory.CountLeadingZeroBits16]
     \\ lrfs []
     \\ lfs [])
   |> Drule.UNDISCH_ALL)

(* ------------------------------------------------------------------------
   ConditionPassed_enc: rewrites ConditionPassed for the ARM encoding.
   Depends on the EV-derived ConditionPassed_rwt.
   ------------------------------------------------------------------------ *)

local
   val ConditionPassed_rwt =
      EV [ConditionPassed_def, CurrentCond_def] [] []
         ``ConditionPassed ()`` |> hd
in
   val ConditionPassed_enc = save_thm ("ConditionPassed_enc",
      Q.prove(
        `!s c.
           ConditionPassed ()
             (s with <|CurrentCondition := c; Encoding := Encoding_ARM |>) =
           ConditionPassed () (s with CurrentCondition := c)`,
        lrw [ConditionPassed_rwt])
      |> DATATYPE_RULE)
end

(* ------------------------------------------------------------------------
   Three utilsLib.qm auxiliary rewrites arm_stepLib used inline.
   ------------------------------------------------------------------------ *)

Theorem BXWritePC_qm_lem = utilsLib.qm []
   ``(c ==> b) ==>
     ((if b then x:'a else if ~c then y else z) = (if b then x else y))``

Theorem ROR_qm_lem = utilsLib.qm [wordsTheory.SHIFT_ZERO]
   ``(if n = 0 then (x: 'a word,s) else (x #>> n, ^st)) = (x #>> n, s)``

Theorem DecodeVFP_cond_case = utilsLib.qm []
   ``!z b x y. (z = if b then x:'a else y) ==> (~b ==> (z = y))``

(* ------------------------------------------------------------------------
   reg'PSR: reg-to-record equality theorem synthesized by utilsLib.
   ------------------------------------------------------------------------ *)

Theorem reg_PSR = utilsLib.mk_reg_thm "arm" "PSR"

(* ------------------------------------------------------------------------
   Standalone theorems — no local intermediates needed.
   ------------------------------------------------------------------------ *)

Theorem ArchVersion_CPSR_rwt =
   Q.prove(
     `!s c. ArchVersion () (s with CPSR := c) = ArchVersion () s`,
     lrw [ArchVersion_def]) |> DATATYPE_RULE

Theorem arm_imm_lem = Q.prove(
   `((if n = 0 then ((w, c1), s) else ((w #>> n, c2), s)) =
     ((w #>> n, if n = 0 then c1 else c2), s)) /\
    (2 * w2n (v2w [a; b; c; d] : word4) = w2n (v2w [a; b; c; d; F] : word5))`,
   rw [] \\ wordsLib.n2w_INTRO_TAC 5 \\ blastLib.BBLAST_TAC)

Theorem fpscr_thm = Q.prove(
  `FPSCR a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
         a17 a18 a19 a20 a21 =
   ^st.FP.FPSCR with
   <|AHP := a0; C := a1; DN := a2; DZC := a3; DZE := a4;
     FZ := a5; IDC := a6; IDE := a7; IOC := a8; IOE := a9;
     IXC := a10; IXE := a11; N := a12; OFC := a13; OFE := a14;
     QC := a15; RMode := a16; UFC := a17; UFE := a18; V := a19; Z := a20;
     fpscr'rst := a21|>`,
   simp [FPSCR_component_equality])

val PSR_TAC = utilsLib.REC_REG_BIT_FIELD_INSERT_TAC "arm" "PSR"

Theorem PSR_FIELDS = Q.prove(
   `(!p v.
       rec'PSR (bit_field_insert 31 27 (v: word5) (reg'PSR p)) =
       p with <|N := v ' 4; Z := v ' 3; C := v ' 2; V := v ' 1; Q := v ' 0|>) /\
    (!p v.
       rec'PSR (bit_field_insert 26 24 (v: word3) (reg'PSR p)) =
       p with <|IT := bit_field_insert 1 0 ((2 >< 1) v: word2) p.IT;
                J := v ' 0|>) /\
    (!p v.
       rec'PSR (bit_field_insert 19 16 (v: word4) (reg'PSR p)) =
       p with <|GE := v|>) /\
    (!p v.
       rec'PSR (bit_field_insert 15 10 (v: word6) (reg'PSR p)) =
       p with <|IT := bit_field_insert 7 2 v p.IT|>) /\
    (!p v.
       rec'PSR (bit_field_insert 4 0 (v: word5) (reg'PSR p)) =
       p with <|M := bit_field_insert 4 0 v p.M|>)`,
   REPEAT CONJ_TAC \\ PSR_TAC `p`)

Theorem PSR_FLAGS = Q.prove(
   `(!b p v.
       rec'PSR (bit_field_insert 9 9 (v2w [b]: word1) (reg'PSR p)) =
       p with <|E := b|>) /\
    (!b p v.
       rec'PSR (bit_field_insert 8 8 (v2w [b]: word1) (reg'PSR p)) =
       p with <|A := b|>) /\
    (!b p v.
       rec'PSR (bit_field_insert 7 7 (v2w [b]: word1) (reg'PSR p)) =
       p with <|I := b|>) /\
    (!b p v.
       rec'PSR (bit_field_insert 6 6 (v2w [b]: word1) (reg'PSR p)) =
       p with <|F := b|>) /\
    (!b p v.
       rec'PSR (bit_field_insert 5 5 (v2w [b]: word1) (reg'PSR p)) =
       p with <|T := b|>)`,
   REPEAT CONJ_TAC \\ Cases \\ PSR_TAC `p`)

Theorem IT_concat = Q.prove(
   `(!v: word6 w: word8.
       bit_field_insert 7 2 v w = w2w v << 2 || (w && 0b11w)) /\
    (!v: word2 w: word8.
       bit_field_insert 1 0 v w = w2w v || (w && 0b11111100w)) /\
    (!v1: word6 v2: word2 w: word8.
      bit_field_insert 7 2 v1 (bit_field_insert 1 0 v2 w) = v1 @@ v2)`,
   REPEAT strip_tac
   \\ rewrite_tac [wordsTheory.bit_field_insert_def]
   \\ blastLib.BBLAST_TAC)

Theorem insert_mode = Q.prove(
   `!w: word32.
       bit_field_insert 4 0 ((4 >< 0) w : word5) (v: word5) = (4 >< 0) w`,
   blastLib.BBLAST_TAC)

Theorem CPSR_lem = Q.prove(
  `GoodMode m ==> m <> 16w ==> m <> 31w ==>
   ((if m = 17w then (a, s)
     else if m = 18w then (b, s)
     else if m = 19w then (c, s)
     else if m = 22w then (d, s)
     else if m = 23w then (e, s)
     else if m = 26w then (f, s)
     else if m = 27w then (g, s)
     else h) =
    (if m = 17w then a
     else if m = 18w then b
     else if m = 19w then c
     else if m = 22w then d
     else if m = 23w then e
     else if m = 26w then f
     else g, s))`,
  rw [GoodMode_def])

Theorem CPSR_it = Q.prove(
  `((if m = 17w : word5 then (7 >< 2) a.IT : word6
     else if m = 18w then (7 >< 2) b.IT
     else if m = 19w then (7 >< 2) c.IT
     else if m = 22w then (7 >< 2) d.IT
     else if m = 23w then (7 >< 2) e.IT
     else if m = 26w then (7 >< 2) f.IT
     else (7 >< 2) g.IT) @@
    (if m = 17w then (1 >< 0) a.IT : word2
     else if m = 18w then (1 >< 0) b.IT
     else if m = 19w then (1 >< 0) c.IT
     else if m = 22w then (1 >< 0) d.IT
     else if m = 23w then (1 >< 0) e.IT
     else if m = 26w then (1 >< 0) f.IT
     else (1 >< 0) g.IT)) =
    (if m = 17w then a
     else if m = 18w then b
     else if m = 19w then c
     else if m = 22w then d
     else if m = 23w then e
     else if m = 26w then f
     else g).IT`,
  rw [] \\ fs [] \\ blastLib.BBLAST_TAC)

Theorem concat_bit_lo = Q.prove(
  `n < dimindex(:'b) /\ n <  dimindex(:'c) /\
   FINITE (univ(:'a)) /\ FINITE (univ(:'b)) ==>
   ((((a : 'a word) @@ (b : 'b word)) : 'c word) ' n = b ' n)`,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [fcpTheory.index_sum])

Theorem concat_bit_hi = Q.prove(
  `dimindex(:'b) <= n /\ n <  dimindex(:'c) /\
   n < dimindex(:'a) + dimindex (:'b) /\
   FINITE (univ(:'a)) /\ FINITE (univ(:'b)) ==>
   ((((a : 'a word) @@ (b : 'b word)) : 'c word) ' n =
    a ' (n - dimindex(:'b)))`,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [fcpTheory.index_sum])

(* Trivial-tactic anonymous rewrites that arm_stepLib used inline. *)

Theorem IncPC_16_rwt = Q.prove
  (`!b. ((if b then 16 else 32) = 16n) = b`,
   rw [])

Theorem ExpandImm_C_pair_split = Q.prove
  (`(if b then (((x, y), s): (word32 # bool) # arm_state) else ((m, n), s)) =
    ((if b then x else m, if b then y else n), s)`,
   rw [])

Theorem cond_write_R_rearrange = Q.prove
  (`!p a b n s.
      (if p then write'R (a, n) s else write'R (b, n) s) =
      write'R (if p then a else b, n) s`,
   lrw [])

Theorem StoreMultiple_rearrange = Q.prove
  (`(if p then
       s with <|MEM := a; REG := b|>
     else
       s with <|MEM := c; REG := d|>) =
    s with <|MEM := if p then a else c; REG := if p then b else d|>`,
   rw [])

Theorem eq0_bits_rwts = Q.prove
  (`(NUMERAL (BIT1 x) <> 0) /\ (NUMERAL (BIT2 x) <> 0)`,
   REWRITE_TAC [arithmeticTheory.NUMERAL_DEF, arithmeticTheory.BIT1,
                arithmeticTheory.BIT2]
   \\ DECIDE_TAC)

Theorem LoadWritePC_arch45_split = Q.prove
  (`(^st.Architecture = ARMv4) \/ (^st.Architecture = ARMv4T) ==>
    (^st.Architecture <> ARMv4 /\ ^st.Architecture <> ARMv4T /\
     ^st.Architecture <> ARMv5T /\ ^st.Architecture <> ARMv5TE \/
     aligned 2 (imm32: word32) = aligned 2 imm32)`,
   lrw [] \\ lfs [])

Theorem v2w_word_eq_lem = Q.prove
  (`(!p. ((if p then v2w [b1; b2; b3] else v2w [b4; b5; b6]) = 7w : word3) =
          (if p then b1 /\ b2 /\ b3 else b4 /\ b5 /\ b6)) /\
    (!p. ((if p then v2w [b1; b2] else v2w [b3; b4]) = 0w : word2) =
          (if p then ~b1 /\ ~b2 else ~b3 /\ ~b4))`,
   rw_tac std_ss []
   \\ CONV_TAC (Conv.LHS_CONV bitstringLib.v2w_eq_CONV)
   \\ decide_tac)

val _ = temp_set_grammars ambient_grammars
