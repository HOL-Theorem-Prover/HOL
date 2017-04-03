(* ------------------------------------------------------------------------
   Definitions and theorems used by CHERI/MIPS step evaluator (cheri_stepLib)
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib

open utilsLib
open wordsLib blastLib alignmentTheory
open updateTheory cheriTheory

val _ = new_theory "cheri_step"

val _ = List.app (fn f => f ())
   [numLib.prefer_num, wordsLib.prefer_word, wordsLib.guess_lengths]

(* ------------------------------------------------------------------------ *)

(* Next state theorems *)

val NextStateCHERI_def = Define`
   NextStateCHERI s0 =
   let s1 = Next s0 in if s1.exception = NoException then SOME s1 else NONE`

val exceptionSignalled_id = Q.prove(
   `!s. ~exceptionSignalled s ==>
        (s with c_state := s.c_state with c_exceptionSignalled := F = s)`,
   lrw [exceptionSignalled_def, cheri_state_component_equality,
        procState_component_equality])

val tac =
   lrw [NextStateCHERI_def, Next_def, AddressTranslation_def,
        write'CP0_def, write'exceptionSignalled_def,
        BranchTo_def, BranchDelay_def, BranchDelayPCC_def]
   \\ Cases_on
       `(Run (Decode w) (s' with currentInst := SOME w)).c_state.c_BranchTo`
   \\ Cases_on
       `(Run (Decode w) (s' with currentInst := SOME w)).c_state.c_BranchDelay`
   \\ TRY (Cases_on `x`)
   \\ lrw [write'PC_def, write'BranchTo_def, write'BranchDelay_def, CP0_def,
           PC_def]
   \\ fs [cheri_state_component_equality, procState_component_equality]

val NextStateCHERI_nodelay = utilsLib.ustore_thm("NextStateCHERI_nodelay",
    `(s.exception = NoException) /\
     (BranchDelay s = NONE) /\
     (BranchDelayPCC s = NONE) /\
     ~exceptionSignalled s ==>
     (Fetch (s with currentInst := NONE) = (SOME w, s')) /\
     (Decode w = i) /\
     (Run i (s' with currentInst := SOME w) = next_state) /\
     (next_state.exception = s.exception) /\
     (BranchDelay next_state = s.c_state.c_BranchDelay) /\
     (BranchDelayPCC next_state = NONE) /\
     (BranchToPCC next_state = NONE) /\
     (BranchTo next_state = b) /\
     ~exceptionSignalled next_state ==>
     (NextStateCHERI s =
      SOME (next_state with
              <| c_state := next_state.c_state with
                   <| c_PC := PC next_state + 4w;
                      c_BranchDelay := b;
                      c_BranchTo := NONE;
                      c_exceptionSignalled := F;
                      c_CP0 := CP0 next_state with
                        Count := (CP0 next_state).Count + 1w
                   |>
              |>))`,
    tac
    )

val NextStateCHERI_delay = utilsLib.ustore_thm("NextStateCHERI_delay",
    `(s.exception = NoException) /\
     (BranchDelay s = SOME a) /\
     (BranchDelayPCC s = NONE) /\
     ~exceptionSignalled s ==>
     (Fetch (s with currentInst := NONE) = (SOME w, s')) /\
     (Decode w = i) /\
     (Run i (s' with currentInst := SOME w) = next_state) /\
     (next_state.exception = s.exception) /\
     (BranchDelay next_state = s.c_state.c_BranchDelay) /\
     (BranchDelayPCC next_state = NONE) /\
     (BranchToPCC next_state = NONE) /\
     (BranchTo next_state = NONE) /\
     ~exceptionSignalled next_state ==>
     (NextStateCHERI s =
      SOME (next_state with
              <| c_state := next_state.c_state with
                   <| c_PC := a;
                      c_BranchDelay := NONE;
                      c_BranchTo := NONE;
                      c_exceptionSignalled := F;
                      c_CP0 := CP0 next_state with
                        Count := (CP0 next_state).Count + 1w
                   |>
              |>))`,
    tac
    )

(* ------------------------------------------------------------------------ *)

(* Lemmas and tools *)

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

val () = show_assums := true

val isAligned = Q.store_thm("isAligned",
  `(!a. isAligned (a, 0w)) /\
   (!a. isAligned (a, 1w) = aligned 1 a) /\
   (!a. isAligned (a, 3w) = aligned 2 a) /\
   (!a. isAligned (a, 7w) = aligned 3 a)`,
  simp [isAligned_def, alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val aligned_pc = Q.prove(
  `!pc : word64.  ((1 >< 0) pc = 0w : word2) = aligned 2 pc`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC)

val word1_lem = utilsLib.mk_cond_exhaustive_thm 1
val word2_lem = utilsLib.mk_cond_exhaustive_thm 2
val word3_lem = utilsLib.mk_cond_exhaustive_thm 3

val write_data_lem0 = Q.prove(
  `!d1 : word64 d2 : word64 d3 : word64 d4 : word64 mask : word64 data : word64.
     (63 >< 0) d4 && (63 >< 0) (~mask) ||
     (63 >< 0) data && (63 >< 0) mask || (63 >< 0) d1 << 192 ||
     (63 >< 0) d2 << 128 || (63 >< 0) d3 << 64 =
     (d1 @@ d2 @@ d3 @@ (d4 && ~mask || data && mask)) : 256 word`,
  blastLib.BBLAST_TAC)

val write_data_lem1 = Q.prove(
  `!d1 : word64 d2 : word64 d3 : word64 d4 : word64 mask : word64 data : word64.
     (63 >< 0) d3 << 64 && (63 >< 0) (~mask) << 64 ||
     (63 >< 0) data << 64 && (63 >< 0) mask << 64 ||
     (63 >< 0) d1 << 192 || (63 >< 0) d2 << 128 || (63 >< 0) d4 =
     (d1 @@ d2 @@ (d3 && ~mask || data && mask) @@ d4) : 256 word`,
  blastLib.BBLAST_TAC)

val write_data_lem2 = Q.prove(
  `!d1 : word64 d2 : word64 d3 : word64 d4 : word64 mask : word64 data : word64.
     (63 >< 0) d2 << 128 && (63 >< 0) (~mask) << 128 ||
     (63 >< 0) data << 128 && (63 >< 0) mask << 128 ||
     (63 >< 0) d1 << 192 || (63 >< 0) d3 << 64 || (63 >< 0) d4 =
     (d1 @@ (d2 && ~mask || data && mask) @@ d3 @@ d4) : 256 word`,
  blastLib.BBLAST_TAC)

val write_data_lem3 = Q.prove(
  `!d1 : word64 d2 : word64 d3 : word64 d4 : word64 mask : word64 data : word64.
     (63 >< 0) d1 << 192 && (63 >< 0) (~mask) << 192 ||
     (63 >< 0) data << 192 && (63 >< 0) mask << 192 ||
     (63 >< 0) d2 << 128 || (63 >< 0) d3 << 64 || (63 >< 0) d4 =
     ((d1 && ~mask || data && mask) @@ d2 @@ d3 @@ d4) : 256 word`,
  blastLib.BBLAST_TAC)

val write_data_lem =
  LIST_CONJ [write_data_lem0, write_data_lem1, write_data_lem2, write_data_lem3]

val B_ZALL_lem = Q.prove(
  `(if b then s with <| c_gpr := x; c_state := y |> else s) =
    s with <| c_gpr := if b then x else s.c_gpr;
              c_state := if b then y else s.c_state |>`,
  rw [cheri_state_component_equality])

val for_end =
  state_transformerTheory.FOR_def
  |> Q.SPECL [`i`, `i`]
  |> REWRITE_RULE []

val state_id =
  LIST_CONJ [
    utilsLib.mk_state_id_thm cheri_state_component_equality
      [["c_gpr"],
       ["all_state", "c_state"],
       ["c_BranchDelayPCC", "c_BranchToPCC", "c_capr", "c_pcc", "c_state"]],
    utilsLib.mk_state_id_thm procState_component_equality
      [["c_LLbit"],
       ["c_CP0", "c_LLbit"]]
    ]

val st = ``s:cheri_state``

val extract_conv = simpLib.SIMP_CONV (srw_ss()++wordsLib.WORD_EXTRACT_ss) []

local
  val datatype_thms =
    utilsLib.datatype_rewrites true "cheri"
      ["cheri_state", "cheri_state_brss__0", "cheri_state_brss__1",
       "procState", "DataType", "CP0", "CapCause", "StatusRegister",
       "ExceptionType"]
  val datatype_conv = SIMP_CONV std_ss datatype_thms
  val datatype_rule = CONV_RULE datatype_conv
  val datatype_thms =
    datatype_thms @
     List.map datatype_rule
      (utilsLib.mk_cond_update_thms
         [``:cheri_state``, ``:cheri_state_brss__0``, ``:cheri_state_brss__1``,
          ``:procState``, ``:CP0``] @
       [state_id, updateTheory.APPLY_UPDATE_ID, CP0_def,
        BETA_RULE (utilsLib.mk_cond_rand_thms [``\f. f (w2n a)``]),
        utilsLib.mk_cond_rand_thms
           [``cheri$cheri_state_brss__sf0``,
            ``cheri$cheri_state_brss__sf1``,
            ``cheri$CP0_Status``,
            pairSyntax.fst_tm, pairSyntax.snd_tm,
            optionSyntax.is_some_tm,
            wordsSyntax.sw2sw_tm, wordsSyntax.w2w_tm,
            wordsSyntax.word_add_tm, wordsSyntax.word_sub_tm,
            wordsSyntax.word_mul_tm,
            wordsSyntax.word_srem_tm, wordsSyntax.word_sdiv_tm,
            wordsSyntax.word_mod_tm, wordsSyntax.word_div_tm,
            wordsSyntax.word_lo_tm, wordsSyntax.word_lt_tm,
            wordsSyntax.word_ls_tm, wordsSyntax.word_le_tm,
            wordsSyntax.word_hi_tm, wordsSyntax.word_gt_tm,
            wordsSyntax.word_hs_tm, wordsSyntax.word_ge_tm,
            wordsSyntax.word_and_tm, wordsSyntax.word_or_tm,
            wordsSyntax.word_xor_tm, wordsSyntax.word_lsl_tm,
            wordsSyntax.word_lsr_tm, wordsSyntax.word_asr_tm,
            wordsSyntax.word_1comp_tm, wordsSyntax.word_2comp_tm,
            wordsSyntax.w2n_tm,
            ``(h >< l) : 'a word -> 'b word``,
            ``(=):'a word -> 'a word -> bool``,
            ``word_bit n: 'a word -> bool``]])
  val thms =
    List.map datatype_rule
     [extract_conv ``(1 >< 0) ((39 >< 3) (vaddr: word64) : 37 word) : word2``,
      extract_conv ``(36 >< 2) ((39 >< 3) (vaddr: word64) : 37 word) :35 word``,
      extract_conv ``(39 >< 5) ((39 >< 0) (vaddr: word64) : 40 word) :35 word``,
      bitstringLib.v2w_n2w_CONV ``v2w [F] :word1``, BranchDelay_def,
      BranchDelayPCC_def, getTag_def, getSealed_def, getBase_def,
      getLength_def, getPerms_def, getOffset_def, CAPR_def, write'CAPR_def,
      isCapRepresentable_def, setOffset_def, rec'Perms_def, Perms_accessors,
      wordsTheory.WORD_XOR_CLAUSES, isAligned, BYTE_def, HALFWORD_def,
      WORD_def, DOUBLEWORD_def, LLbit_def, write'LLbit_def, write'CP0_def,
      KCC_def, PC_def, write'PC_def, PCC_def, write'PCC_def, write'EPCC_def,
      NotWordValue0, NotWordValueCond, GPR_def, write'GPR_def, gpr_def,
      write'gpr_def, CPR_def, write'CPR_def, boolTheory.COND_ID,
      wordsLib.WORD_DECIDE ``~(a > a:'a word)``,
      wordsLib.WORD_DECIDE ``a >= a:'a word``,
      wordsTheory.WORD_EXTRACT_ZERO2, wordsTheory.WORD_ADD_0,
      wordsTheory.WORD_AND_CLAUSES, wordsTheory.WORD_OR_CLAUSES,
      wordsTheory.WORD_XOR_CLAUSES, wordsTheory.WORD_MULT_CLAUSES,
      wordsTheory.WORD_SUB_RZERO, wordsTheory.WORD_SUB_LZERO,
      wordsTheory.WORD_LESS_REFL, wordsTheory.WORD_LOWER_REFL,
      wordsTheory.WORD_LESS_EQ_REFL, wordsTheory.WORD_LO_word_0,
      wordsTheory.ZERO_SHIFT, wordsTheory.SHIFT_ZERO,
      wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_NEG_0,
      wordsTheory.WORD_NOT_0, wordsTheory.sw2sw_0, wordsTheory.w2w_0,
      wordsTheory.word_0_n2w, wordsTheory.word_bit_0
     ]
  val conv = SIMP_CONV std_ss (datatype_thms @ thms)
in
  val finish_off = List.map (utilsLib.FULL_CONV_RULE conv)
  val datatype_rule = datatype_rule
  val ev_conv = conv
  val ev_rule = CONV_RULE conv
  val step = utilsLib.STEP (Lib.curry (op @) datatype_thms, st)
  fun ev ths ctxt cvr t = finish_off (step (ths @ thms) ctxt cvr t)
end

(* ------------------------------------------------------------------------ *)

(* CHERI exceptions *)

val () = utilsLib.resetStepConv ()

val cp0_conv =
  RAND_CONV (SIMP_CONV (std_ss++boolSimps.LET_ss)
               [PCC_def, CP0_def, write'CP0_def]
             THENC ev_conv)

val ev_assume =
  Thm.ASSUME o utilsLib.rhsc o
  (QCONV (REWRITE_CONV [CP0_def, BranchDelay_def, BranchDelayPCC_def])
   THENC ev_conv)

val BranchDelayPCC =
  updateTheory.APPLY_UPDATE_ID
  |> Q.ISPECL [`^st.c_BranchDelayPCC`, `^st.procID`]
  |> datatype_rule
  |> REWRITE_RULE [ev_assume ``~IS_SOME (BranchDelayPCC ^st)``]

val SignalException0_rwt =
  SignalException_def
  |> Drule.SPEC_ALL
  |> (fn th => Thm.AP_THM th st)
  |> Conv.RIGHT_CONV_RULE
       (Thm.BETA_CONV
        THENC REWRITE_CONV [BranchDelay_def, BranchDelayPCC_def]
        THENC ev_conv
        THENC REWRITE_CONV
          (List.map ev_assume
            [``~IS_SOME (BranchDelay ^st)``,
             ``~IS_SOME (BranchDelayPCC ^st)``,
             ``~(CP0 ^st).Status.EXL``,
             ``ExceptionType <> XTLBRefillL``,
             ``ExceptionType <> XTLBRefillS``,
             ``ExceptionType <> C2E``])
        THENC cp0_conv
        THENC PairedLambda.let_CONV
        THENC RAND_CONV
                (ev_conv
                 THENC REWRITE_CONV
                        [CP0_def, ev_assume ``IS_SOME ^st.currentInst``]
                 THENC PairedLambda.let_CONV
                 THENC ev_conv)
        THENC PairedLambda.let_CONV
        THENC cp0_conv
        THENC PairedLambda.let_CONV
        THENC cp0_conv
        THENC PairedLambda.let_CONV
        THENC RAND_CONV
                (ev_conv
                 THENC REWRITE_CONV [ev_assume ``(CP0 ^st).Status.BEV``])
        THENC PairedLambda.let_CONV
        THENC RAND_CONV
                 (REWRITE_CONV
                    [write'BranchDelay_def, write'BranchTo_def,
                     write'BranchDelayPCC_def, write'BranchToPCC_def,
                     write'exceptionSignalled_def, write'CAPR_def
                     ]
                  THENC ev_conv
                  THENC PairedLambda.let_CONV
                  THENC REWRITE_CONV [PCC_def, BranchDelayPCC]
                  THENC ev_conv)
        THENC PairedLambda.let_CONV
        THENC cp0_conv
       )

val SignalException_rwt =
  ev [SignalException0_rwt] [[``(CP0 ^st).Status.BEV``]] []
    ``SignalException (ExceptionType)``
  |> hd

local
  val is_SignalException = #4 (HolKernel.syntax_fns2 "cheri" "SignalException")
  fun negate b =
    case Lib.total boolSyntax.dest_neg b of
       SOME nb => nb
     | NONE => boolSyntax.mk_neg b
  fun get_exception_cond tm =
    let
      val (b, t, e) = boolSyntax.dest_cond tm
    in
      if is_SignalException t orelse is_SignalException e
        then b
      else raise ERR "" ""
    end
in
  fun split_exception th =
    let
      val t = HolKernel.find_term (Lib.can get_exception_cond) (Thm.concl th)
      val b = #1 (boolSyntax.dest_cond t)
    in
      finish_off
        (List.map (utilsLib.INST_REWRITE_RULE [SignalException_rwt] o ev_rule)
          [REWRITE_RULE [ASSUME b] th,
           REWRITE_RULE [ASSUME (negate b)] th])
    end
    handle HOL_ERR _ => [th]
end

(* ------------------------------------------------------------------------ *)

val () = ( utilsLib.reset_thms ()
         ; utilsLib.setStepConv utilsLib.WGROUND_CONV
         )

fun get_def n =
  let
    val th = DB.fetch "cheri" ("dfn'" ^ n ^ "_def")
    val tm = utilsLib.lhsc (Drule.SPEC_ALL th)
  in
    (th, tm)
  end

local
  val thms =
    [write'HI_def, write'LO_def, HI_def, LO_def,
     write'hi_def, write'lo_def, hi_def, lo_def,
     write'BranchTo_def, CheckBranch_def,
     ev_rule B_ZALL_lem]
  fun instr_ev d cvr name =
    let
      val (th, tm) = get_def name
    in
      ev (th :: thms)
        [[``^d <> 0w : word5``,
          ``~NotWordValue (^st.c_gpr (rs))``,
          ``~NotWordValue (^st.c_gpr (rt))``,
          ``^st.c_state.c_hi = SOME hival``,
          ``^st.c_state.c_lo = SOME loval``,
          ``~IS_SOME ^st.c_state.c_BranchDelay``
        ]] cvr tm
        |> List.map split_exception
        |> List.concat
        |> utilsLib.save_thms name
    end
  val v0 = bitstringSyntax.padded_fixedwidth_of_num (Arbnum.fromInt 0, 5)
in
  val tev = instr_ev ``rt : word5`` [[`rt` |-> v0], []]
  val dev = instr_ev ``rd : word5`` [[`rd` |-> v0], []]
  val xev = instr_ev ``rx : word5`` []
end

(* Arithmetic/Logic instructions *)

val ADDI  = tev "ADDI"
val DADDI = tev "DADDI"

val ADDIU  = tev "ADDIU"
val DADDIU = tev "DADDIU"
val SLTI   = tev "SLTI"
val SLTIU  = tev "SLTIU"
val ANDI   = tev "ANDI"
val ORI    = tev "ORI"
val XORI   = tev "XORI"

val LUI = tev "LUI"

val ADD  = dev "ADD"
val SUB  = dev "SUB"
val DADD = dev "DADD"
val DSUB = dev "DSUB"
val MOVN = dev "MOVN"
val MOVZ = dev "MOVZ"

val ADDU  = dev "ADDU"
val DADDU = dev "DADDU"
val SUBU  = dev "SUBU"
val DSUBU = dev "DSUBU"
val SLT   = dev "SLT"
val SLTU  = dev "SLTU"
val AND   = dev "AND"
val OR    = dev "OR"
val XOR   = dev "XOR"
val NOR   = dev "NOR"
val SLLV  = dev "SLLV"
val SRLV  = dev "SRLV"
val SRAV  = dev "SRAV"
val DSLLV = dev "DSLLV"
val DSRLV = dev "DSRLV"
val DSRAV = dev "DSRAV"

val SLL    = dev "SLL"
val SRL    = dev "SRL"
val SRA    = dev "SRA"
val DSLL   = dev "DSLL"
val DSRL   = dev "DSRL"
val DSRA   = dev "DSRA"
val DSLL32 = dev "DSLL32"
val DSRL32 = dev "DSRL32"
val DSRA32 = dev "DSRA32"

val MFHI = dev "MFHI"
val MFLO = dev "MFLO"
val MTHI = xev "MTHI"
val MTLO = xev "MTLO"

val MUL    = dev "MUL"
val MADD   = xev "MADD"
val MADDU  = xev "MADDU"
val MSUB   = xev "MSUB"
val MSUBU  = xev "MSUBU"
val MULT   = xev "MULT"
val MULTU  = xev "MULTU"
val DMULT  = xev "DMULT"
val DMULTU = xev "DMULTU"

val DIV   = tev "DIV"
val DIVU  = tev "DIVU"
val DDIV  = tev "DDIV"
val DDIVU = tev "DDIVU"

(* ------------------------------------------------------------------------- *)

(* Jumps and Branches *)

val J       = xev "J"
val JAL     = xev "JAL"
val JR      = xev "JR"
val JALR    = dev "JALR"
val BEQ     = xev "BEQ"
val BNE     = xev "BNE"
val BEQL    = xev "BEQL"
val BNEL    = xev "BNEL"
val BLEZ    = xev "BLEZ"
val BGTZ    = xev "BGTZ"
val BLTZ    = xev "BLTZ"
val BGEZ    = xev "BGEZ"
val BLTZAL  = xev "BLTZAL"
val BGEZAL  = xev "BGEZAL"
val BLEZL   = xev "BLEZL"
val BGTZL   = xev "BGTZL"
val BLTZL   = xev "BLTZL"
val BGEZL   = xev "BGEZL"
val BLTZALL = xev "BLTZALL"
val BGEZALL = xev "BGEZALL"

(* ------------------------------------------------------------------------ *)

val cap_ok =
  [``^st.totalCore = 1``, ``^st.procID = 0w``,
   ``^st.c_capr ^st.procID 0w = capr0``, ``capr0.tag``, ``~capr0.sealed``,
   ``(^st.c_pcc 0w).tag``, ``~(^st.c_pcc 0w).sealed``,
   ``~((^st.c_pcc 0w).base + ^st.c_state.c_PC <+ (^st.c_pcc 0w).base)``,
   ``~((63 >< 0) ((^st.c_pcc 0w).base + ^st.c_state.c_PC) + (4w : 65 word) >+
       (63 >< 0) (^st.c_pcc 0w).base + (63 >< 0) (^st.c_pcc 0w).length)``,
   ``(1 >< 1) (^st.c_pcc 0w).perms = 1w : word32``,
   ``~(vaddr <+ capr0.base)``,
   ``~(vaddr >+ capr0.base + capr0.length)``,
   ``~(vaddr + 3w >+ capr0.base + capr0.length)``,
   ``~(vaddr + 7w >+ capr0.base + capr0.length)``,
   ``~(vaddr + w2w (accesslength : word3) >+ capr0.base + capr0.length)``,
   ``~(needalign /\ ~aligned 1 (vaddr : word64))``,
   ``~(needalign /\ ~aligned 2 (vaddr : word64))``,
   ``~(needalign /\ ~aligned 3 (vaddr : word64))``,
   ``(2 >< 2) capr0.perms = 1w : word32``,
   ``(3 >< 3) capr0.perms = 1w : word32``]

val ReverseEndian_rwt =
  ev [ReverseEndian_def] [[``~(CP0 ^st).Status.RE``]] []
    ``ReverseEndian`` |> hd

(* CHERI is normally big-endian *)
val BigEndianCPU_rwt =
  ev [BigEndianCPU_def, BigEndianMem_def, ReverseEndian_rwt]
     [[``(CP0 ^st).Config.BE``]] []
    ``BigEndianCPU`` |> hd

val () = utilsLib.setStepConv (utilsLib.WGROUND_CONV THENC extract_conv)

val WriteData_rwt =
  ev [WriteData_def, updateDwordInRaw_def, CAPBYTEWIDTH_def, capToBits_def,
      word2_lem]
    [[``^st.mem ((36 >< 2) (addr : 37 word)) =
        Raw ((d1 : word64) @@ (d2 : word64) @@
             (d3 : word64) @@ (d4 : word64))``]] []
    ``WriteData (addr, data, mask)``
   |> hd
   |> REWRITE_RULE [write_data_lem]

fun StoreMemory cnd =
  ev [StoreMemory_def, StoreMemoryCap_def, AdjustEndian_def, ReverseEndian_rwt,
      for_end]
     [``s.c_state.c_LLbit = SOME b`` ::
      ``(CP0 ^st).LLAddr = (39 >< 0) (vaddr : word64)`` ::
      cap_ok]
     [[`memtype` |-> ``BYTE``, `accesslength` |-> ``BYTE``, `cnd` |-> cnd],
      [`memtype` |-> ``WORD``, `accesslength` |-> ``WORD``, `cnd` |-> cnd],
      [`memtype` |-> ``DOUBLEWORD``, `accesslength` |-> ``DOUBLEWORD``,
       `cnd` |-> cnd]]
    ``StoreMemory (memtype,accesslength,needalign,memelem,vaddr,cnd)``
  |> List.map (ev_rule o INST_REWRITE_RULE [WriteData_rwt])

val StoreMemory_cond_rwt = StoreMemory ``T``
val StoreMemory_notcond_rwt = StoreMemory ``F``

val ReadData_rwt =
  step [ReadData_def, readDwordFromRaw_def, CAPBYTEWIDTH_def, word2_lem]
    [[``^st.mem ((36 >< 2) (addr : 37 word)) =
        Raw ((d1 : word64) @@ (d2 : word64) @@
             (d3 : word64) @@ (d4 : word64))``]] []
    ``ReadData addr`` |> hd

val LoadMemory_rwt =
  ev [LoadMemory_def, LoadMemoryCap_def, AdjustEndian_def, ReverseEndian_rwt,
      ReadData_rwt]
     [cap_ok]
     [[`memtype` |-> ``BYTE``],
      [`memtype` |-> ``WORD``],
      [`memtype` |-> ``DOUBLEWORD``]
     ]
    ``LoadMemory (memtype,accesslength,needalign,vaddr,link)``;

val () = utilsLib.setStepConv utilsLib.WGROUND_CONV

local
  val thms =
    LoadMemory_rwt @ StoreMemory_cond_rwt @ StoreMemory_notcond_rwt @
    [BigEndianCPU_rwt, getVirtualAddress_def, exceptionSignalled_def,
     loadByte_def, loadHalf_def, loadWord_def, loadDoubleword_def,
     storeWord_def, storeDoubleword_def,
     word1_lem, word2_lem, word3_lem,
     bitstringLib.v2w_n2w_CONV ``v2w [T] : word1``,
     EVAL ``word_replicate 3 (1w : word1) : word3``,
     SIMP_CONV (srw_ss()) [] ``x + y + (z - y) : 'a word``]
  fun instr_ev rt name =
    let
      val (th, tm) = get_def name
    in
      ev (th :: thms)
        [rt @ [``base <> 0w : word5``, ``~^st.c_state.c_exceptionSignalled``] @
         cap_ok] [] tm
        |> utilsLib.save_thms name
    end
in
  val lev = instr_ev [``rt <> 0w : word5``]
  val sev = instr_ev []
end

val LB  = lev "LB"
val LBU = lev "LBU"

val LW  = lev "LW"
val LWU = lev "LWU"
val LL  = lev "LL"
val LWL = lev "LWL"
val LWR = lev "LWR"

val LD  = lev "LD"
val LLD = lev "LLD"
val LDL = lev "LDL"
val LDR = lev "LDR"

val SB  = sev "SB"
val SW  = sev "SW"
val SD  = sev "SD"
val SC  = sev "SC"
val SCD = sev "SCD"

(* ------------------------------------------------------------------------ *)

val () = utilsLib.setStepConv (utilsLib.WGROUND_CONV THENC extract_conv)

val ReadWord_def = Define`
  ReadWord m (addr : 40 word) =
  case m ((39 >< 5) addr : 35 word) of
     Raw w256 =>
       SOME
         (let v = (4 >< 2) addr : word3
          in
          if v = 0w      then (63  >< 32 ) w256
          else if v = 1w then (31  >< 0  ) w256
          else if v = 2w then (127 >< 96 ) w256
          else if v = 3w then (95  >< 64 ) w256
          else if v = 4w then (191 >< 160) w256
          else if v = 5w then (159 >< 128) w256
          else if v = 6w then (255 >< 224) w256
          else                (223 >< 192) w256 : word32)
   | _ => NONE`

val ReadInst = Q.prove(
  `(ReadWord s.mem addr = SOME w) ==> (ReadInst addr s = w)`,
  rw [ReadInst_def, readDwordFromRaw_def, CAPBYTEWIDTH_def, ReadWord_def,
      alignmentTheory.aligned_extract, word2_lem]
  \\ Cases_on `s.mem ((39 >< 5) addr)`
  \\ full_simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
  \\ rw []
  \\ blastLib.FULL_BBLAST_TAC) |> Drule.UNDISCH_ALL

val Fetch_rwt =
  ev [Fetch_def, exceptionSignalled_def, aligned_pc]
    [[``~(CP0 ^st).Status.IE``,
      ``aligned 2 (^st.c_state.c_PC)``,
      ``~^st.c_state.c_exceptionSignalled``] @ cap_ok]
    [] ``Fetch``
    |> List.map (INST_REWRITE_RULE [ReadInst])
    |> finish_off

val Fetch = Theory.save_thm("Fetch", hd Fetch_rwt)

val lem = Q.prove(
  `aligned 2 (a : word64) ==>
    (~((63 >< 0) a + (4w : 65 word) >+ 0xFFFFFFFFFFFFFFFFw) =
     a <> 0xFFFFFFFFFFFFFFFCw)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC) |> Drule.UNDISCH_ALL

val Fetch_default = Theory.save_thm("Fetch_default",
  utilsLib.FULL_CONV_RULE
    (utilsLib.SRW_CONV []
     THENC REWRITE_CONV [ev_assume ``^st.c_pcc 0w = defaultCap``]
     THENC utilsLib.SRW_CONV [wordsTheory.WORD_LO_word_0, defaultCap_def]
     THENC utilsLib.INST_REWRITE_CONV [lem])
    (Thm.INST [st |-> ``^st with currentInst := NONE``] Fetch)
    )

(* ------------------------------------------------------------------------ *)

val () = (utilsLib.adjoin_thms (); export_theory ())
