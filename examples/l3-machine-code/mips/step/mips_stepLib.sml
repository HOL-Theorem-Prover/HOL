(* ------------------------------------------------------------------------
   MIPS step evaluator
   ------------------------------------------------------------------------ *)

structure mips_stepLib :> mips_stepLib =
struct

open HolKernel boolLib bossLib
open lcsymtacs blastLib mipsTheory mips_stepTheory

structure Parse =
struct
   open Parse
   val (tyg, (tmg, _)) =
      (I ## term_grammar.mfupdate_overload_info
               (Overload.remove_overloaded_form "add"))
      mipsTheory.mips_grammars
   val (Type, Term) = parse_from_grammars (tyg, tmg)
end

open Parse

val ERR = Feedback.mk_HOL_ERR "mips_evalLib"

val () = show_assums := true

(* ========================================================================= *)

val rhsc = utilsLib.rhsc
val st = ``s: mips_state``
fun mapl x = utilsLib.augment x [[]]

val cond_thms = Q.prove(
   `(!b c. (if b then T else c) = b \/ c) /\
    (!b c. (if b then F else c) = ~b /\ c)`,
   rw []
   )

local
   val state_fns = utilsLib.accessor_fns ``:mips_state``
   val other_fns =
      [pairSyntax.fst_tm, pairSyntax.snd_tm, bitstringSyntax.v2w_tm] @
      utilsLib.update_fns ``:mips_state``
   val extra_fns =
      [wordsSyntax.sw2sw_tm, wordsSyntax.w2w_tm,
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
       ``word_bit n: 'a word -> bool``]
   val exc = ``SND (raise'exception e s : 'a # mips_state)``
in
   val cond_rand_thms = utilsLib.mk_cond_rand_thms (other_fns @ state_fns)
   val extra_cond_rand_thms = utilsLib.mk_cond_rand_thms extra_fns
   val snd_exception_thms =
      utilsLib.map_conv
         (Drule.GEN_ALL o
          utilsLib.SRW_CONV [cond_rand_thms, mipsTheory.raise'exception_def] o
          (fn tm => Term.mk_comb (tm, exc))) state_fns
end

fun mips_thms thms =
   thms @
   [cond_rand_thms, cond_thms, snd_exception_thms,
    NotWordValue0, NotWordValueCond,
    GPR_def, write'GPR_def, CPR_def, write'CPR_def, boolTheory.COND_ID,
    wordsLib.WORD_DECIDE ``~(a > a:'a word)``,
    wordsLib.WORD_DECIDE ``a >= a:'a word``,
    wordsTheory.WORD_EXTRACT_ZERO2, wordsTheory.WORD_ADD_0,
    wordsTheory.WORD_AND_CLAUSES, wordsTheory.WORD_OR_CLAUSES,
    wordsTheory.WORD_XOR_CLAUSES, wordsTheory.WORD_MULT_CLAUSES,
    wordsTheory.WORD_SUB_RZERO, wordsTheory.WORD_SUB_LZERO,
    wordsTheory.WORD_LESS_REFL, wordsTheory.WORD_LOWER_REFL,
    wordsTheory.WORD_LESS_EQ_REFL,
    wordsTheory.WORD_LO_word_0, wordsTheory.ZERO_SHIFT, wordsTheory.SHIFT_ZERO,
    wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_NEG_0, wordsTheory.WORD_NOT_0,
    wordsTheory.sw2sw_0, wordsTheory.w2w_0, wordsTheory.word_0_n2w,
    wordsTheory.word_bit_0, sw16_to_sw64] @
   utilsLib.datatype_rewrites "mips"
      ["mips_state", "CP0", "StatusRegister", "ExceptionType"]

val COND_UPDATE_CONV =
   REWRITE_CONV (utilsLib.mk_cond_update_thms
                    [``:mips_state``, ``:CP0``, ``:StatusRegister``])
   THENC REWRITE_CONV (mips_thms [])

val COND_UPDATE_RULE = Conv.CONV_RULE COND_UPDATE_CONV

local
   val thms = ref ([]: thm list)
in
   fun resetThms () = thms := []
   fun getThms tms =
      utilsLib.specialized "" (utilsLib.WGROUND_CONV, tms) (!thms)
   fun addThms ts = (thms := ts @ !thms; ts)
end

val ev = utilsLib.STEP (mips_thms, st)
fun evr (rule:rule) thms c cvr = List.map rule o ev thms c cvr

fun EVR rule thms c cvr = addThms o evr rule thms c cvr
val EV = EVR Lib.I
val EVC = EVR COND_UPDATE_RULE

(* ------------------------------------------------------------------------- *)

val () = utilsLib.setStepConv utilsLib.WGROUND_CONV

val SignalException =
   ev [SignalException_def, extra_cond_rand_thms] [[``~^st.CP0.Status.EXL``]] []
      ``SignalException (ExceptionType)``
   |> hd

val rule =
   utilsLib.ALL_HYP_CONV_RULE (SIMP_CONV std_ss (mips_thms [])) o
   REWRITE_RULE [] o
   utilsLib.INST_REWRITE_RULE [ASSUME ``~^st.CP0.Status.EXL``]

val () = utilsLib.resetStepConv ()

fun reg i = bitstringSyntax.padded_fixedwidth_of_int (i, 5)

val r0 = reg 0

fun comb (0, _    ) = [[]]
  | comb (_, []   ) = []
  | comb (m, x::xs) = map (fn y => x :: y) (comb (m-1, xs)) @ comb (m, xs)

fun all_comb l =
   List.concat (List.tabulate (List.length l + 1, fn i => comb (i, l)))

val oEV =
   EVR (rule o COND_UPDATE_RULE)
      [dfn'ADDI_def, dfn'DADDI_def,
       SignalException, ExceptionCode_def, extra_cond_rand_thms]
      [[``rt <> 0w: word5``, ``rs <> 0w: word5``,
        ``~NotWordValue (^st.gpr (rs))``]]
      (all_comb [`rt` |-> r0, `rs` |-> r0])

val iEV =
   EV [dfn'ADDIU_def, dfn'DADDIU_def, dfn'SLTI_def, dfn'SLTIU_def,
       dfn'ANDI_def, dfn'ORI_def, dfn'XORI_def, dfn'LUI_def,
       extra_cond_rand_thms]
      [[``rt <> 0w: word5``, ``rs <> 0w: word5``,
        ``~NotWordValue (^st.gpr (rs))``]]
      (all_comb [`rt` |-> r0, `rs` |-> r0])

val lEV =
   EV [dfn'LUI_def, extra_cond_rand_thms]
      [[``rt <> 0w: word5``]]
      [[], [`rt` |-> r0]]

val pEV =
   EVR (rule o COND_UPDATE_RULE)
      [dfn'ADD_def, dfn'SUB_def, dfn'DADD_def, dfn'DSUB_def,
       SignalException, ExceptionCode_def, extra_cond_rand_thms]
      [[``rd <> 0w: word5``, ``rs <> 0w: word5``, ``rt <> 0w: word5``,
        ``~NotWordValue (^st.gpr (rs))``, ``~NotWordValue (^st.gpr (rt))``]]
      (all_comb [`rt` |-> r0, `rs` |-> r0, `rd` |-> r0])

val rEV =
   EV [dfn'ADDU_def, dfn'DADDU_def, dfn'SUBU_def, dfn'DSUBU_def, dfn'SLT_def,
       dfn'SLTU_def, dfn'AND_def, dfn'OR_def, dfn'XOR_def, dfn'NOR_def,
       dfn'SLLV_def, dfn'SRLV_def, dfn'SRAV_def, dfn'DSLLV_def, dfn'DSRLV_def,
       dfn'DSRAV_def, dfn'MTHI_def, dfn'MTLO_def,
       extra_cond_rand_thms]
      [[``rd <> 0w: word5``, ``rs <> 0w: word5``, ``rt <> 0w: word5``,
        ``~NotWordValue (^st.gpr (rs))``, ``~NotWordValue (^st.gpr (rt))``]]
      (all_comb [`rt` |-> r0, `rs` |-> r0, `rd` |-> r0])

val sEV =
   EV [dfn'SLL_def, dfn'SRL_def, dfn'SRA_def, dfn'DSLL_def, dfn'DSRL_def,
       dfn'DSRA_def, dfn'DSLL32_def, dfn'DSRL32_def, dfn'DSRA32_def,
       extra_cond_rand_thms]
      [[``rd <> 0w: word5``, ``rt <> 0w: word5``,
        ``~NotWordValue (^st.gpr (rt))``]]
      (all_comb [`rt` |-> r0, `rd` |-> r0])

val hEV =
   EVC [dfn'MFHI_def, dfn'MFLO_def, dfn'MTHI_def, dfn'MTLO_def, dfn'JALR_def,
        extra_cond_rand_thms]
       [[``rd <> 0w: word5``, ``^st.HLStatus <> HLmtlo``,
         ``^st.HLStatus <> HLmthi``]]
       [[], [`rd` |-> r0]]

val mEV =
   EV [dfn'MULT_def, dfn'MULTU_def, dfn'DMULT_def, dfn'DMULTU_def,
       extra_cond_rand_thms]
      [[``rs <> 0w: word5``, ``rt <> 0w: word5``,
        ``~NotWordValue (^st.gpr (rs))``, ``~NotWordValue (^st.gpr (rt))``]]
      (all_comb [`rt` |-> r0, `rs` |-> r0])

val dEV =
   EV [dfn'DIV_def, dfn'DIVU_def, dfn'DDIV_def, dfn'DDIVU_def,
       extra_cond_rand_thms]
      [[``rt <> 0w: word5``, ``^st.gpr (rt) <> 0w``, ``rs <> 0w: word5``,
        ``~NotWordValue (^st.gpr (rs))``, ``~NotWordValue (^st.gpr (rt))``]]
      [[], [`rs` |-> r0]]

(* ------------------------------------------------------------------------- *)

(*
val () = resetThms ()
*)

(* Arithmetic/Logic instructions *)

val ADDI = oEV ``dfn'ADDI (rs, rt, immediate)``
val DADDI = oEV ``dfn'DADDI (rs, rt, immediate)``

val ADDIU = iEV ``dfn'ADDIU (rs, rt, immediate)``
val DADDIU = iEV ``dfn'DADDIU (rs, rt, immediate)``
val SLTI = iEV ``dfn'SLTI (rs, rt, immediate)``
val SLTIU = iEV ``dfn'SLTIU (rs, rt, immediate)``
val ANDI = iEV ``dfn'ANDI (rs, rt, immediate)``
val ORI = iEV ``dfn'ORI (rs, rt, immediate)``
val XORI = iEV ``dfn'XORI (rs, rt, immediate)``

val LUI = lEV ``dfn'LUI (rt, immediate)``

val ADD = pEV ``dfn'ADD (rs, rt, rd)``
val SUB = pEV ``dfn'SUB (rs, rt, rd)``
val DADD = pEV ``dfn'DADD (rs, rt, rd)``
val DSUB = pEV ``dfn'DSUB (rs, rt, rd)``

val ADDU = rEV ``dfn'ADDU (rs, rt, rd)``
val DADDU = rEV ``dfn'DADDU (rs, rt, rd)``
val SUBU = rEV ``dfn'SUBU (rs, rt, rd)``
val DSUBU = rEV ``dfn'DSUBU (rs, rt, rd)``
val SLT = rEV ``dfn'SLT (rs, rt, rd)``
val SLTU = rEV ``dfn'SLTU (rs, rt, rd)``
val AND = rEV ``dfn'AND (rs, rt, rd)``
val OR = rEV ``dfn'OR (rs, rt, rd)``
val XOR = rEV ``dfn'XOR (rs, rt, rd)``
val NOR = rEV ``dfn'NOR (rs, rt, rd)``
val SLLV = rEV ``dfn'SLLV (rs, rt, rd)``
val SRLV = rEV ``dfn'SRLV (rs, rt, rd)``
val SRAV = rEV ``dfn'SRAV (rs, rt, rd)``
val DSLLV = rEV ``dfn'DSLLV (rs, rt, rd)``
val DSRLV = rEV ``dfn'DSRLV (rs, rt, rd)``
val DSRAV = rEV ``dfn'DSRAV (rs, rt, rd)``

val SLL = sEV ``dfn'SLL (rt, rd, sa)``
val SRL = sEV ``dfn'SRL (rt, rd, sa)``
val SRA = sEV ``dfn'SRA (rt, rd, sa)``
val DSLL = sEV ``dfn'DSLL (rt, rd, sa)``
val DSRL = sEV ``dfn'DSRL (rt, rd, sa)``
val DSRA = sEV ``dfn'DSRA (rt, rd, sa)``
val DSLL32 = sEV ``dfn'DSLL32 (rt, rd, sa)``
val DSRL32 = sEV ``dfn'DSRL32 (rt, rd, sa)``
val DSRA32 = sEV ``dfn'DSRA32 (rt, rd, sa)``

val MFHI = hEV ``dfn'MFHI (rd)``
val MFLO = hEV ``dfn'MFLO (rd)``
val MTHI = hEV ``dfn'MTHI (rd)``
val MTLO = hEV ``dfn'MTLO (rd)``

val MULT = mEV ``dfn'MULT (rs, rt)``
val MULTU = mEV ``dfn'MULTU (rs, rt)``
val DMULT = mEV ``dfn'DMULT (rs, rt)``
val DMULTU = mEV ``dfn'DMULTU (rs, rt)``

val DIV = dEV ``dfn'DIV (rs, rt)``
val DIVU = dEV ``dfn'DIVU (rs, rt)``
val DDIV = dEV ``dfn'DDIV (rs, rt)``
val DDIVU = dEV ``dfn'DDIVU (rs, rt)``

(* ------------------------------------------------------------------------- *)

(* Jumps and Branches *)

val J = EV [dfn'J_def] [] [] ``dfn'J (instr_index)``
val JAL = EV [dfn'JAL_def] [] [] ``dfn'JAL (instr_index)``
val JR = EV [dfn'JR_def] [] [] ``dfn'JR (instr_index)``
val JALR = hEV ``dfn'JALR (rs, rd)``
val BEQ = EVC [dfn'BEQ_def] [] [] ``dfn'BEQ (rs, rt, offset)``
val BNE = EVC [dfn'BNE_def] [] [] ``dfn'BNE (rs, rt, offset)``
val BLEZ = EVC [dfn'BLEZ_def] [] [] ``dfn'BLEZ (rs, offset)``
val BGTZ = EVC [dfn'BGTZ_def] [] [] ``dfn'BGTZ (rs, offset)``
val BLTZ = EVC [dfn'BLTZ_def] [] [] ``dfn'BLTZ (rs, offset)``
val BGEZ = EVC [dfn'BGEZ_def] [] [] ``dfn'BGEZ (rs, offset)``
val BLTZAL = EVC [dfn'BLTZAL_def] [] [] ``dfn'BLTZAL (rs, offset)``
val BGEZAL = EVC [dfn'BGEZAL_def] [] [] ``dfn'BGEZAL (rs, offset)``
val BEQL = EVC [dfn'BEQL_def] [] [] ``dfn'BEQL (rs, rt, offset)``
val BNEL = EVC [dfn'BNEL_def] [] [] ``dfn'BNEL (rs, rt, offset)``
val BLEZL = EVC [dfn'BLEZL_def] [] [] ``dfn'BLEZL (rs, offset)``
val BGTZL = EVC [dfn'BGTZL_def] [] [] ``dfn'BGTZL (rs, offset)``
val BLTZL = EVC [dfn'BLTZL_def] [] [] ``dfn'BLTZL (rs, offset)``
val BGEZL = EVC [dfn'BGEZL_def] [] [] ``dfn'BGEZL (rs, offset)``
val BLTZALL = EVC [dfn'BLTZALL_def] [] [] ``dfn'BLTZALL (rs, offset)``
val BGEZALL = EVC [dfn'BGEZALL_def] [] [] ``dfn'BGEZALL (rs, offset)``

(* ------------------------------------------------------------------------- *)

(* Load/Store thms and tools *)

val mem_thms =
   [AddressTranslation_def, LoadMemory_def,
    StoreMemory_byte, storeWord_def, storeDoubleword_def,
    Drule.UNDISCH StoreMemory_half, Drule.UNDISCH StoreMemory_word,
    Drule.UNDISCH StoreMemory_doubleword,
    PSIZE_def, ReverseEndian_def, BigEndianMem_def, BigEndianCPU_def,
    BYTE_def, HALFWORD_def, WORD_def, DOUBLEWORD_def,
    address_align, cond_sign_extend, byte_address, extract_byte,
    wordsTheory.word_concat_0_0,
    EVAL ``((1w:word1) @@ (0w:word2)) : word3``,
    EVAL ``(word_replicate 2 (0w:word1) : word2 @@ (0w:word1)) : word3``,
    EVAL ``(word_replicate 2 (1w:word1) : word2 @@ (0w:word1)) : word3``,
    EVAL ``word_replicate 3 (0w:word1) : word3``,
    EVAL ``word_replicate 3 (1w:word1) : word3``]

val select_rule =
   REWRITE_RULE
     [select_byte_le, select_byte_be, byte_address,
      wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_XOR_CLAUSES] o
   utilsLib.INST_REWRITE_RULE
      [select_half_le, select_half_be,
       select_word_le, select_word_be,
       select_pc_le, select_pc_be]

val memcntxts =
  [[``FST (UserMode ^st)``, ``^st.CP0.Status.RE``, ``^st.CP0.Config.BE``],
   [``~FST (UserMode ^st)``, ``^st.CP0.Status.RE``, ``^st.CP0.Config.BE``],
   [``~^st.CP0.Status.RE``, ``^st.CP0.Config.BE``],
   [ ``FST (UserMode ^st)``, ``^st.CP0.Status.RE``, ``~^st.CP0.Config.BE``],
   [``~FST (UserMode ^st)``, ``^st.CP0.Status.RE``, ``~^st.CP0.Config.BE``],
   [``~^st.CP0.Status.RE``, ``~^st.CP0.Config.BE``]]

val addr = ``sw2sw (offset:word16) + if base = 0w then 0w else ^st.gpr base``

val addr = ``sw2sw (offset:word16) + if base = 0w then 0w else ^st.gpr base``

val memcntxts =
   List.map
      (fn l =>
         [``rt <> 0w:word5``,
          ``~word_bit 0 ^addr``,
          ``(1 >< 0) ^addr = 0w: word2``,
          ``(1 >< 0) ^st.PC = 0w: word2``] @ l)
      memcntxts

val dmemcntxts =
   List.map (fn l => ``(2 >< 0) ^addr = 0w: word3`` :: l) memcntxts

fun merge_cases thms =
   let
      fun thm i = List.nth (thms, i)
   in
      utilsLib.MERGE_CASES ``^st.CP0.Config.BE``
        (utilsLib.MERGE_CASES ``^st.CP0.Status.RE``
            (utilsLib.MERGE_CASES ``FST (UserMode ^st)`` (thm 0) (thm 1))
            (thm 2))
        (utilsLib.MERGE_CASES ``^st.CP0.Status.RE``
            (utilsLib.MERGE_CASES ``FST (UserMode ^st)`` (thm 3) (thm 4))
            (thm 5))
   end

fun EVL l tm =
   let
      val thm =
         SIMP_CONV std_ss [dfn'LB_def, dfn'LBU_def,
                           dfn'LH_def, dfn'LHU_def,
                           dfn'LW_def, dfn'LWU_def,
                           dfn'LL_def, dfn'LD_def, dfn'LLD_def] tm
   in
      List.map (fn th => Conv.RIGHT_CONV_RULE (REWRITE_CONV [th]) thm) l
      |> addThms
   end

fun store_rule thms =
   utilsLib.ALL_HYP_CONV_RULE (SIMP_CONV std_ss (cond_rand_thms :: thms))

(* ------------------------------------------------------------------------- *)

(* Load instructions *)

val loadByte =
   evr select_rule (loadByte_def :: mem_thms) memcntxts []
      ``loadByte (base, rt, offset, unsigned)``
   |> merge_cases

val loadHalf =
   evr select_rule (loadHalf_def :: mem_thms) memcntxts []
      ``loadHalf (base, rt, offset, unsigned)``

val loadWord =
   evr select_rule (loadWord_def :: mem_thms) memcntxts []
      ``loadWord (base, rt, offset, unsigned)``

val loadDoubleword =
   ev ([loadDoubleword_def, double_aligned] @ mem_thms) dmemcntxts []
      ``loadDoubleword (base, rt, offset)``

val LB  = EVL [loadByte] ``dfn'LB (base, rt, offset) ^st``
val LBU = EVL [loadByte] ``dfn'LBU (base, rt, offset) ^st``

val LH  = EVL loadHalf ``dfn'LH (base, rt, offset) ^st``
val LHU = EVL loadHalf ``dfn'LHU (base, rt, offset) ^st``

val LW  = EVL loadWord ``dfn'LW (base, rt, offset) ^st``
val LWU = EVL loadWord ``dfn'LWU (base, rt, offset) ^st``
val LL  = EVL loadWord ``dfn'LL (base, rt, offset) ^st``

val LD  = EVL loadDoubleword ``dfn'LD (base, rt, offset) ^st``
val LLD = EVL loadDoubleword ``dfn'LLD (base, rt, offset) ^st``

(* Store instructions *)

val SB =
   ev (dfn'SB_def :: mem_thms) memcntxts []
      ``dfn'SB (base, rt, offset)``
   |> merge_cases
   |> Lib.list_of_singleton
   |> addThms

val SH =
   EVR (store_rule [bit_0_2_0, bit_0_2_0_6])
       ([dfn'SH_def, extract_half] @ mem_thms) memcntxts []
      ``dfn'SH (base, rt, offset)``

val SW =
   EVR (store_rule [bit_1_0_2_0, bit_1_0_2_0_4])
       ([dfn'SW_def, extract_word] @ mem_thms) memcntxts []
      ``dfn'SW (base, rt, offset)``

val SD =
   EVR (store_rule []) (dfn'SD_def :: mem_thms) dmemcntxts []
      ``dfn'SD (base, rt, offset)``

(* ------------------------------------------------------------------------- *)

(* Coprocessor instructions *)

val cps = mapl (`rd`, List.map reg [23, 26]) : utilsLib.cover

val MTC0 =
   EV [dfn'MTC0_def, extra_cond_rand_thms] [] cps
      ``dfn'MTC0 (rt, rd, v2w [F; F; F])``

val MFC0 =
   EV [dfn'MFC0_def, cast_thms] [[``rt <> 0w: word5``]] cps
      ``dfn'MFC0 (rt, rd, v2w [F; F; F])``

(* ------------------------------------------------------------------------- *)

(* Fetch *)

val Fetch = evr select_rule (Fetch_def :: mem_thms) memcntxts [] ``Fetch``

local
   fun bytes4 l =
      let
         val (b1, l) = Lib.split_after 8 l
         val (b2, l) = Lib.split_after 8 l
         val (b3, b4) = Lib.split_after 8 l
      in
         (b1, b2, b3, b4)
      end
   fun build_byte n l =
      List.tabulate
         (8, fn i => (bitstringSyntax.mk_bit (7 - i + n) |-> List.nth (l, i)))
   val mk_byte = bitstringSyntax.mk_vec 8
   val conc_rule =
      SIMP_RULE (srw_ss()++boolSimps.LET_ss)
           [bitstringTheory.fixwidth_def, bitstringTheory.field_def,
            bitstringTheory.shiftr_def, bitstringTheory.w2w_v2w] o
      ONCE_REWRITE_RULE [bitstringTheory.word_concat_v2w_rwt]
   val rule =
      Lib.funpow 3 conc_rule o
      REWRITE_RULE
         (List.map ASSUME
           [
            ``^st.MEM s.PC = ^(mk_byte 0)``,
            ``^st.MEM (s.PC + 1w) = ^(mk_byte 8)``,
            ``^st.MEM (s.PC + 2w) = ^(mk_byte 16)``,
            ``^st.MEM (s.PC + 3w) = ^(mk_byte 24)``
           ])
   fun fetch_thm i = rule (List.nth (Fetch, i))
   val Fetch_be = fetch_thm 2
   val Fetch_le = fetch_thm 5
in
   fun pad_opcode v =
      let
         val (l, ty) = listSyntax.dest_list v
         val () = ignore (ty = Type.bool andalso List.length l <= 32 orelse
                  raise ERR "mk_opcode" "bad opcode")
      in
         utilsLib.padLeft boolSyntax.F 32 l
      end
   fun fetch be v =
      let
         val (b1, b2, b3, b4) = bytes4 (pad_opcode v)
         val (thm, s) =
            if be
               then (Fetch_be,
                     build_byte 24 b4 @ build_byte 16 b3 @
                     build_byte 8 b2 @ build_byte 0 b1)
            else (Fetch_le,
                  build_byte 24 b1 @ build_byte 16 b2 @
                  build_byte 8 b3 @ build_byte 0 b4)
      in
         Thm.INST s thm
      end
   fun fetch_hex be = fetch be o bitstringSyntax.bitstring_of_hexstring
end

(* ------------------------------------------------------------------------- *)

(* Decoder *)

local
   val boolify_conv =
      Conv.RAND_CONV
         (Conv.CHANGED_CONV
            (REWRITE_CONV [mipsTheory.boolify5_v2w, mipsTheory.boolify6_v2w,
                           mipsTheory.boolify26_v2w]))
      THENC PairedLambda.let_CONV
   val Decode =
      Decode_def
      |> Thm.SPEC (bitstringSyntax.mk_vec 32 0)
      |> Conv.RIGHT_CONV_RULE
             (
              REWRITE_CONV [mipsTheory.boolify32_v2w]
              THENC Conv.DEPTH_CONV PairedLambda.let_CONV
              THENC Conv.DEPTH_CONV bitstringLib.extract_v2w_CONV
              THENC Conv.DEPTH_CONV boolify_conv
             )
   val v = fst (bitstringSyntax.dest_v2w (bitstringSyntax.mk_vec 32 0))
in
   fun DecodeMIPS pat =
      let
         val s = fst (Term.match_term v pat)
      in
         Decode |> Thm.INST s
                |> REWRITE_RULE []
                |> Conv.RIGHT_CONV_RULE (Conv.REPEATC PairedLambda.let_CONV)
      end
end

local
   fun rename b v =
      case Lib.total Term.dest_var v of
        SOME (s, ty) =>
          if String.sub (s, 0) = #"_"
             then SOME (v |-> Term.mk_var (b ^ String.extract (s, 1, NONE), ty))
          else NONE
      | NONE => NONE
   fun mk_pat_term s =
      let
         val p = s |> utilsLib.uppercase
                   |> String.explode
                   |> Lib.separate #";"
                   |> String.implode
      in
         Parse.Term [HOLPP.QUOTE ("[" ^ p ^ "]")]
      end
in
   fun pattern s =
      let
         val tm = mk_pat_term s
         val vs = Term.free_vars tm
         val s = List.mapPartial (rename "x") vs
      in
         Term.subst s tm
      end
end

val mips_ipatterns = List.map (I ## pattern)
   [
    ("ADDI",   "FFTFFF__________________________"),
    ("ADDIU",  "FFTFFT__________________________"),
    ("SLTI",   "FFTFTF__________________________"),
    ("SLTIU",  "FFTFTT__________________________"),
    ("ANDI",   "FFTTFF__________________________"),
    ("ORI",    "FFTTFT__________________________"),
    ("XORI",   "FFTTTF__________________________"),
    ("DADDI",  "FTTFFF__________________________"),
    ("DADDIU", "FTTFFT__________________________"),
    ("MULT",   "FFFFFF__________FFFFFFFFFFFTTFFF"),
    ("MULTU",  "FFFFFF__________FFFFFFFFFFFTTFFT"),
    ("DMULT",  "FFFFFF__________FFFFFFFFFFFTTTFF"),
    ("DMULTU", "FFFFFF__________FFFFFFFFFFFTTTFT")
   ]

val mips_dpatterns = List.map (I ## pattern)
   [
    ("JALR",   "FFFFFF_____FFFFF__________FFTFFT")
   ]

val mips_rpatterns = List.map (I ## pattern)
   [
    ("SLLV",   "FFFFFF_______________FFFFFFFFTFF"),
    ("SRLV",   "FFFFFF_______________FFFFFFFFTTF"),
    ("SRAV",   "FFFFFF_______________FFFFFFFFTTT"),
    ("DSLLV",  "FFFFFF_______________FFFFFFTFTFF"),
    ("DSRLV",  "FFFFFF_______________FFFFFFTFTTF"),
    ("DSRAV",  "FFFFFF_______________FFFFFFTFTTT"),
    ("ADD",    "FFFFFF_______________FFFFFTFFFFF"),
    ("ADDU",   "FFFFFF_______________FFFFFTFFFFT"),
    ("SUB",    "FFFFFF_______________FFFFFTFFFTF"),
    ("SUBU",   "FFFFFF_______________FFFFFTFFFTT"),
    ("AND",    "FFFFFF_______________FFFFFTFFTFF"),
    ("OR",     "FFFFFF_______________FFFFFTFFTFT"),
    ("XOR",    "FFFFFF_______________FFFFFTFFTTF"),
    ("NOR",    "FFFFFF_______________FFFFFTFFTTT"),
    ("SLT",    "FFFFFF_______________FFFFFTFTFTF"),
    ("SLTU",   "FFFFFF_______________FFFFFTFTFTT"),
    ("DADD",   "FFFFFF_______________FFFFFTFTTFF"),
    ("DADDU",  "FFFFFF_______________FFFFFTFTTFT"),
    ("DSUB",   "FFFFFF_______________FFFFFTFTTTF"),
    ("DSUBU",  "FFFFFF_______________FFFFFTFTTTT")
   ]

val mips_jpatterns = List.map (I ## pattern)
   [
    ("SLL",    "FFFFFFFFFFF_______________FFFFFF"),
    ("SRL",    "FFFFFFFFFFF_______________FFFFTF"),
    ("SRA",    "FFFFFFFFFFF_______________FFFFTT"),
    ("DSLL",   "FFFFFFFFFFF_______________TTTFFF"),
    ("DSRL",   "FFFFFFFFFFF_______________TTTFTF"),
    ("DSRA",   "FFFFFFFFFFF_______________TTTFTT"),
    ("DSLL32", "FFFFFFFFFFF_______________TTTTFF"),
    ("DSRL32", "FFFFFFFFFFF_______________TTTTTF"),
    ("DSRA32", "FFFFFFFFFFF_______________TTTTTT")
   ]

val mips_patterns0 = List.map (I ## pattern)
   [
    ("LUI",    "FFTTTTFFFFF_____________________"),
    ("DIV",    "FFFFFF__________FFFFFFFFFFFTTFTF"),
    ("DIVU",   "FFFFFF__________FFFFFFFFFFFTTFTT"),
    ("DDIV",   "FFFFFF__________FFFFFFFFFFFTTTTF"),
    ("DDIVU",  "FFFFFF__________FFFFFFFFFFFTTTTT"),
    ("MTHI",   "FFFFFF_____FFFFFFFFFFFFFFFFTFFFT"),
    ("MTLO",   "FFFFFF_____FFFFFFFFFFFFFFFFTFFTT"),
    ("MFHI",   "FFFFFFFFFFFFFFFF_____FFFFFFTFFFF"),
    ("MFLO",   "FFFFFFFFFFFFFFFF_____FFFFFFTFFTF")
   ]

val mips_cpatterns = List.map (I ## pattern)
   [
    ("MFC0",    "FTFFFFFFFFF__________FFFFFFFF___"),
    ("MTC0",    "FTFFFFFFTFF__________FFFFFFFF___")
   ]

val mips_patterns = List.map (I ## pattern)
   [
    ("JR",      "FFFFFF_____FFFFFFFFFF_____FFTFFF"),
    ("BLTZ",    "FFFFFT_____FFFFF________________"),
    ("BGEZ",    "FFFFFT_____FFFFT________________"),
    ("BLTZL",   "FFFFFT_____FFFTF________________"),
    ("BGEZL",   "FFFFFT_____FFFTT________________"),
    ("BLTZAL",  "FFFFFT_____TFFFF________________"),
    ("BGEZAL",  "FFFFFT_____TFFFT________________"),
    ("BLTZALL", "FFFFFT_____TFFTF________________"),
    ("BGEZALL", "FFFFFT_____TFFTT________________"),
    ("J",       "FFFFTF__________________________"),
    ("JAL",     "FFFFTT__________________________"),
    ("BEQ",     "FFFTFF__________________________"),
    ("BNE",     "FFFTFT__________________________"),
    ("BLEZ",    "FFFTTF_____FFFFF________________"),
    ("BGTZ",    "FFFTTT_____FFFFF________________"),
    ("BEQL",    "FTFTFF__________________________"),
    ("BNEL",    "FTFTFT__________________________"),
    ("BLEZL",   "FTFTTF_____FFFFF________________"),
    ("BGTZL",   "FTFTTT_____FFFFF________________"),
    ("LB",      "TFFFFF__________________________"),
    ("LH",      "TFFFFT__________________________"),
    ("LW",      "TFFFTT__________________________"),
    ("LBU",     "TFFTFF__________________________"),
    ("LHU",     "TFFTFT__________________________"),
    ("LWU",     "TFFTTT__________________________"),
    ("SB",      "TFTFFF__________________________"),
    ("SH",      "TFTFFT__________________________"),
    ("SW",      "TFTFTT__________________________"),
    ("LL",      "TTFFFF__________________________"),
    ("LLD",     "TTFTFF__________________________"),
    ("LD",      "TTFTTT__________________________"),
    ("SD",      "TTTTTT__________________________")
   ]

local
   val patterns =
      List.concat [mips_ipatterns, mips_jpatterns, mips_dpatterns,
                   mips_rpatterns, mips_patterns0, mips_cpatterns,
                   mips_patterns]
   fun padded_opcode v = listSyntax.mk_list (pad_opcode v, Type.bool)
   val get_opc = boolSyntax.rand o boolSyntax.rand o utilsLib.lhsc
   fun mk_net l =
      List.foldl
         (fn ((s:string, p), nt) =>
            let
               val thm = DecodeMIPS p
            in
               LVTermNet.insert (nt, ([], get_opc thm), (s, thm))
            end)
         LVTermNet.empty l
   fun find_opcode net =
      let
         fun find_opc tm =
            case LVTermNet.match (net, tm) of
               [(([], opc), (name, thm))] => SOME (name:string, opc, thm:thm)
             | _ => NONE
      in
         fn v =>
            let
               val pv = padded_opcode v
            in
               Option.map
                  (fn (name, opc, thm) =>
                     (name, opc, thm, fst (Term.match_term opc pv)))
                  (find_opc pv)
            end
      end
   fun x i = Term.mk_var ("x" ^ Int.toString i, Type.bool)
   fun assign_bits (p, i, n) =
      let
         val l = (i, n) |> bitstringSyntax.padded_fixedwidth_of_int
                        |> bitstringSyntax.dest_v2w |> fst
                        |> listSyntax.dest_list |> fst
      in
         Term.subst (Lib.mapi (fn i => fn b => x (i + p) |-> b) l)
      end
   val r0  = assign_bits (0, 0, 5)
   val r5  = assign_bits (5, 0, 5)
   val r10 = assign_bits (10, 0, 5)
   val sel = assign_bits (10, 0, 3)
   val dbg = assign_bits (5, 23, 5) o sel
   val err = assign_bits (5, 26, 5) o sel
   fun fnd l = find_opcode (mk_net l)
   fun fnd2 l tm = Option.map (fn (s, t, _, _) => (s, t)) (fnd l tm)
   fun sb l =
      all_comb
         (List.map
            (fn (x, f:term -> term) => (fn (s, t) => (s ^ "_" ^ x, f t))) l)
   val fnd_sb = fnd2 ## sb
   val fp = fnd_sb (mips_patterns, [])
   val f0 = fnd_sb (mips_patterns0, [("0", r0)])
   val fd = fnd_sb (mips_dpatterns, [("d0", r10)])
   val fi = fnd_sb (mips_ipatterns, [("s0", r0), ("t0", r5)])
   val fj = fnd_sb (mips_jpatterns, [("t0", r0), ("d0", r5)])
   val fr = fnd_sb (mips_rpatterns, [("s0", r0), ("t0", r5), ("d0", r10)])
   val fc = (fnd2 mips_cpatterns,
               [[fn (s, t) => (s ^ "_debug", dbg t)],
                [fn (s, t) => (s ^ "_errctl", err t)]])
   fun try_patterns [] tm = []
     | try_patterns ((f, l) :: r) tm =
         (case f tm of
             SOME x => List.map (List.foldl (fn (f, a) => f a) x) l
           | NONE => try_patterns r tm)
   val find_opc = try_patterns [fi, fr, fp, fj, fd, f0, fc]
   val mips_find_opc_ = fnd patterns
in
   val hex_to_padded_opcode =
      padded_opcode o bitstringSyntax.bitstring_of_hexstring
   fun mips_decode v =
      case mips_find_opc_ v of
         SOME (_, _, thm, s) => if List.null s then thm else Thm.INST s thm
       | NONE => raise ERR "decode" (utilsLib.long_term_to_string v)
   val mips_decode_hex = mips_decode o hex_to_padded_opcode
   fun mips_find_opc opc =
      let
         val l = find_opc opc
      in
         List.filter (fn (_, p) => Lib.can (Term.match_term p) opc) l
      end
   val mips_dict = Redblackmap.fromList String.compare patterns
   (* fun mk_mips_pattern s = Redblackmap.peek (dict, utilsLib.uppercase s) *)
end

(*
  List.map (mips_decode o snd) (Redblackmap.listItems mips_dict)
*)


(* ------------------------------------------------------------------------- *)

(* Evaluator *)

local
   val eval_simp_rule =
      utilsLib.ALL_HYP_CONV_RULE
         (Conv.DEPTH_CONV wordsLib.word_EQ_CONV
          THENC REWRITE_CONV [v2w_0_rwts])
   fun eval0 tm rwt =
      let
         val thm = eval_simp_rule (utilsLib.INST_REWRITE_CONV1 rwt tm)
      in
         if utilsLib.vacuous thm then NONE else SOME thm
      end
  val be_tm = ``^st.CP0.Config.BE``
  val le_tm = boolSyntax.mk_neg be_tm
  val base_tms = [``~^st.CP0.Status.RE``]
  fun find_thm be =
     let
        val tms = (if be then be_tm else le_tm) :: base_tms
     in
        utilsLib.find_rw (utilsLib.mk_rw_net utilsLib.lhsc (getThms tms))
     end
in
   fun eval be =
      let
         val fnd = find_thm be
      in
         fn tm =>
            let
               fun err s = (Parse.print_term tm; print "\n"; raise ERR "eval" s)
            in
              (case List.mapPartial (eval0 tm) (fnd tm) of
                  [] => err "no valid step theorem"
                | [x] => x
                | l => (List.app (fn x => (Parse.print_thm x; print "\n")) l
                        ; err "more than one valid step theorem"))
              handle HOL_ERR {message = "not found",
                              origin_function = "find_rw", ...} =>
                 err "instruction instance not supported"
            end
      end
end

local
   val get_state = snd o pairSyntax.dest_pair o rhsc
   fun mk_mips_const n = Term.prim_mk_const {Thy = "mips", Name = n}
   val state_exception_tm = mk_mips_const "mips_state_exception"
   val state_BranchStatus_tm = mk_mips_const "mips_state_BranchStatus"
   fun mk_proj_exception r = Term.mk_comb (state_exception_tm, r)
   fun mk_proj_BranchStatus r = Term.mk_comb (state_BranchStatus_tm, r)
   val ap_snd = Thm.AP_TERM ``SND:unit # mips_state -> mips_state``
   val snd_conv = Conv.REWR_CONV pairTheory.SND
   val STATE_CONV =
      Conv.QCONV
        (REWRITE_CONV (utilsLib.datatype_rewrites "mips" ["mips_state", "CP0"] @
                       [combinTheory.K_THM, combinTheory.o_THM,
                        boolTheory.COND_ID, cond_rand_thms]))
   val BranchNone_RULE =
      utilsLib.FULL_CONV_RULE STATE_CONV o
      Thm.INST [st |-> ``^st with BranchStatus := NONE``]
   val Branch_tm = mk_mips_const "Branch"
   fun is_branch thm =
      case Lib.total (fst o Term.dest_comb o utilsLib.rhsc) thm of
         SOME t => t = Branch_tm
       | NONE => false
   val state_rule = Conv.RIGHT_CONV_RULE (Conv.RAND_CONV STATE_CONV)
   val MP_Next  = state_rule o Drule.MATCH_MP NextStateMIPS_nobranch
   val MP_NextB = state_rule o Drule.MATCH_MP NextStateMIPS_branch
   val Run_CONV = utilsLib.Run_CONV ("mips", st) o utilsLib.rhsc
in
   fun mips_eval be =
      let
         val ftch = fetch be
         val run = eval be
      in
         fn v =>
            let
               val thm1 = ftch v
               val thm2 = mips_decode v
               val thm3 = Drule.SPEC_ALL (Run_CONV thm2)
               val ethm = run (rhsc thm3)
               val thm3 = thm3 |> ap_snd
                               |> Conv.RIGHT_CONV_RULE
                                    (Conv.RAND_CONV (Conv.REWR_CONV ethm)
                                     THENC snd_conv)
               val thm4 = STATE_CONV (mk_proj_exception (rhsc thm3))
               val thm = Drule.LIST_CONJ [thm1, thm2, thm3, thm4]
            in
               MP_Next thm ::
               (if is_branch thm2
                   then []
                else let
                        val thm3b = BranchNone_RULE thm3
                        val tm = rhsc thm3b
                        val thm4b = STATE_CONV (mk_proj_exception tm)
                        val thm5b = STATE_CONV (mk_proj_BranchStatus tm)
                        val thm =
                           Drule.LIST_CONJ [thm1, thm2, thm3b, thm4b, thm5b]
                     in
                        [MP_NextB thm]
                     end)
            end
      end
end

fun mips_eval_hex be = mips_eval be o bitstringSyntax.bitstring_of_hexstring

(* ========================================================================= *)

end
