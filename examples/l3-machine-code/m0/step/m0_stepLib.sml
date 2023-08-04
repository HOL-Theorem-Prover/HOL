(* ------------------------------------------------------------------------
   ARMv6-M step evaluator
   ------------------------------------------------------------------------ *)

structure m0_stepLib :> m0_stepLib =
struct

open HolKernel boolLib bossLib

open m0Theory m0_stepTheory
open state_transformerSyntax blastLib
open Parse

val ambient_grammars = (type_grammar(), term_grammar())
val _ = temp_set_grammars m0_stepTheory.m0_step_grammars

val ERR = Feedback.mk_HOL_ERR "m0_stepLib"
val WARN = Feedback.HOL_WARNING "m0_stepLib"

val () = show_assums := true

(* ========================================================================= *)

val mk_byte = bitstringSyntax.mk_vec 8
val rhsc = utilsLib.rhsc
fun mapl x = utilsLib.augment x [[]]

fun MATCH_HYP_RW l = utilsLib.MATCH_HYP_CONV_RULE (REWRITE_CONV l)
val REG_CONV = REWRITE_CONV [v2w_13_15_rwts, v2w_ground4]

val opcodes     = utilsLib.list_mk_wordii 4 (List.tabulate (16, Lib.I))
val arithlogic  = utilsLib.list_mk_wordii 4 [0,1,2,3,4,5,6,7,12,14]
val testcompare = utilsLib.list_mk_wordii 2 [0,2,3]

val st = Term.mk_var ("s", Type.mk_type ("m0_state", []))

fun mk_arm_const n = Term.prim_mk_const {Thy = "m0", Name = n}
fun mk_arm_type n = Type.mk_thy_type {Thy = "m0", Tyop = n, Args = []}

(* ---------------------------- *)

local
   val a_of = utilsLib.accessor_fns o mk_arm_type
   val u_of = utilsLib.update_fns o mk_arm_type
   val state_fns = a_of "m0_state"
   val other_fns =
      [pairSyntax.fst_tm, pairSyntax.snd_tm, bitstringSyntax.v2w_tm,
       ``IncPC ()``, ``(h >< l) : 'a word -> 'b word``] @ u_of "m0_state"
   val exc = ``SND (raise'exception e s : 'a # m0_state)``
in
   val cond_rand_thms = utilsLib.mk_cond_rand_thms (other_fns @ state_fns)
   val snd_exception_thms =
      utilsLib.map_conv
         (Drule.GEN_ALL o
          utilsLib.SRW_CONV [cond_rand_thms, m0Theory.raise'exception_def] o
          (fn tm => Term.mk_comb (tm, exc))) state_fns
end

(* ---------------------------- *)

(* ARM datatype theorems/conversions *)

fun datatype_thms thms =
   thms @ [cond_rand_thms, snd_exception_thms, FST_SWAP,
           m0_stepTheory.Align, m0_stepTheory.Aligned] @
   utilsLib.datatype_rewrites true "m0" ["m0_state", "RName", "SRType", "PSR"]

val DATATYPE_CONV = REWRITE_CONV (datatype_thms [])
val DATATYPE_RULE = Conv.CONV_RULE DATATYPE_CONV
val FULL_DATATYPE_RULE = utilsLib.FULL_CONV_RULE DATATYPE_CONV

val COND_UPDATE_CONV =
   REWRITE_CONV
     (utilsLib.qm [] ``!b. (if b then T else F) = b`` ::
      utilsLib.mk_cond_update_thms (List.map mk_arm_type ["m0_state", "PSR"]))

val COND_UPDATE_RULE = Conv.CONV_RULE COND_UPDATE_CONV

val STATE_CONV =
   REWRITE_CONV (utilsLib.datatype_rewrites true "m0" ["m0_state"] @
                 [boolTheory.COND_ID, cond_rand_thms])

local
   val cmp = computeLib.bool_compset ()
   val () = computeLib.add_thms (datatype_thms [pairTheory.FST]) cmp
in
   val EVAL_DATATYPE_CONV = Conv.TRY_CONV (utilsLib.CHANGE_CBV_CONV cmp)
end

fun fix_datatype tm = rhsc (Conv.QCONV DATATYPE_CONV tm)
val fix_datatypes = List.map fix_datatype

local
   val big_tm = fix_datatype ``^st.AIRCR.ENDIANNESS``
   val little_tm = boolSyntax.mk_neg big_tm
   val spsel_tm = fix_datatype ``^st.CONTROL.SPSEL``
   val nspsel_tm = boolSyntax.mk_neg spsel_tm
in
   fun endian be = [if be then big_tm else little_tm]
   fun spsel sel = [if sel then spsel_tm else nspsel_tm]
end

fun specialized0 m tms =
    utilsLib.specialized m (Conv.ALL_CONV, fix_datatypes tms)
fun specialized1 m tms =
    utilsLib.specialized m (utilsLib.WGROUND_CONV, fix_datatypes tms)

fun state_with_pcinc e = (st |-> fix_datatype ``^st with pcinc := ^e``)

local
   fun ADD_PRECOND_RULE e thm =
      FULL_DATATYPE_RULE (Thm.INST [state_with_pcinc e] thm)
   val rwts = ref ([]: thm list)
in
   fun getThms e tms =
      List.map (ADD_PRECOND_RULE e) (specialized1 "eval" tms (!rwts))
      |> List.filter (not o utilsLib.vacuous)
   fun resetThms () = rwts := []
   fun addThms thms = (rwts := thms @ !rwts; thms)
end

val EV = utilsLib.STEP (datatype_thms, st)
val resetEvConv = utilsLib.resetStepConv
val setEvConv = utilsLib.setStepConv

(* ========================================================================= *)

(* register access *)

val () = setEvConv utilsLib.WGROUND_CONV

val PC_rwt =
   EV [PC_def, R_def] [] []
      ``PC`` |> hd

val () = resetEvConv ()

val write'PC_rwt =
   EV [write'PC_def] [] []
      ``write'PC x`` |> hd

local
   val mask_sp =
      blastLib.BBLAST_PROVE
         ``d && 0xFFFFFFFCw : word32 = ((31 >< 2) d : word30) @@ (0w: word2)``

   fun r_rwt t = Q.prove(t,
      wordsLib.Cases_on_word_value `n`
      \\ simp [write'R_def, R_def, R_name_def, LookUpSP_def, num2RName_thm,
               mask_sp]
      )
      |> Drule.UNDISCH
in
   val R_name_rwt = r_rwt
      `n <> 15w ==> (R n ^st = ^st.REG (R_name ^st.CONTROL.SPSEL n))`

   val write'R_name_rwt = r_rwt
      `n <> 15w ==>
       (write'R (d, n) ^st =
        ^st with REG :=
        (R_name ^st.CONTROL.SPSEL n =+
        if n = 13w then d && 0xFFFFFFFCw else d) ^st.REG)`

   val RName_LR_rwt = EVAL ``m0_step$R_name x 14w``
end

(* ---------------------------- *)

(* write PC *)

val BranchTo_rwt =
   EV [BranchTo_def, write'PC_rwt] [] []
     ``BranchTo imm32`` |> hd

val IncPC_rwt =
   EV [IncPC_def, BranchTo_rwt] [] []
     ``IncPC ()`` |> hd

val BranchWritePC_rwt =
   EV [BranchWritePC_def, BranchTo_rwt] [] []
     ``BranchWritePC imm32`` |> hd

val BXWritePC_rwt =
   EV [BXWritePC_def, BranchTo_rwt]
      [[``^st.CurrentMode <> Mode_Handler``, ``word_bit 0 (imm32:word32)``]] []
    ``BXWritePC imm32`` |> hd

val BLXWritePC_rwt =
   EV [BLXWritePC_def, BranchTo_rwt] [[``word_bit 0 (imm32:word32)``]] []
    ``BLXWritePC imm32`` |> hd

val LoadWritePC_rwt =
   EV [LoadWritePC_def, BXWritePC_rwt] [] []
    ``LoadWritePC imm32`` |> hd

val ALUWritePC_rwt =
   EV [ALUWritePC_def, BranchWritePC_rwt] [] []
      ``ALUWritePC d`` |> hd

(* ---------------------------- *)

(* read mem *)

fun fixwidth_for ty =
  bitstringTheory.fixwidth_id
    |> Q.ISPEC `w2v (w:^(ty_antiq (wordsSyntax.mk_word_type ty)))`
    |> REWRITE_RULE [bitstringTheory.length_w2v]
    |> Conv.CONV_RULE (Conv.DEPTH_CONV wordsLib.SIZES_CONV)
    |> Drule.GEN_ALL

val mem_rwt =
  EV ([mem_def, mem1_def, concat16, concat32, bitstringTheory.field_fixwidth] @
      List.map fixwidth_for [``:8``, ``:16``, ``:32``]) []
    (mapl (`n`, [``1n``,``2n``,``4n``]))
    ``mem (a, n)``

val BigEndianReverse_rwt =
  EV [BigEndianReverse_def] [] (mapl (`n`, [``1n``,``2n``,``4n``]))
    ``BigEndianReverse (v, n)``

local
   val rwts =
     [MemA_def, cond_rand_thms, snd_exception_thms, alignmentTheory.aligned_0,
      wordsTheory.WORD_ADD_0, bitstringTheory.v2w_w2v] @
     mem_rwt @ BigEndianReverse_rwt
in
   val MemA_1_rwt =
     EV (rwts @ [bitstringTheory.field_fixwidth, fixwidth_for ``:8``]) [] []
       ``MemA (v, 1) : m0_state -> word8 # m0_state``
       |> hd

   val MemA_2_rwt =
     EV (extract16 :: rwts) [[``aligned 1 (v:word32)``]] []
       ``MemA (v, 2) : m0_state -> word16 # m0_state``
       |> hd

   val MemA_4_rwt =
     EV (extract32 :: rwts) [[``aligned 2 (v:word32)``]] []
       ``MemA (v, 4) : m0_state -> word32 # m0_state``
       |> hd

   val MemU_1_rwt =
     EV [MemU_def, MemA_1_rwt] [] []
       ``MemU (v, 1) : m0_state -> word8 # m0_state``
       |> hd

   val MemU_2_rwt =
     EV [MemU_def, MemA_2_rwt] [] []
       ``MemU (v, 2) : m0_state -> word16 # m0_state``
       |> hd

   val MemU_4_rwt =
     EV [MemU_def, MemA_4_rwt] [] []
       ``MemU (v, 4) : m0_state -> word32 # m0_state``
       |> hd
end

(* ---------------------------- *)

(* write mem *)

val write'mem_rwt =
  EV ([write'mem_def]) [] (mapl (`n`, [``1n``,``2n``,``4n``]))
    ``write'mem (v, a, n)``

local
   val field_cond_rand = Drule.ISPEC ``field h l`` boolTheory.COND_RAND
   val rwts =
     [write'MemA_def, cond_rand_thms, snd_exception_thms,
      wordsTheory.WORD_ADD_0, bitstringTheory.v2w_w2v,
      alignmentTheory.aligned_0, field_cond_rand] @
     write'mem_rwt @ BigEndianReverse_rwt
in
   val write'MemA_1_rwt =
     EV (rwts @ [fixwidth_for ``:8``, bitstringTheory.field_fixwidth]) [] []
       ``write'MemA (w: word8, v, 1)``
       |> hd

   val write'MemA_2_rwt =
     EV (field16 :: rwts) [[``aligned 1 (v:word32)``]] []
       ``write'MemA (w:word16, v, 2)``
       |> hd

   val write'MemA_4_rwt =
     EV (field32 :: rwts) [[``aligned 2 (v:word32)``]] []
       ``write'MemA (w:word32, v, 4)``
       |> hd

   val write'MemU_1_rwt =
     EV [write'MemU_def, write'MemA_1_rwt] [] []
       ``write'MemU (w: word8, v, 1)``
       |> hd

   val write'MemU_2_rwt =
     EV [write'MemU_def, write'MemA_2_rwt] [] []
       ``write'MemU (w: word16, v, 2)``
       |> hd

   val write'MemU_4_rwt =
     EV [write'MemU_def, write'MemA_4_rwt] [] []
       ``write'MemU (w: word32, v, 4)``
       |> hd
end

;

(* ---------------------------- *)

fun Shift_C_typ a b =
  Shift_C_DecodeRegShift_rwt
  |> Q.SPECL [a, b]
  |> Drule.SPEC_ALL
  |> REWRITE_RULE []
  |> Conv.CONV_RULE
       (Conv.LHS_CONV (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
                       THENC REWRITE_CONV [DecodeRegShift_rwt])

val Shift_C_LSL_rwt =
   EV [Shift_C_def, LSL_C_def] [] []
      ``Shift_C (value,SRType_LSL,0,carry_in)
        : m0_state -> ('a word # bool) # m0_state``
      |> hd

val Shift_C_rwt =
   EV [Shift_C_def, LSL_C_def, LSR_C_def, ASR_C_def, ROR_C_def, RRX_C_def] [] []
      ``Shift_C (value,typ,amount,carry_in)
        : m0_state -> ('a word # bool) # m0_state``
      |> hd
      |> SIMP_RULE std_ss []

val SND_Shift_C_rwt = Q.prove(
   `!s. SND (Shift_C (value,typ,amount,carry_in) s) = s`,
   Cases_on `typ` \\ lrw [Shift_C_rwt]) |> Drule.GEN_ALL

(* ---------------------------- *)

fun unfold_for_loop n thm =
   thm
   |> REWRITE_RULE [utilsLib.for_thm (n,0), BitCount]
   |> Drule.SPEC_ALL
   |> Conv.CONV_RULE (Conv.X_FUN_EQ_CONV st)
   |> Drule.SPEC_ALL
   |> Conv.RIGHT_CONV_RULE
        (PairedLambda.GEN_BETA_CONV
         THENC PairedLambda.let_CONV
         THENC PairedLambda.let_CONV
         THENC REWRITE_CONV []
         THENC Conv.ONCE_DEPTH_CONV PairedLambda.GEN_BETA_CONV
        )

val abs_body = snd o Term.dest_abs

local
   fun let_body t = let val (_, _, b) = pairSyntax.dest_plet t in b end
   fun let_val t = let val (_, b, _) = pairSyntax.dest_plet t in b end
   fun cond_true t = let val (_, b, _) = boolSyntax.dest_cond t in b end
   val split_memA =
      GSYM (Q.ISPEC `MemA x s : 'a word # m0_state` pairTheory.PAIR)
   val dest_for = (fn (_, _, b) => b) o state_transformerSyntax.dest_for o
                  Term.rator
in
   fun simp_for_body thm =
      thm
      |> Drule.SPEC_ALL
      |> rhsc |> abs_body
      |> let_body
      |> let_body
      |> let_val
      |> Term.rand
      |> dest_for
      |> abs_body |> abs_body
      |> (SIMP_CONV bool_ss [Once split_memA, pairTheory.pair_case_thm]
          THENC Conv.DEPTH_CONV PairedLambda.GEN_LET_CONV
          THENC SIMP_CONV std_ss [cond_rand_thms])
end

fun upto_enumerate n thm =
   Drule.LIST_CONJ (List.tabulate (n, fn i =>
      let
         val t = numSyntax.term_of_int i
      in
         Thm.CONJ (thm |> Thm.SPEC t |> numLib.REDUCE_RULE)
                  (numLib.REDUCE_CONV ``^t + 1``)
      end))

(* -- *)

val count_list_8 = EVAL ``COUNT_LIST 8``
val count_list_9 = EVAL ``COUNT_LIST 9``

val () = resetThms ()

local
   val LDM_UPTO_SUC = upto_enumerate 7 m0_stepTheory.LDM_UPTO_SUC
   val LDM_lem = simp_for_body dfn'LoadMultiple_def
   val LDM_thm = unfold_for_loop 7 dfn'LoadMultiple_def

   fun FOR_BETA_CONV i tm =
      let
         val b = pairSyntax.dest_snd tm
         val (b, _, _) = boolSyntax.dest_cond (abs_body (rator b))
         val n = fst (wordsSyntax.dest_word_bit b)
         val _ = numLib.int_of_term n = i orelse raise ERR "FOR_BETA_CONV" ""
         val thm =
            write'R_name_rwt
            |> Q.INST [`n` |-> `n2w ^n`]
            |> utilsLib.FULL_CONV_RULE wordsLib.WORD_EVAL_CONV
      in
         (Conv.RAND_CONV
            (PairedLambda.GEN_BETA_CONV
             THENC Conv.REWR_CONV LDM_lem
             THENC utilsLib.INST_REWRITE_CONV [MemA_4_rwt, thm])
          THENC REWRITE_CONV [cond_rand_thms, LDM_UPTO_components,
                              LDM_UPTO_0, LDM_UPTO_SUC]) tm
      end

   val LDM =
      LDM_thm
      |> Conv.RIGHT_CONV_RULE
           (REWRITE_CONV [R_name_rwt, ASSUME ``n <> 15w: word4``]
            THENC Conv.EVERY_CONV
                     (List.tabulate
                         (8, fn i => Conv.ONCE_DEPTH_CONV (FOR_BETA_CONV i))))
      |> utilsLib.ALL_HYP_CONV_RULE
            (utilsLib.WGROUND_CONV
             THENC REWRITE_CONV
                      [alignmentTheory.aligned_add_sub_123, Aligned_concat4,
                       LDM_UPTO_components]
             THENC numLib.REDUCE_CONV)

   val lem = Q.prove(
      `!registers:word9. ~word_bit (w2n (13w: word4)) registers`,
      simp [wordsTheory.word_bit_def]
      )
in
   val POP_rwt =
      EV [LDM, LDM_UPTO_def, IncPC_rwt, LDM_UPTO_PC, write'R_name_rwt,
          Aligned_SP, LoadWritePC_rwt, MemA_4_rwt, lem]
         [[``~word_bit 8 (registers: word9)``],
          [``word_bit 8 (registers: word9)``]] []
        ``dfn'LoadMultiple (T, 13w, registers)``
        |> List.map (REWRITE_RULE [count_list_8, wordsTheory.word_mul_n2w] o
                     utilsLib.MATCH_HYP_CONV_RULE wordsLib.WORD_EVAL_CONV
                       ``n2w a <> n2w b: word4`` o
                     utilsLib.ALL_HYP_CONV_RULE
                        (DATATYPE_CONV
                         THENC SIMP_CONV std_ss
                                  [alignmentTheory.aligned_add_sub_123,
                                   word_bit_0_of_load, wordsTheory.word_mul_n2w]
                         THENC DATATYPE_CONV))
        |> addThms
   val LoadMultiple_rwt =
      EV [LDM, LDM_UPTO_def, IncPC_rwt, LDM_UPTO_PC, write'R_name_rwt,
          Aligned_SP]
         [[``~word_bit 8 (registers: word9)``,
           ``b = ~word_bit (w2n (n: word4)) (registers: word9)``]] []
        ``dfn'LoadMultiple (b, n, registers)``
        |> List.map
             (Drule.ADD_ASSUM ``n <> 13w: word4`` o
              REWRITE_RULE
                 ([boolTheory.COND_ID, count_list_8] @
                  List.drop
                     (utilsLib.mk_cond_update_thms [``:m0_state``], 3)))
        |> addThms
end

(* -- *)

local
   val STM_UPTO_SUC =
      m0_stepTheory.STM_UPTO_SUC
      |> Thm.INST_TYPE [Type.alpha |-> ``:8``]
      |> SIMP_RULE (srw_ss()) []
      |> upto_enumerate 7

   val PUSH_UPTO_SUC =
      m0_stepTheory.STM_UPTO_SUC
      |> Thm.INST_TYPE [Type.alpha |-> ``:9``]
      |> SIMP_RULE (srw_ss()) []
      |> upto_enumerate 7

   val STM_thm = unfold_for_loop 7 dfn'StoreMultiple_def
   val PUSH_thm = Conv.RIGHT_CONV_RULE PairedLambda.let_CONV
                    (unfold_for_loop 8 dfn'Push_def)

   val cond_lsb = Q.prove(
      `i < 8 ==>
       (word_bit (w2n n) r ==>
        (n2w (LowestSetBit (r: word8)) = n: word4)) ==>
       ((if word_bit i r then
           (x1, if (n2w i = n) /\ (i <> LowestSetBit r) then x2 else x3)
         else
           x4) =
        (if word_bit i r then (x1, x3) else x4))`,
      lrw [m0Theory.LowestSetBit_def, wordsTheory.word_reverse_thm,
           CountLeadingZeroBits8]
      \\ lrfs []
      \\ lfs []
      )
      |> Drule.UNDISCH_ALL

   fun FOR_BETA_CONV i tm =
      let
         val b = pairSyntax.dest_snd tm
         val (b, _, _) =
           boolSyntax.dest_cond
             (snd (pairSyntax.dest_pair (abs_body (rator b))))
         val n = fst (wordsSyntax.dest_word_bit b)
         val _ = numLib.int_of_term n = i orelse raise ERR "FOR_BETA_CONV" ""
      in
         (Conv.RAND_CONV
            (PairedLambda.GEN_BETA_CONV
             THENC utilsLib.INST_REWRITE_CONV [cond_lsb]
             THENC utilsLib.INST_REWRITE_CONV [write'MemA_4_rwt, R_name_rwt]
             THENC REWRITE_CONV [])
          THENC numLib.REDUCE_CONV
          THENC REWRITE_CONV [cond_rand_thms, STM_UPTO_components,
                              STM_UPTO_0, STM_UPTO_SUC, PUSH_UPTO_SUC]) tm
      end

   fun rule thm =
      thm
      |> Conv.RIGHT_CONV_RULE
           (REWRITE_CONV [R_name_rwt, SP_def, ASSUME ``n <> 15w: word4``]
            THENC Conv.EVERY_CONV
                     (List.tabulate
                         (8, fn i => Conv.ONCE_DEPTH_CONV (FOR_BETA_CONV i))))
      |> utilsLib.ALL_HYP_CONV_RULE
            (numLib.REDUCE_CONV
             THENC REWRITE_CONV
                     [alignmentTheory.aligned_add_sub_123, Aligned_concat4,
                      STM_UPTO_components]
             THENC wordsLib.WORD_EVAL_CONV)

   val STM  = rule STM_thm
   val PUSH = rule PUSH_thm
in
   val StoreMultiple_rwt =
      EV [STM, STM_UPTO_def, IncPC_rwt, write'R_name_rwt,
          m0_stepTheory.R_x_not_pc, count_list_8] [[``n <> 13w: word4``]] []
         ``dfn'StoreMultiple (n, registers)``
         |> addThms
   val Push_rwt =
      EV [PUSH, STM_UPTO_def, IncPC_rwt, LR_def, R_name_rwt, write'R_name_rwt,
          write'MemA_4_rwt, write'SP_def, m0_stepTheory.R_x_not_pc,
          count_list_8] [] []
         ``dfn'Push (registers)``
         |> List.map
             (utilsLib.ALL_HYP_CONV_RULE
                 (REWRITE_CONV [alignmentTheory.aligned_add_sub_123]
                  THENC wordsLib.WORD_EVAL_CONV) o
              SIMP_RULE bool_ss
                 [wordsTheory.WORD_MULT_CLAUSES, wordsTheory.word_mul_n2w,
                  bit_count_9_m_8] o
              REWRITE_RULE
                 (boolTheory.COND_ID ::
                  List.drop
                     (utilsLib.mk_cond_update_thms [``:m0_state``], 3)))
         |> addThms
end

(* ----------- *)

local
   val word_bit_conv = wordsLib.WORD_BIT_INDEX_CONV true
   val map_word_bit_rule =
      List.map (Conv.CONV_RULE (Conv.LHS_CONV word_bit_conv))
   fun word_bit_thms n =
      let
         val v = bitstringSyntax.mk_vec n 0
         fun wb i = wordsSyntax.mk_word_bit (numSyntax.term_of_int i, v)
      in
         List.tabulate (n, fn i => bitstringLib.word_bit_CONV (wb i))
      end
   val suc_rule =
      Conv.CONV_RULE
         (Conv.LHS_CONV (Conv.RATOR_CONV (Conv.RAND_CONV reduceLib.SUC_CONV)))
in
   fun BIT_THMS_CONV n =
      let
         val wbit_thms = word_bit_thms n
         val widx_thms = map_word_bit_rule wbit_thms
      (* val dim_thm =
            wordsLib.SIZES_CONV
               (wordsSyntax.mk_dimindex (fcpSyntax.mk_int_numeric_type n))
         val thms = ref ([dim_thm, wordsTheory.bit_count_def] @ wbit_thms) *)
         val thms = ref wbit_thms
         val c = ref (PURE_REWRITE_CONV (!thms))
         fun bit_count_thms v =
            let
               fun upto_thm i =
                  wordsSyntax.mk_bit_count_upto (numSyntax.term_of_int i, v)
               fun thm i t =
                  let
                     val thm =
                        wordsTheory.bit_count_upto_SUC
                        |> Drule.ISPECL [v, numSyntax.term_of_int (i - 1)]
                        |> suc_rule
                  in
                     i |> upto_thm
                       |> (Conv.REWR_CONV thm
                           THENC Conv.LAND_CONV (REWRITE_CONV widx_thms)
                           THENC Conv.RAND_CONV (Conv.REWR_CONV t)
                           THENC numLib.REDUCE_CONV)
                  end
               fun loop a i =
                  if n < i then a else loop (thm i (hd a) :: a) (i + 1)
            in
               loop [Drule.ISPEC v wordsTheory.bit_count_upto_0] 1
            end
      in
         fn tm =>
            (!c) tm
            handle Conv.UNCHANGED =>
              let
                 val v =
                    HolKernel.find_term
                      (fn t =>
                         case Lib.total bitstringSyntax.dest_v2w t of
                            SOME (_, ty) =>
                               fcpSyntax.dest_int_numeric_type ty = n andalso
                               List.null (Term.free_vars t)
                          | NONE => false) tm
                 val () = thms := !thms @ (bit_count_thms v)
                 val () = c := PURE_REWRITE_CONV (!thms)
              in
                 (!c) tm
              end
      end
end

val BIT_THMS_CONV_9 = BIT_THMS_CONV 9
val BIT_THMS_CONV_8 = BIT_THMS_CONV 8 ORELSEC BIT_THMS_CONV_9

local
   val eq0_rwts = Q.prove(
      `(NUMERAL (BIT1 x) <> 0) /\ (NUMERAL (BIT2 x) <> 0)`,
      REWRITE_TAC [arithmeticTheory.NUMERAL_DEF, arithmeticTheory.BIT1,
                   arithmeticTheory.BIT2]
      \\ DECIDE_TAC)
   val count8 = rhsc count_list_8
   (* val count9 = rhsc count_list_9 *)
   val ok8 = Term.term_eq count8
   (* val ok9 = Term.term_eq count9 *)
   val STM1 = REWRITE_RULE [wordsTheory.word_mul_n2w] STM1_def
   val LDM1_tm = Term.prim_mk_const {Thy = "m0_step", Name = "LDM1"}
   val STM1_tm = Term.prim_mk_const {Thy = "m0_step", Name = "STM1"}
   val f_tm = Term.mk_var ("f", Term.type_of ``m0_step$R_name b``)
   val b_tm = Term.mk_var ("b", wordsSyntax.mk_int_word_type 32)
   val r_tm = Term.mk_var ("r", ``:RName -> word32``)
   val m_tm = Term.mk_var ("r", ``:word32 -> word8``)
   val FOLDL1_CONV = Conv.REWR_CONV (Thm.CONJUNCT1 listTheory.FOLDL)
   val FOLDL2_CONV = Conv.REWR_CONV (Thm.CONJUNCT2 listTheory.FOLDL)
   val CONV0 = REWRITE_CONV [Thm.CONJUNCT1 wordsTheory.WORD_ADD_0, eq0_rwts]
   val ONCE_FOLDL_LDM1_CONV =
     (FOLDL2_CONV
      THENC Conv.RATOR_CONV (Conv.RAND_CONV
              (Conv.REWR_CONV LDM1_def
               THENC Conv.RATOR_CONV (Conv.RATOR_CONV BIT_THMS_CONV_9)
               THENC CONV0
               THENC (Conv.REWR_CONV combinTheory.I_THM
                      ORELSEC Conv.RATOR_CONV (Conv.RAND_CONV
                                (Conv.RAND_CONV
                                    (Conv.TRY_CONV BIT_THMS_CONV_9
                                     THENC wordsLib.WORD_EVAL_CONV)
                                 THENC PairedLambda.let_CONV))))))
   val ONCE_FOLDL_STM1_CONV =
     (FOLDL2_CONV
      THENC Conv.RATOR_CONV (Conv.RAND_CONV
              (Conv.REWR_CONV STM1
               THENC Conv.RATOR_CONV (Conv.RATOR_CONV BIT_THMS_CONV_8)
               THENC CONV0
               THENC (Conv.REWR_CONV combinTheory.I_THM
                      ORELSEC (Conv.RATOR_CONV
                                  (Conv.RATOR_CONV
                                     (Conv.TRY_CONV BIT_THMS_CONV_8
                                      THENC numLib.REDUCE_CONV)
                                   THENC PairedLambda.let_CONV)
                               THENC PURE_REWRITE_CONV [combinTheory.o_THM])))))
   val lconv = REPEATC ONCE_FOLDL_LDM1_CONV THENC FOLDL1_CONV
   val sconv = REPEATC ONCE_FOLDL_STM1_CONV THENC FOLDL1_CONV
   val lthms = ref ([]: thm list)
   val sthms = ref ([]: thm list)
   val lc = ref (PURE_REWRITE_CONV (!lthms))
   val sc = ref (PURE_REWRITE_CONV (!sthms))
in
   fun FOLDL_LDM1_CONV tm = (!lc) tm
      handle Conv.UNCHANGED =>
        let
           val (f, r, l) = listSyntax.dest_foldl tm
           val (ldm, f, b, v, s) =
              case boolSyntax.strip_comb f of
                 (ld, [f, b, v, s]) => (ld, f, b, v, s)
               | _ => raise ERR "FOLDL_LDM1_CONV" ""
           val _ = Term.term_eq LDM1_tm ldm andalso ok8 l
                   orelse raise ERR "FOLDL_LDM1_CONV" ""
           val df = Term.list_mk_comb (LDM1_tm, [f_tm, b_tm, v, st])
           val thm = lconv (listSyntax.mk_foldl (df, r_tm, count8))
                     |> Drule.GEN_ALL
           val () = lthms := thm :: (!lthms)
           val () = lc := PURE_REWRITE_CONV (!lthms)
        in
           Drule.SPECL [s, r, f, b] thm
        end
   fun FOLDL_STM1_CONV tm = (!sc) tm
      handle Conv.UNCHANGED =>
        let
           val (f, m, l) = listSyntax.dest_foldl tm
           val (stm, f, b, v, s) =
              case boolSyntax.strip_comb f of
                 (stm, [f, b, v, s]) => (stm, f, b, v, s)
               | _ => raise ERR "FOLDL_STM1_CONV" ""
           val _ = Term.same_const STM1_tm stm andalso ok8 l
                   orelse raise ERR "FOLDL_STM1_CONV" ""
           val df = Term.list_mk_comb (stm, [f_tm, b_tm, v, st])
           val thm = sconv (listSyntax.mk_foldl (df, m_tm, count8))
                     |> Drule.GEN_ALL
           val () = lthms := thm :: (!lthms)
           val () = sc := PURE_REWRITE_CONV (!lthms)
        in
           Drule.SPECL [s, m, f, b] thm
        end
end

local
   val word_bit_tm = ``word_bit a (v2w b : word9)``
   val wb_cond_tm = ``if ~^word_bit_tm then r1 else r2: RName -> word32``
   val wb_match = Lib.can (Term.match_term wb_cond_tm)
   val wb_rule =
      utilsLib.MATCH_HYP_CONV_RULE
         (REWRITE_CONV [boolTheory.DE_MORGAN_THM, word_bit_9_expand])
   val wb_rule_wb = wb_rule ``~^word_bit_tm``
   val wb_rule_nowb = wb_rule word_bit_tm
in
   fun split_wb_cond_rule wb thm =
      let
         val tm = rhsc thm
      in
         case Lib.total (HolKernel.find_term wb_match) tm of
            SOME c =>
               let
                  val (c, _, _) = boolSyntax.dest_cond c
               in
                  if wb
                     then wb_rule_wb (REWRITE_RULE [ASSUME c] thm)
                  else wb_rule_nowb
                          (REWRITE_RULE [ASSUME (boolSyntax.dest_neg c)] thm)
               end
          | NONE => thm
      end
end

local
   val be_tm = hd (endian true)
   val le_tm = hd (endian false)
   fun endian_rule thm =
      REWRITE_RULE
         [ASSUME (if Lib.exists (aconv le_tm) (Thm.hyp thm)
                     then le_tm
                  else be_tm)] thm
   fun NO_FREE_VARS_CONV tm =
      if List.null (Term.free_vars tm)
         then Conv.ALL_CONV tm
      else Conv.NO_CONV tm
   val LowestSetBit_CONV =
      Conv.REWR_CONV m0Theory.LowestSetBit_def
      THENC NO_FREE_VARS_CONV
      THENC Conv.RAND_CONV bossLib.EVAL
      THENC Conv.REWR_CONV m0_stepTheory.CountLeadingZeroBits8
      THENC bossLib.EVAL
   val BIT_COUNT_CONV =
      Conv.REWR_CONV wordsTheory.bit_count_def
      THENC Conv.RATOR_CONV (Conv.RAND_CONV wordsLib.SIZES_CONV)
      THENC NO_FREE_VARS_CONV
      THENC BIT_THMS_CONV_8
   val bit_count_rule =
      utilsLib.MATCH_HYP_CONV_RULE numLib.REDUCE_CONV ``~(a < 1n)`` o
      utilsLib.FULL_CONV_RULE (Conv.DEPTH_CONV BIT_COUNT_CONV)
   val word_bit_rule =
      utilsLib.FULL_CONV_RULE
        (utilsLib.WGROUND_CONV
         THENC TRY_CONV BIT_THMS_CONV_8
         THENC REWRITE_CONV [])
   val mk_neq = boolSyntax.mk_neg o boolSyntax.mk_eq
   fun mk_stm_wb_thm t =
      let
         val l = t |> boolSyntax.lhand
                   |> boolSyntax.rand
                   |> bitstringSyntax.dest_v2w |> fst
                   |> bitstringSyntax.bitlist_of_term
                   |> List.foldl
                         (fn (b, (i, a)) => (i - 1, if b then i :: a else a))
                         (7, [])
                   |> snd |> tl
         val base = boolSyntax.rhs (boolSyntax.rand t)
         val t2 =
           List.map (fn i => mk_neq (base, wordsSyntax.mk_wordii (i, 4))) l
           |> (fn [] => boolSyntax.T | x => boolSyntax.list_mk_conj x)
         val eq_thm =
            boolSyntax.list_mk_forall
               (Term.free_vars base, boolSyntax.mk_eq (t, t2))
      in
         (*
         set_goal ([], eq_thm)
         *)
         Tactical.prove(eq_thm, REPEAT Cases THEN EVAL_TAC)
      end
   val stm_rule1 =
      utilsLib.MATCH_HYP_CONV_RULE
         (Conv.RAND_CONV
            (Conv.LHS_CONV (Conv.RAND_CONV (Conv.TRY_CONV LowestSetBit_CONV))))
         ``x ==> (n2w (LowestSetBit (l: word8)) = v2w q : word4)``
   fun stm_rule2 thm =
      case List.find boolSyntax.is_imp_only (Thm.hyp thm) of
         SOME t =>
            (case Lib.total mk_stm_wb_thm t of
                SOME rwt =>
                  utilsLib.MATCH_HYP_CONV_RULE
                    (PURE_REWRITE_CONV [rwt]) ``x ==> (a: word4 = b)`` thm
              | NONE => thm)
       | NONE => thm
in
   fun ldm_stm_rule s =
      let
         val s' = utilsLib.uppercase s
         val ld = String.isPrefix "LDM" s'
      in
         if ld orelse String.isPrefix "POP" s'
            then utilsLib.FULL_CONV_RULE numLib.REDUCE_CONV o endian_rule o
                 Conv.CONV_RULE (Conv.DEPTH_CONV FOLDL_LDM1_CONV) o
                 bit_count_rule o
                 word_bit_rule o
                 (if ld andalso s' <> "LDM"
                     then split_wb_cond_rule (String.isSubstring "(WB)" s')
                  else Lib.I)
         else if String.isPrefix "STM" s' orelse String.isPrefix "PUSH" s'
            then numLib.REDUCE_RULE o stm_rule2 o stm_rule1 o bit_count_rule o
                 endian_rule o
                 Conv.CONV_RULE (Conv.DEPTH_CONV FOLDL_STM1_CONV) o
                 word_bit_rule
         else Lib.I
      end
end

(*

val v8 = rhsc (bitstringLib.n2w_v2w_CONV ``0x1w: word8``)
val v8 = rhsc (bitstringLib.n2w_v2w_CONV ``0xFFw: word8``)

val v9 = rhsc (bitstringLib.n2w_v2w_CONV ``0x1w: word9``)
val v9 = rhsc (bitstringLib.n2w_v2w_CONV ``0x1FFw: word9``)

val tm =
   ``(FOLDL (m0_step$LDM1 f (s.REG (f n) + 4w) ^v9 s) s.REG
         [0; 1; 2; 3; 4; 5; 6; 7])``

val tm =
  ``FOLDL (m0_step$STM1 f (s.REG (f n) + 4w) ^v8 s) s.MEM
      [0; 1; 2; 3; 4; 5; 6; 7]``

Count.apply FOLDL_LDM1_CONV tm
Count.apply FOLDL_STM1_CONV tm

*)

(* ========================================================================= *)

(* Fetch *)

fun mk_bool_list l = listSyntax.mk_list (l, Type.bool)

local
   val err = ERR "dest_bool_list" "bad Bool list"
in
   fun dest_bool_list tm =
      case Lib.total listSyntax.dest_list tm of
         SOME (l, ty) => (ty = Type.bool orelse raise err; l)
       | NONE => raise err
end

local
   fun pad_opcode n =
      let
         val wty = fcpSyntax.mk_int_numeric_type n
      in
         fn v =>
            let
               val l = dest_bool_list v
               val () = ignore (List.length l <= n
                                orelse raise ERR "pad_opcode" "bad Bool list")
            in
               (utilsLib.padLeft boolSyntax.F n l, wty)
            end
      end
   fun mk_thumb2_pair l =
      let
         val l1 = mk_bool_list (List.take (l, 16))
         val l2 = mk_bool_list (List.drop (l, 16))
      in
         pairSyntax.mk_pair (l1, l2)
      end
   val pad_16 = pad_opcode 16
   val pad_32 = pad_opcode 32
   val hex_to_bits_16 =
      mk_bool_list o fst o pad_16 o bitstringSyntax.bitstring_of_hexstring
   val hex_to_bits_16x2 =
      mk_thumb2_pair o fst o pad_32 o bitstringSyntax.bitstring_of_hexstring
in
   val split_thumb2_pat = mk_thumb2_pair o dest_bool_list
   fun hex_to_bits s =
      hex_to_bits_16 s
      handle HOL_ERR {message = "bad Bool list", ...} =>
      hex_to_bits_16x2 s
   fun mk_opcode v =
      case Lib.total pairSyntax.dest_pair v of
         SOME (l, r) =>
           let
              val (opc1, ty) = pad_16 l
              val (opc2, _) = pad_16 r
           in
              pairSyntax.mk_pair
                (bitstringSyntax.mk_v2w (mk_bool_list opc1, ty),
                 bitstringSyntax.mk_v2w (mk_bool_list opc2, ty))
           end
       | NONE =>
           let
              val (opc, ty) = pad_16 v
           in
              bitstringSyntax.mk_v2w (mk_bool_list opc, ty)
           end
end

local
   val lem = Q.prove (
      `(!p. ((if p then v2w [b1; b2; b3] else v2w [b4; b5; b6]) = 7w : word3) =
             (if p then b1 /\ b2 /\ b3 else b4 /\ b5 /\ b6)) /\
       (!p. ((if p then v2w [b1; b2] else v2w [b3; b4]) = 0w : word2) =
             (if p then ~b1 /\ ~b2 else ~b3 /\ ~b4))`,
      lrw []
      \\ CONV_TAC (Conv.LHS_CONV bitstringLib.v2w_eq_CONV)
      \\ decide_tac)

   val CONC_RULE =
     SIMP_RULE (srw_ss()++boolSimps.LET_ss)
        [bitstringTheory.fixwidth_def, bitstringTheory.field_def,
         bitstringTheory.shiftr_def, bitstringTheory.w2w_v2w, lem] o
     ONCE_REWRITE_RULE [bitstringTheory.word_concat_v2w_rwt]

   val lem =
      Drule.LIST_CONJ
        [simpLib.SIMP_CONV (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
            ``(15 >< 13) (((w1:word8) @@ (w2:word8)) : word16) : word3``,
         simpLib.SIMP_CONV (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
            ``(12 >< 11) (((w1:word8) @@ (w2:word8)) : word16) : word2``,
         simpLib.SIMP_CONV (srw_ss()) [] ``a + 2w + 1w : word32``]

   val rule =
      CONC_RULE o
      ASM_REWRITE_RULE [cond_rand_thms, lem,
         bitstringTheory.word_extract_v2w, bitstringTheory.word_bits_v2w]

   val ALIGNED_PLUS_RULE =
      MATCH_HYP_RW [alignmentTheory.aligned_add_sub_123,
                    alignmentTheory.aligned_numeric]
        ``aligned c (a + b : 'a word)``

   val thumb2_test_tm =
      fix_datatype
       ``((15 >< 13) (FST (MemA (^st.REG RName_PC,2) s): word16) = 7w: word3) /\
          (12 >< 11) (FST (MemA (^st.REG RName_PC,2) s): word16) <> 0w: word2``

   val not_thumb2_test_tm = boolSyntax.mk_neg thumb2_test_tm

   val byte_tms = List.map fix_datatype
      [``^st.MEM (^st.REG RName_PC) = ^(mk_byte 0)``,
       ``^st.MEM (^st.REG RName_PC + 1w) = ^(mk_byte 8)``,
       ``^st.MEM (^st.REG RName_PC + 2w) = ^(mk_byte 16)``,
       ``^st.MEM (^st.REG RName_PC + 3w) = ^(mk_byte 24)``]

   val fetch_thumb_rwts =
      EV [Fetch_def, MemA_2_rwt] [[not_thumb2_test_tm], [thumb2_test_tm]] []
         ``Fetch``

   val fetch_thms =
      [fetch_thumb_rwts
       |> hd
       |> Thm.DISCH not_thumb2_test_tm
       |> Drule.ADD_ASSUM (List.nth (byte_tms, 0))
       |> Drule.ADD_ASSUM (List.nth (byte_tms, 1))
       |> Conv.CONV_RULE (utilsLib.INST_REWRITE_CONV [MemA_2_rwt])
       |> rule,
       fetch_thumb_rwts
       |> tl |> hd
       |> Thm.DISCH thumb2_test_tm
       |> Drule.ADD_ASSUM (List.nth (byte_tms, 0))
       |> Drule.ADD_ASSUM (List.nth (byte_tms, 1))
       |> Drule.ADD_ASSUM (List.nth (byte_tms, 2))
       |> Drule.ADD_ASSUM (List.nth (byte_tms, 3))
       |> Conv.CONV_RULE
             (utilsLib.INST_REWRITE_CONV [MemA_2_rwt] THENC DATATYPE_CONV)
       |> ALIGNED_PLUS_RULE
       |> rule]

   fun bytes2 l = Lib.split_after 8 l

   fun bytes4 l =
      let
         val (b1, l) = Lib.split_after 8 l
         val (b2, l) = Lib.split_after 8 l
         val (b3, b4) = Lib.split_after 8 l
      in
         (b1, b2, b3, b4)
      end

   fun build_byte n l =
      List.tabulate (8,
         fn i => (bitstringSyntax.mk_bit (7 - i + n) |-> List.nth (l, i)))

   fun assign_thumb e = fn v =>
      let
         val (b1, b2) = bytes2 (utilsLib.padLeft boolSyntax.F 16 v)
      in
         if e then build_byte 8 b2 @ build_byte 0 b1
         else build_byte 8 b1 @ build_byte 0 b2
      end

   fun assign_thumb2 e = fn v =>
      let
         val (b1, b2, b3, b4) = bytes4 v
      in
         if e then build_byte 24 b4 @ build_byte 16 b3 @
                   build_byte 8 b2 @ build_byte 0 b1
         else build_byte 24 b3 @ build_byte 16 b4 @
              build_byte 8 b1 @ build_byte 0 b2
      end

   fun ftch_thms tms =
      utilsLib.specialized "fetch"
         (utilsLib.WGROUND_CONV THENC DATATYPE_CONV, fix_datatypes tms)
         fetch_thms

   fun fetch_thm tms =
      case ftch_thms tms of
         [thm1, thm2] => (thm1, thm2)
       | _ => raise ERR "fetch_thm" "expecting 1 or 2 theorems"

   val rule =
      MATCH_HYP_RW [] ``a /\ b: bool`` o MATCH_HYP_RW [] ``a \/ b: bool``

   fun check (l, s) thm =
      if utilsLib.vacuous thm
         then raise ERR "fetch" (utilsLib.long_term_to_string l ^ " " ^ s)
      else thm
in
   fun fetch e =
      let
         val (thm1, thm2) = fetch_thm (endian e)
      in
         fn v =>
            let
               val l = dest_bool_list v
                       handle e as HOL_ERR {message = "bad Bool list", ...} =>
                        let
                           val (l1, l2) = Lib.with_exn pairSyntax.dest_pair v e
                        in
                           dest_bool_list l1 @ dest_bool_list l2
                        end
            in
               if List.length l <= 16
                  then check (v, "is a Thumb-2 prefix")
                             (rule (Thm.INST (assign_thumb e l) thm1))
               else if List.length l = 32
                  then check (v, "is not a Thumb-2 instruction")
                             (rule (Thm.INST (assign_thumb2 e l) thm2))
               else raise ERR "fetch" "length must be 16 or 32"
            end
      end
end

fun fetch_hex tms =
   let
      val ftch = fetch tms
   in
      ftch o hex_to_bits
   end

(*

val ftch = fetch_hex true
val ftch = fetch_hex false

Count.apply ftch "8F1FF3BF"
Count.apply ftch "8F1F"
Count.apply ftch "F3BF8F1F"
Count.apply ftch "F000BFFE"

*)

(* ========================================================================= *)

(* Decode *)

val DECODE_UNPREDICTABLE_rwt =
   EV [DECODE_UNPREDICTABLE_def, MachineCode_case_def]
      [] (mapl (`mc`, [``Thumb opc``, ``Thumb2 (opc1, opc2)``]))
      ``DECODE_UNPREDICTABLE (mc, e)``
      |> List.map Drule.GEN_ALL

val ConditionPassed_rwt =
   EV [ConditionPassed_def] [] []
      ``ConditionPassed c`` |> hd

local
   fun ConditionPassed cond =
      ConditionPassed_rwt
      |> Thm.INST [``c:word4`` |-> ``^cond``]
      |> Conv.RIGHT_CONV_RULE
           (DATATYPE_CONV
            THENC Conv.DEPTH_CONV bitstringLib.word_bit_CONV
            THENC Conv.DEPTH_CONV bitstringLib.extract_v2w_CONV
            THENC Conv.DEPTH_CONV bitstringLib.v2w_eq_CONV
            THENC SIMP_CONV bool_ss [])
   fun iConditionPassed i =
      wordsSyntax.mk_wordii (i, 4)
        |> ConditionPassed |> Conv.CONV_RULE wordsLib.WORD_EVAL_CONV
in
   val iConditionPassed_rwts = List.tabulate (16, iConditionPassed)
end

local
   val DecodeImmShift_rwt =
      pairTheory.PAIR
      |> Q.ISPEC `DecodeImmShift x`
      |> Thm.SYM
      |> Drule.GEN_ALL
   fun selective_v2w_eq_CONV tm =
      let
         val r = boolSyntax.rhs tm
      in
         if wordsSyntax.size_of r = Arbnum.fromInt 4
            then raise ERR "selective_v2w_eq_CONV" ""
         else bitstringLib.v2w_eq_CONV tm
      end
in
   val DecodeThumb =
      DecodeThumb_def
      |> Thm.SPEC (bitstringSyntax.mk_vec 16 0)
      |> Lib.C Thm.AP_THM st
      |> Conv.RIGHT_CONV_RULE
             (Thm.BETA_CONV
              THENC REWRITE_CONV [m0Theory.boolify16_v2w, Decode_simps]
              THENC ONCE_REWRITE_CONV [DecodeImmShift_rwt]
              THENC Conv.DEPTH_CONV PairedLambda.let_CONV
              THENC Conv.DEPTH_CONV selective_v2w_eq_CONV
              THENC SIMP_CONV bool_ss
                      ([pairTheory.FST, Decode_simps, BitCount,
                        bit_count_lt_1] @ DECODE_UNPREDICTABLE_rwt)
              THENC Conv.DEPTH_CONV utilsLib.WGROUND_CONV
              THENC REWRITE_CONV [DecodeRegShift_rwt]
              THENC Conv.DEPTH_CONV PairedLambda.PAIRED_BETA_CONV)
end

val DecodeThumb2 =
   DecodeThumb2_def
   |> Thm.SPEC
        (pairSyntax.mk_pair
           (bitstringSyntax.mk_vec 16 16, bitstringSyntax.mk_vec 16 0))
   |> Lib.C Thm.AP_THM st
   |> Conv.RIGHT_CONV_RULE
          (Thm.BETA_CONV
           THENC PURE_REWRITE_CONV [pairTheory.FST, pairTheory.SND]
           THENC REWRITE_CONV [m0Theory.boolify16_v2w, Decode_simps]
           THENC Conv.DEPTH_CONV PairedLambda.let_CONV
           THENC Conv.DEPTH_CONV bitstringLib.v2w_eq_CONV
           THENC SIMP_CONV bool_ss DECODE_UNPREDICTABLE_rwt)

local
   val v1 = fst (bitstringSyntax.dest_v2w (bitstringSyntax.mk_vec 16 0))
   val v2 = fst (bitstringSyntax.dest_v2w (bitstringSyntax.mk_vec 32 0))
   val lem = utilsLib.SRW_CONV [] ``(s with pcinc := x).PSR``
   val rule =
      Conv.RIGHT_CONV_RULE
         (REWRITE_CONV [v2w_ground2, v2w_ground4]
          THENC utilsLib.WGROUND_CONV
          THENC REWRITE_CONV (lem :: iConditionPassed_rwts))
in
   fun DecodeThumb_rwt pat =
      let
         val (thm, s) =
             (DecodeThumb,
              state_with_pcinc ``2w:word32`` :: fst (Term.match_term v1 pat))
             handle HOL_ERR {message = "different constructors",
                             origin_function = "raw_match_term", ...} =>
             (DecodeThumb2,
              state_with_pcinc ``4w:word32`` :: fst (Term.match_term v2 pat))
      in
         rule (Thm.INST s thm)
      end
end

(* -- *)

val thumb_patterns = List.map (I ## utilsLib.pattern)
  [("ADDS",            "FFFTTFF_________"),
   ("SUBS",            "FFFTTFT_________"),
   ("ADDS (imm3)",     "FFFTTTF_________"),
   ("SUBS (imm3)",     "FFFTTTT_________"),
   ("LSLS (imm)",      "FFFFF___________"),
   ("LSRS (imm)",      "FFFFT___________"),
   ("ASRS (imm)",      "FFFTF___________"),
   ("MOVS",            "FFTFF___________"),
   ("CMP (imm)",       "FFTFT___________"),
   ("ADDS (imm)",      "FFTTF___________"),
   ("SUBS (imm)",      "FFTTT___________"),
   ("ANDS",            "FTFFFFFFFF______"),
   ("EORS",            "FTFFFFFFFT______"),
   ("LSLS",            "FTFFFFFFTF______"),
   ("LSRS",            "FTFFFFFFTT______"),
   ("ASRS",            "FTFFFFFTFF______"),
   ("ADCS",            "FTFFFFFTFT______"),
   ("SBCS",            "FTFFFFFTTF______"),
   ("RORS",            "FTFFFFFTTT______"),
   ("TST",             "FTFFFFTFFF______"),
   ("RSBS",            "FTFFFFTFFT______"),
   ("CMP",             "FTFFFFTFTF______"),
   ("CMN",             "FTFFFFTFTT______"),
   ("ORRS",            "FTFFFFTTFF______"),
   ("MULS",            "FTFFFFTTFT______"),
   ("BICS",            "FTFFFFTTTF______"),
   ("MVNS",            "FTFFFFTTTT______"),
   ("ADD",             "FTFFFTFF________"),
   ("ADD (pc)",        "FTFFFTFFT____TTT"),
   ("CMP (high)",      "FTFFFTFT________"),
   ("MOV",             "FTFFFTTF________"),
   ("MOV (pc)",        "FTFFFTTFT____TTT"),
   ("BX",              "FTFFFTTTF_______"),
   ("BLX",             "FTFFFTTTT_______"),
   ("LDR (lit)",       "FTFFT___________"),
   ("STR",             "FTFTFFF_________"),
   ("STRH",            "FTFTFFT_________"),
   ("STRB",            "FTFTFTF_________"),
   ("LDRSB",           "FTFTFTT_________"),
   ("LDR",             "FTFTTFF_________"),
   ("LDRH",            "FTFTTFT_________"),
   ("LDRB",            "FTFTTTF_________"),
   ("LDRSH",           "FTFTTTT_________"),
   ("STR (imm)",       "FTTFF___________"),
   ("LDR (imm)",       "FTTFT___________"),
   ("STRB (imm)",      "FTTTF___________"),
   ("LDRB (imm)",      "FTTTT___________"),
   ("STRH (imm)",      "TFFFF___________"),
   ("LDRH (imm)",      "TFFFT___________"),
   ("STR (sp)",        "TFFTF___________"),
   ("LDR (sp)",        "TFFTT___________"),
(* ("ADD (reg,pc)",    "TFTFF___________"), *)
   ("ADD (sp)",        "TFTFT___________"),
   ("ADD (sp,sp)",     "TFTTFFFFF_______"),
   ("SUB (sp,sp)",     "TFTTFFFFT_______"),
   ("SXTH",            "TFTTFFTFFF______"),
   ("UXTH",            "TFTTFFTFTF______"),
   ("SXTB",            "TFTTFFTFFT______"),
   ("UXTB",            "TFTTFFTFTT______"),
   ("PUSH",            "TFTTFTF_________"),
   ("REV",             "TFTTTFTFFF______"),
   ("REV16",           "TFTTTFTFFT______"),
   ("REVSH",           "TFTTTFTFTT______"),
   ("POP",             "TFTTTTFF________"),
   ("POP (pc)",        "TFTTTTFT________"),
   ("NOP",             "TFTTTTTTFFFFFFFF"),
   ("STM",             "TTFFF___________"),
   ("LDM",             "TTFFT___________"),
   ("BEQ",             "TTFTFFFF________"),
   ("BNE",             "TTFTFFFT________"),
   ("BCS",             "TTFTFFTF________"),
   ("BCC",             "TTFTFFTT________"),
   ("BMI",             "TTFTFTFF________"),
   ("BPL",             "TTFTFTFT________"),
   ("BVS",             "TTFTFTTF________"),
   ("BVC",             "TTFTFTTT________"),
   ("BHI",             "TTFTTFFF________"),
   ("BLS",             "TTFTTFFT________"),
   ("BGE",             "TTFTTFTF________"),
   ("BLT",             "TTFTTFTT________"),
   ("BGT",             "TTFTTTFF________"),
   ("BLE",             "TTFTTTFT________"),
   ("B",               "TTTFF___________")
  ]

val thumb2_patterns = List.map (I ## utilsLib.pattern)
  [("BL",    "TTTTF___________TT_T____________")
  ]

(* -- *)

local
   val sep1 = String.tokens (Lib.equal #",")
   val sep2 = String.tokens (fn c => c = #"-" orelse Char.isSpace c)
   fun err s = raise ERR "index" ("bad index: " ^ s)
   fun index s = case Int.fromString s of
                    SOME i => (i < 16 orelse err s; i)
                  | NONE => err s
   fun reg_array s =
      let
         val a = Array.array (16, boolSyntax.F)
         fun set i = Array.update (a, i, boolSyntax.T)
      in
         List.app
            (fn r => case sep2 r of
                        [i] => set (index i)
                      | [i, j] =>
                          let
                             val x = index i
                             val y = index j
                          in
                             Lib.for_se (Int.min (x, y)) (Int.max (x, y)) set
                          end
                      | _ => raise ERR "reg_array" "syntax error") (sep1 s)
          ; a
      end
in
   fun reg_list_subst (n, p) s =
      let
         val a = reg_array s
      in
         List.tabulate
           (n, fn i => Term.mk_var ("x" ^ Int.toString (i + p), Type.bool) |->
                       Array.sub (a, n - 1 - i))
      end
end

local
   val thumb_pats =
      Redblackmap.fromList String.compare
         (thumb_patterns @ List.map (I ## split_thumb2_pat) thumb2_patterns)
   fun printn s = TextIO.print (s ^ "\n")
   fun lsub s i = Char.toUpper (String.sub (s, i))
   val splitAtSemi = utilsLib.splitAtChar (Lib.equal #";")
   fun sharePrefix3 s1 s2 =
      let
         val n = Int.min (3, Int.min (String.size s1, String.size s2))
         val f1 = lsub s1
         val f2 = lsub s2
         fun loop i = i >= n orelse f1 i = f2 i andalso loop (i + 1)
      in
         loop 0
      end
   fun LDM_STM s = String.isPrefix "LDM" s orelse String.isPrefix "STM" s
   fun comma i =
      let
         val is = Int.toString i
      in
         fn "" => is
          | s => is ^ "," ^ s
      end
   val reglist =
      snd o
      List.foldr
        (fn (t, (i, s)) =>
           (i + 1, if Teq t then comma i s else s)) (0, "")
   fun insertRegList i =
      fn "PUSH" => let
                      val l = List.drop (i, 7)
                      val lr = bitstringSyntax.dest_b (hd l)
                   in
                      "PUSH;" ^ (if lr then "14," else "") ^ reglist (tl l)
                   end
       | "LDM" => let
                     val l = List.drop (i, 5)
                     val rn = List.take (l, 3)
                              |> List.map bitstringSyntax.dest_b
                              |> bitstringSyntax.bitlist_to_num
                              |> Arbnum.toInt
                     val registers = List.drop (l, 3)
                     val wb = not (bitstringSyntax.dest_b
                                      (List.nth (registers, 7 - rn)))
                  in
                     (if wb then "LDM (wb);" else "LDM;") ^ reglist registers
                  end
       | s => if Lib.mem s ["POP", "POP (pc)", "STM"]
                 then s ^ ";" ^ reglist (List.drop (i, 8))
              else s
in
   fun list_instructions () = Redblackmap.listItems thumb_pats
   val list_mnemonics = List.map fst o list_instructions
   val print_instructions = List.app printn o list_mnemonics
   fun mk_thumb_opcode s =
      let
         val (s1, s2) = splitAtSemi s
         val s1 = if s1 = "LDM (wb)" then "LDM" else s1
         val m = if s2 = ""
                    then []
                 else let
                         val s3 = String.extract (s2, 1, NONE)
                      in
                         if LDM_STM s1
                            then reg_list_subst (8, 3) s3
                         else if s1 = "PUSH"
                            then [hd (reg_list_subst (15, 0) s3)] @
                                 reg_list_subst (8, 1) s3
                         else if String.isPrefix "POP" s1
                            then reg_list_subst (8, 0) s3
                         else raise ERR "mk_thumb_opcode" ("bad suffix: " ^ s)
                      end
      in
         case Redblackmap.peek (thumb_pats, s1) of
            SOME pat => Term.subst m pat
          | NONE =>
              let
                 val p = list_mnemonics ()
                         |> List.filter (sharePrefix3 s1)
                         |> Lib.commafy
                         |> String.concat
                 val p = if p = "" then "." else ". Try: " ^ p
              in
                 raise ERR "mk_arm_opcode" ("Not found: " ^ s1 ^ p)
              end
      end
   fun thumb_instruction opc =
      let
         val f = case Lib.total listSyntax.dest_list opc of
                    SOME (i, _) => insertRegList i
                  | NONE => Lib.I
         fun mtch s = Term.match_term (mk_thumb_opcode s) opc
      in
         case List.filter (Lib.can mtch) (list_mnemonics()) of
            [] => raise ERR "thumb_instruction" "no match found"
          | [s] => f s
          | ["ADD", s as "ADD (pc)"] => s
          | ["MOV", s as "MOV (pc)"] => s
          | _ => raise ERR "thumb_instruction" "more than one match!"
      end
end

(* -- *)

local
   fun f ps = List.map (DecodeThumb_rwt o snd) ps
   val rwts_16 = f thumb_patterns
   val rwts_32 = f thumb2_patterns
   val pcinc2 = fix_datatype ``^st with pcinc := 2w``
   val pcinc4 = fix_datatype ``^st with pcinc := 4w``
   val DecodeThumb_tm = mk_arm_const "DecodeThumb"
   val DecodeThumb2_tm = mk_arm_const "DecodeThumb2"
   fun mk_decode_thumb t =
      Term.list_mk_comb (DecodeThumb_tm, [t, pcinc2])
      handle HOL_ERR {message = "incompatible types", ...} =>
      Term.list_mk_comb (DecodeThumb2_tm, [t, pcinc4])
   val rewrites =
      [v2w_13_15_rwts,
       bitstringLib.v2n_CONV ``v2n [F;F;F;F;F]``,
       blastLib.BBLAST_PROVE
         ``((v2w [T;T;b;T] = 13w: word4) \/ (v2w [T;T;b;T] = 15w: word4)) = T``]
   val raise_tm = mk_arm_const "raise'exception"
   val avoid =
      List.filter
         (not o Lib.can (HolKernel.find_term (Term.same_const raise_tm) o rhsc))
   val FINISH_RULE =
      List.map
        (utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV [boolTheory.DE_MORGAN_THM]) o
         Conv.RIGHT_CONV_RULE
            (REG_CONV THENC Conv.DEPTH_CONV bitstringLib.v2n_CONV))
   val rwconv = REWRITE_CONV rewrites
in
   fun thumb_decode be =
      let
         val tms = endian be
         val x = (DATATYPE_CONV, fix_datatypes tms)
         fun gen_rws m r = rewrites @ utilsLib.specialized m x r
         val rw = REWRITE_CONV (gen_rws "decode Thumb" rwts_16 @
                                gen_rws "decode Thumb-2" rwts_32)
         val FALL_CONV =
            REWRITE_CONV
               (datatype_thms [v2w_ground4] @
                gen_rws "decode Thumb (fallback)" [DecodeThumb] @
                gen_rws "decode Thumb-2 (fallback)" [DecodeThumb2])
      in
         fn v =>
            let
               val tm = mk_decode_thumb (mk_opcode v)
            in
               (rw tm
                handle Conv.UNCHANGED =>
                           (WARN "arm_decode" "fallback (slow) decode"
                            ; FALL_CONV tm))
               |> utilsLib.split_conditions
               |> avoid
               |> FINISH_RULE
               |> (fn l => if List.null l
                              then raise ERR "thumb_decode"
                                         ("unpredictable: " ^
                                          utilsLib.long_term_to_string v)
                           else l)
            end
      end
end

fun thumb_decode_hex be =
   let
      val dec = thumb_decode be
   in
      dec o hex_to_bits
   end

(*

val be = false
val tst = Count.apply (thumb_decode true o mk_thumb_opcode)
val tst = Count.apply (thumb_decode_hex true)

tst "CMP"

tst "450F"
tst "9876"
tst "be01"
tst "B422"
tst "F000BFFE"

tst "ADDS";
tst "ADDS (imm3)";
tst "SUBS";
tst "SUBS (imm3)";
tst "ANDS";
tst "ADD";
tst "CMP";
tst "BEQ";

tst "PUSH";
tst "POP";
tst "STM";
tst "LDM";

tst "MOV"
tst "MOVS"


*)

(* ========================================================================= *)

(* Run *)

val NoOperation_rwt =
   EV [dfn'NoOperation_def, IncPC_rwt] [] []
      ``dfn'NoOperation()``
   |> addThms

(* ---------------------------- *)

local
   val f = rand o rand o rand o rator o utilsLib.lhsc
   val cnv = REWRITE_CONV [alignmentTheory.aligned_add_sub_123,
                           alignmentTheory.aligned_numeric]
 in
   val BranchTarget_rwt =
      EV [dfn'BranchTarget_def, PC_rwt, BranchWritePC_rwt,
          Aligned_Branch9, Aligned_Branch12, Aligned_Branch_Wide6,
          Aligned_Branch_Wide10] []
         [[`imm32` |-> f Aligned_Branch9],
          [`imm32` |-> f Aligned_Branch12],
          [`imm32` |-> f Aligned_Branch_Wide6],
          [`imm32` |-> f Aligned_Branch_Wide10]]
         ``dfn'BranchTarget imm32``
      |> List.map (utilsLib.ALL_HYP_CONV_RULE cnv)
      |> addThms
   val BranchLinkImmediate_rwt =
      EV [dfn'BranchLinkImmediate_def, BranchWritePC_rwt, R_name_rwt,
          write'LR_def, write'R_name_rwt, PC_rwt, R_x_pc, RName_LR_rwt,
          Aligned_Branch_Wide10, Aligned_BranchLink] []
         [[`imm32` |-> f Aligned_Branch_Wide10]]
         ``dfn'BranchLinkImmediate imm32``
      |> List.map (utilsLib.ALL_HYP_CONV_RULE
                      (EVAL_DATATYPE_CONV
                       THENC REWRITE_CONV [R_x_pc]
                       THENC utilsLib.WGROUND_CONV
                       THENC cnv) o
                   utilsLib.MATCH_HYP_CONV_RULE wordsLib.WORD_EVAL_CONV
                      ``~(n2w a = b: word4)``)
      |> addThms
end

(* ---------------------------- *)

val BranchExchange_rwt =
   EV [dfn'BranchExchange_def, BXWritePC_rwt, R_name_rwt]
      [] []
      ``dfn'BranchExchange m``
   |> List.map (MATCH_HYP_RW [] ``word_bit x (y: word32)``)
   |> addThms

(* ---------------------------- *)

val BranchLinkExchangeRegister_rwt =
   EV [dfn'BranchLinkExchangeRegister_def, BLXWritePC_rwt, R_name_rwt,
       write'LR_def, write'R_name_rwt, PC_rwt, RName_LR_rwt,
       Aligned_BranchLinkEx] [] []
      ``dfn'BranchLinkExchangeRegister m``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV []) o
                utilsLib.MATCH_HYP_CONV_RULE wordsLib.WORD_EVAL_CONV
                   ``~(n2w a = b: word4)``)
   |> addThms

(* ---------------------------- *)

local
   val rwt =
      utilsLib.qm [wordsTheory.SHIFT_ZERO]
        ``(if n = 0 then (x: 'a word,s) else (x #>> n, ^st)) = (x #>> n, s)``
in
   val ROR_rwt =
      EV [ROR_def, ROR_C_def] [] []
         ``ROR (x: 'a word, n)``
         |> hd
         |> SIMP_RULE bool_ss [rwt]
end

(* ---------------------------- *)

val () = setEvConv utilsLib.WGROUND_CONV

local
   val DataProcessing_rwts =
      List.map
         (fn opc =>
            let
               val i = wordsSyntax.uint_of_word opc
               val w = if 8 <= i andalso i <= 11 then [] else [write'R_name_rwt]
            in
               EV ([R_name_rwt, m0_stepTheory.R_x_not_pc,
                    utilsLib.SET_RULE DataProcessing_def, DataProcessingALU_def,
                    AddWithCarry, wordsTheory.FST_ADD_WITH_CARRY,
                    ArithmeticOpcode_def, PC_rwt, IncPC_rwt, cond_rand_thms] @
                   w)
                  [] [[`opc` |-> opc]]
                  ``DataProcessing (opc, setflags, d, n, imm32, c)``
               |> List.map (DATATYPE_RULE o COND_UPDATE_RULE)
            end) opcodes
in
   fun dp n = hd (List.nth (DataProcessing_rwts, n))
end

val tst = dp 8
val cmp = dp 10
val cmn = dp 11
val mov = dp 13
val mvn = dp 15
fun al () = List.tabulate (8, fn i => dp i) @ [dp 12, dp 14]

(* ---------------------------- *)

val psr_id =
   Thm.CONJ
     (utilsLib.mk_state_id_thm m0Theory.PSR_component_equality
         [["C", "N", "Z"], ["N"], ["Z"], ["C"], ["V"]])
     (utilsLib.mk_state_id_thm m0Theory.m0_state_component_equality
         [["PSR", "REG", "count"],
          ["PSR", "REG", "count", "pcinc"]])

val Move_rwt =
   EV [dfn'Move_def, mov, bitstringTheory.word_concat_v2w_rwt,
       wordsTheory.WORD_OR_CLAUSES, psr_id] [[``d <> 13w:word4``]] []
      ``dfn'Move (d, imm32)``
      |> addThms

val CompareImmediate_rwt =
   EV [dfn'CompareImmediate_def, cmp, bitstringTheory.word_concat_v2w_rwt] [] []
      ``dfn'CompareImmediate (n, imm32)``
      |> addThms

val ArithLogicImmediate_rwt =
   EV ([dfn'ArithLogicImmediate_def, bitstringTheory.word_concat_v2w_rwt,
        psr_id] @ al()) [] (mapl (`op`, arithlogic))
      ``dfn'ArithLogicImmediate (op, s, d, n, imm32)``
      |> addThms

val ShiftImmediate_rwt =
   EV [dfn'ShiftImmediate_def, R_name_rwt, mov,
       doRegister_def, ArithmeticOpcode_def, Shift_C_DecodeImmShift_rwt,
       wordsTheory.WORD_OR_CLAUSES] [[``d <> 13w:word4``]]
       [[`a` |-> boolSyntax.F, `b` |-> boolSyntax.F],
        [`a` |-> boolSyntax.F, `b` |-> boolSyntax.T],
        [`a` |-> boolSyntax.T, `b` |-> boolSyntax.F]]
      ``dfn'ShiftImmediate
          (F, T, d, m,
           FST (DecodeImmShift (v2w [a; b], imm5)),
           SND (DecodeImmShift (v2w [a; b], imm5)))``
      |> List.map
            (Conv.CONV_RULE
                (Conv.LHS_CONV
                    (REWRITE_CONV []
                     THENC Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)))
      |> addThms

val MoveRegister_rwt =
   EV [dfn'ShiftImmediate_def, R_name_rwt, mov, psr_id,
       doRegister_def, ArithmeticOpcode_def,
       Shift_C_LSL_rwt, SND_Shift_C_rwt] [[``d <> 15w:word4``]] []
      ``dfn'ShiftImmediate (F, F, d, m, SRType_LSL, 0)``
      |> addThms

val MoveRegister_pc_rwt =
   EV [dfn'ShiftImmediate_def, R_name_rwt, ALUWritePC_rwt,
       doRegister_def, DataProcessingPC_def, DataProcessingALU_def,
       Shift_C_LSL_rwt, SND_Shift_C_rwt] [] []
      ``dfn'ShiftImmediate (F, F, 15w, m, SRType_LSL, 0)``
      |> addThms

val MoveNegRegister_rwt =
   EV [dfn'ShiftImmediate_def, R_name_rwt, mvn, psr_id,
       doRegister_def, ArithmeticOpcode_def,
       Shift_C_LSL_rwt, SND_Shift_C_rwt] [[``d <> 13w:word4``]] []
      ``dfn'ShiftImmediate (T, T, d, m, SRType_LSL, 0)``
      |> addThms

val Register_rwt =
   EV ([dfn'Register_def, R_name_rwt, doRegister_def, ArithmeticOpcode_def,
        Shift_C_LSL_rwt, psr_id] @ al())
      [[``d <> 15w:word4``]] (mapl (`op`, arithlogic))
         ``dfn'Register (op, setflags, d, n, m)``
      |> addThms

val Register_add_pc_rwt =
   EV [dfn'Register_def, R_name_rwt, doRegister_def, ALUWritePC_rwt, PC_rwt,
       DataProcessingPC_def, DataProcessingALU_def, Shift_C_LSL_rwt,
       AddWithCarry, wordsTheory.FST_ADD_WITH_CARRY]
      [] []
      ``dfn'Register (4w, F, 15w, 15w, m)``
      |> addThms

val TestCompareRegister_rwt =
   EV ([dfn'TestCompareRegister_def, R_name_rwt, doRegister_def,
        ArithmeticOpcode_def, Shift_C_LSL_rwt, psr_id, cmp, tst, cmn] @ al())
      [] (mapl (`op`, testcompare))
         ``dfn'TestCompareRegister (op, n, m)``
      |> addThms

val ShiftRegister_rwt =
   EV [dfn'ShiftRegister_def, R_name_rwt, mov, mvn, ArithmeticOpcode_def,
       Shift_C_typ `F` `F`, Shift_C_typ `F` `T`,
       Shift_C_typ `T` `F`, Shift_C_typ `T` `T`]
      [[``d <> 13w:word4``]]
      (mapl (`typ`, [``SRType_LSL``, ``SRType_LSR``,
                     ``SRType_ASR``, ``SRType_ROR``]))
      ``dfn'ShiftRegister (d, n, typ, m)``
      |> addThms

(* ---------------------------- *)

val Multiply32_rwt =
   EV [dfn'Multiply32_def, R_name_rwt, write'R_name_rwt,
       m0_stepTheory.R_x_not_pc, IncPC_rwt]
      [[``d <> 13w:word4``]] []
      ``dfn'Multiply32 (d, n, m)``
      |> addThms

(* ---------------------------- *)

val ExtendByte_rwt =
   EV [dfn'ExtendByte_def, R_name_rwt, write'R_name_rwt,
       m0_stepTheory.R_x_not_pc, IncPC_rwt]
      [[``d <> 13w:word4``]] []
     ``dfn'ExtendByte (u, d, m)``
      |> addThms

val ExtendHalfword_rwt =
   EV [dfn'ExtendHalfword_def, R_name_rwt, write'R_name_rwt,
       m0_stepTheory.R_x_not_pc, IncPC_rwt]
      [[``d <> 13w:word4``]] []
      ``dfn'ExtendHalfword (u, d, m)``
      |> addThms

val ByteReverse_rwt =
   EV [dfn'ByteReverse_def, R_name_rwt, write'R_name_rwt,
       m0_stepTheory.R_x_not_pc, IncPC_rwt]
      [[``d <> 13w:word4``]] []
      ``dfn'ByteReverse (d, m)``
      |> addThms

val ByteReversePackedHalfword_rwt =
   EV [dfn'ByteReversePackedHalfword_def, R_name_rwt,
       m0_stepTheory.R_x_not_pc, write'R_name_rwt,
       IncPC_rwt] [[``d <> 13w:word4``]] []
      ``dfn'ByteReversePackedHalfword (d, m)``
      |> addThms

val ByteReverseSignedHalfword_rwt =
   EV [dfn'ByteReverseSignedHalfword_def, R_name_rwt,
       m0_stepTheory.R_x_not_pc, write'R_name_rwt,
       IncPC_rwt] [[``d <> 13w:word4``]] []
      ``dfn'ByteReverseSignedHalfword (d, m)``
      |> addThms

(* ---------------------------- *)

val Extend_rwt =
   utilsLib.map_conv (REWRITE_CONV [Extend_def])
      [``Extend (T, w:'a word): 'b word``,
       ``Extend (F, w:'a word): 'b word``]

val Extract_rwt =
   utilsLib.map_conv utilsLib.EXTRACT_CONV
      [``(15 >< 8) ((15 >< 0) (w: word32) : word16) : word8``,
       ``(7 >< 0) ((15 >< 0) (w: word32) : word16) : word8``]

fun memEV ctxt tm =
   EV [dfn'LoadWord_def, dfn'LoadLiteral_def,
       dfn'LoadByte_def, dfn'LoadHalf_def,
       dfn'StoreWord_def, dfn'StoreByte_def, dfn'StoreHalf_def,
       MemU_1_rwt, MemU_2_rwt, MemU_4_rwt,
       write'MemU_1_rwt, write'MemU_2_rwt, write'MemU_4_rwt,
       PC_rwt, IncPC_rwt, write'R_name_rwt, R_name_rwt,
       m0_stepTheory.R_x_not_pc, m0Theory.offset_case_def,
       pairTheory.pair_case_thm, Shift_C_DecodeImmShift_rwt, Shift_C_LSL_rwt,
       alignmentTheory.aligned_add_sub_123, Shift_def, Extend_rwt, Extract_rwt]
      [[``t <> 13w:word4``]] ctxt tm
    |> List.map (utilsLib.ALL_HYP_CONV_RULE
                   (REWRITE_CONV []
                    THENC utilsLib.INST_REWRITE_CONV [Aligned4_base_pc]))
    |> addThms

(* ---------------------------- *)

val LoadWord_rwt =
   memEV [[`mode` |-> ``immediate_form imm32``],
          [`mode` |-> ``register_form m``]]
        ``dfn'LoadWord (t, n, mode)``

val LoadLiteral_rwt =
   memEV []
     ``dfn'LoadLiteral
         (t, w2w (v2w [b7; b6; b5; b4; b3; b2; b1; b0; F; F] : word10))``

(* ---------------------------- *)

val LoadByte_rwts =
   memEV [[`mode` |-> ``immediate_form imm32``],
          [`mode` |-> ``register_form m``]]
     ``dfn'LoadByte (T, t, n, mode)``

val LoadSignedByte_rwts =
   memEV [[`mode` |-> ``immediate_form imm32``],
          [`mode` |-> ``register_form m``]]
     ``dfn'LoadByte (F, t, n, mode)``

(* ---------------------------- *)

val LoadHalf_rwts =
   memEV [[`mode` |-> ``immediate_form imm32``],
          [`mode` |-> ``register_form m``]]
     ``dfn'LoadHalf (T, t, n, mode)``

val LoadSignedHalf_rwts =
   memEV [[`mode` |-> ``immediate_form imm32``],
          [`mode` |-> ``register_form m``]]
     ``dfn'LoadHalf (F, t, n, mode)``

(* ---------------------------- *)

val StoreWord_rwt =
   memEV [[`mode` |-> ``immediate_form imm32``],
          [`mode` |-> ``register_form m``]]
     ``dfn'StoreWord (t, n, mode)``

(* ---------------------------- *)

val StoreByte_rwt =
   memEV [[`mode` |-> ``immediate_form imm32``],
          [`mode` |-> ``register_form m``]]
     ``dfn'StoreByte (t, n, mode)``

(* ---------------------------- *)

val StoreHalf_rwt =
   memEV [[`mode` |-> ``immediate_form imm32``],
          [`mode` |-> ``register_form m``]]
     ``dfn'StoreHalf (t, n, mode)``

val () = resetEvConv ()

(* ========================================================================= *)

(* Evaluator *)

local
   val word_bit_8 =
      bitstringLib.word_bit_CONV
         ``word_bit 8 (v2w [b8; b7; b6; b5; b4; b3; b2; b1; b0] : word9)``
   val both_rwts = [v2w_13_15_rwts]
   val hyps_rwts = word_bit_8 :: both_rwts
   val conc_rwts = [LDM_UPTO_RUN, STM_UPTO_RUN, Extend_rwt, psr_id] @ both_rwts
   val eval_simp_rule =
      REWRITE_RULE conc_rwts o
      utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV hyps_rwts)
   fun ev tm =
      fn rwt =>
         let
            val thm = eval_simp_rule (utilsLib.INST_REWRITE_CONV1 rwt tm)
         in
            if utilsLib.vacuous thm then NONE else SOME thm
         end
in
   fun eval pcinc tms =
      let
         val net = utilsLib.mk_rw_net utilsLib.lhsc (getThms pcinc tms)
      in
         fn tm =>
            (case List.mapPartial (ev tm) (utilsLib.find_rw net tm) of
                [] => raise ERR "eval" "no valid step theorem"
              | [x] => x
              | l => (Parse.print_term tm
                      ; print "\n"
                      ; raise ERR "eval" "more than one valid step theorem"))
            handle HOL_ERR {message = "not found",
                            origin_function = "find_rw", ...} =>
               raise (Parse.print_term tm
                      ; print "\n"
                      ; ERR "eval" "instruction instance not supported")
      end
end

local
   val u2 = wordsSyntax.mk_wordii (2, 32)
   val u4 = wordsSyntax.mk_wordii (4, 32)
   val get_val = fst o pairSyntax.dest_pair o rhsc
   val get_state = rhsc
   val state_exception_tm =
       mk_arm_const $
         TypeBasePure.mk_recordtype_fieldsel
           {tyname = "m0_state", fieldname = "exception"}
   fun mk_proj_exception r = Term.mk_comb (state_exception_tm, r)
   val MP_Next1 = Drule.MATCH_MP m0_stepTheory.NextStateM0_thumb
   val MP_Next2 = Drule.MATCH_MP m0_stepTheory.NextStateM0_thumb2
   val Run_CONV = utilsLib.Run_CONV ("m0", st) o get_val
   fun is_ineq tm =
      boolSyntax.is_eq (boolSyntax.dest_neg tm) handle HOL_ERR _ => false
in
   fun eval_thumb (be, sel) =
      let
         val tms = endian be @ spsel sel
         val ftch = fetch be
         val dec = thumb_decode be
         val run1 = (MP_Next1, eval u2 tms o Term.subst [state_with_pcinc u2])
         val run2 = (MP_Next2, eval u4 tms o Term.subst [state_with_pcinc u4])
      in
         fn n => fn v =>
            let
               val (mp, run) = if pairSyntax.is_pair v then run2 else run1
               val thm1 = ftch v
               val thm2 = List.nth (dec v, n)
               val thm3 = Run_CONV thm2
               val thm4 = thm3 |> Drule.SPEC_ALL |> rhsc |> run
               val ineq_hyps =
                  List.mapPartial
                     (fn tm => if is_ineq tm then SOME (ASSUME tm) else NONE)
                     (Thm.hyp thm4)
               val (thm2, thm4) =
                  if List.null ineq_hyps
                     then (thm2, thm4)
                  else
                     (utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV ineq_hyps) thm2,
                      REWRITE_RULE ineq_hyps thm4)
               val r = get_state thm4
                       handle HOL_ERR {origin_function = "dest_pair", ...} =>
                         (Parse.print_thm thm4
                          ; print "\n"
                          ; raise ERR "eval_thumb" "failed to fully evaluate")
               val thm5 = STATE_CONV (mk_proj_exception r)
               val thm = Drule.LIST_CONJ [thm1, thm2, thm3, thm4, thm5]
            in
               mp thm
            end
      end
end

local
   val conditional = Redblackset.fromList String.compare
      ["BEQ", "BNE", "BCS", "BCC", "BMI", "BPL", "BVS",
       "BVC", "BHI", "BLS", "BGE", "BLT", "BGT", "BLE"]
   fun isConditional s =
      3 <= String.size s andalso
      Redblackset.member (conditional, String.extract (s, 0, SOME 3))
   fun mk_ev config =
      let
         val ev = eval_thumb config
      in
         fn (s, v) =>
            if isConditional s
               then [ev 1 v, ev 0 v]
            else [ldm_stm_rule s (ev 0 v)]
      end
in
   fun thumb_step config =
      let
         val ev = mk_ev config
      in
         fn s =>
            let
               val v = mk_thumb_opcode s
            in
               ev (s, v)
            end
      end
   fun thumb_step_hex config =
      let
         val ev = mk_ev config
      in
         fn h =>
            let
               val v = hex_to_bits h
            in
               ev (thumb_instruction v, v)
            end
      end
end

fun thumb_step_code config =
   List.map (thumb_step_hex config) o
   (m0AssemblerLib.m0_code: string quotation -> string list)

val _ = temp_set_grammars ambient_grammars

(* ---------------------------- *)

(* testing:

open m0_stepLib

val be = true
val sel = true
val config = (be, sel)
val n = 0
val v = mk_thumb_opcode "POP"

val fails = ref ([] : string list)
val ok = ref ([] : string list)

val evs = Lib.total (Count.apply (thumb_step (true, true)))
val dec = thumb_decode true o mk_thumb_opcode
fun tst s = case evs s of
               SOME thm => (ok := s :: (!ok); SOME (s, thm))
             | NONE => (fails := s :: (!fails); NONE)

val l =
  (fails := []
   ; ok := []
   ; List.mapPartial (tst o fst) (list_instructions()))

   (!ok)
   (!fails)

val evs = Count.apply (thumb_step (false, false))

evs "POP"
evs "POP (pc)"
evs "POP; 1, 0"
evs "POP (pc); 1, 0"
evs "LDM (wb);5,0"
evs "STM; 3, 1"
evs "STM; 3, 1"
evs "LDM"
evs "LDM; 4, 2"
evs "LDM (wb); 4, 2"
evs "BVS";

*)

end
