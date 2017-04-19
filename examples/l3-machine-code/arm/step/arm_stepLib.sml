(* ------------------------------------------------------------------------
   ARM step evaluator
   ------------------------------------------------------------------------ *)

structure arm_stepLib :> arm_stepLib =
struct

open HolKernel boolLib bossLib

open armTheory arm_stepTheory arm_configLib
open state_transformerSyntax blastLib

structure Parse =
struct
   open Parse
   val (tyg, (tmg, _)) =
      (I ## term_grammar.mfupdate_overload_info
               (Overload.remove_overloaded_form "add"))
      arm_stepTheory.arm_step_grammars
   val (Type, Term) = parse_from_grammars (tyg, tmg)
end

open Parse
val _ = Parse.hide "add"

val ERR = Feedback.mk_HOL_ERR "arm_stepLib"
val WARN = Feedback.HOL_WARNING "arm_stepLib"

val () = show_assums := true

(* ========================================================================= *)

val mk_byte = bitstringSyntax.mk_vec 8
val rhsc = utilsLib.rhsc
fun mapl x = utilsLib.augment x [[]]
val splitAtSpace = utilsLib.splitAtChar Char.isSpace
val a_of = utilsLib.accessor_fns o arm_configLib.mk_arm_type
val u_of = utilsLib.update_fns o arm_configLib.mk_arm_type

val REG_CONV = REWRITE_CONV [v2w_13_15_rwts, v2w_ground4]
val REG_RULE = Conv.CONV_RULE REG_CONV

val registers   = utilsLib.tab_fixedwidth 15 4
val opcodes     = utilsLib.list_mk_wordii 4 (List.tabulate (16, Lib.I))
val arithlogic  = utilsLib.list_mk_wordii 4 [0,1,2,3,4,5,6,7,12,14]
val testcompare = utilsLib.list_mk_wordii 4 (List.tabulate (4, fn i => i + 8))

local
   val c_of = TypeBase.constructors_of o arm_configLib.mk_arm_type
in
   val arches = c_of "Architecture"
   val isets  = c_of "InstrSet"
   val shifts = c_of "SRType"
   (* val encs   = c_of "Encoding" *)
end

(* ---------------------------- *)

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

(* ---------------------------- *)

(* ARM datatype theorems/conversions *)

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
val FULL_DATATYPE_RULE = utilsLib.FULL_CONV_RULE DATATYPE_CONV

val COND_UPDATE_CONV =
   REWRITE_CONV
     (utilsLib.qm [] ``!b. (if b then T else F) = b`` ::
      utilsLib.mk_cond_update_thms
         (List.map arm_configLib.mk_arm_type ["arm_state", "FP", "PSR"]))

val COND_UPDATE_RULE = Conv.CONV_RULE COND_UPDATE_CONV

val STATE_CONV =
   REWRITE_CONV (utilsLib.datatype_rewrites true "arm" ["arm_state"] @
                 [boolTheory.COND_ID, cond_rand_thms])

local
   val cmp = computeLib.bool_compset ()
   val () = computeLib.add_thms (datatype_thms [pairTheory.FST]) cmp
in
   val EVAL_DATATYPE_CONV = Conv.TRY_CONV (utilsLib.CHANGE_CBV_CONV cmp)
end

fun fix_datatype tm = rhsc (Conv.QCONV DATATYPE_CONV tm)
val fix_datatypes = List.map fix_datatype

fun specialized0 m tms =
    utilsLib.specialized m (Conv.ALL_CONV, fix_datatypes tms)
fun specialized1 m tms =
    utilsLib.specialized m (utilsLib.WGROUND_CONV, fix_datatypes tms)

fun state_with_enc e = (st |-> fix_datatype ``^st with Encoding := ^e``)

fun state_with_pre (c, e) =
   (st |->
    fix_datatype
      ``^st with <| CurrentCondition := ^c; Encoding := ^e; undefined := F |>``)

local
   val c = Term.mk_var ("c", wordsSyntax.mk_int_word_type 4)
   fun ADD_PRECOND_RULE e thm =
      FULL_DATATYPE_RULE (Thm.INST [state_with_pre (c, e)] thm)
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

val ArchVersion_CPSR_rwt = Q.prove(
   `!s c. ArchVersion () (s with CPSR := c) = ArchVersion () s`,
   lrw [ArchVersion_def]) |> DATATYPE_RULE

val () = setEvConv utilsLib.WGROUND_CONV

val SelectInstrSet_rwt =
   EV [SelectInstrSet_def, write'ISETSTATE_def, CurrentInstrSet_rwt]
      [] (mapl (`iset`, isets))
     ``SelectInstrSet iset``

(* register access *)

val () = resetEvConv ()

val PC_rwt =
   EV [PC_def, R_def, CurrentInstrSet_rwt, not_cond] [] []
      ``PC`` |> hd

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
   val R_rwt = Q.prove(
      `GoodMode (^st.CPSR.M) ==>
       ~^st.Extensions Extension_Security ==>
       ~^st.CPSR.J ==>
       (R n ^st = (if n = 15w then
                     ^st.REG RName_PC + if ^st.CPSR.T then 4w else 8w
                   else ^st.REG (R_mode (^st.CPSR.M) n), ^st))`,
      lrw [R_def, R_mode_def, CurrentInstrSet_rwt, in_ext, DISCH_ALL Rmode_rwt]
      \\ rfs [GoodMode_def]
      \\ blastLib.FULL_BBLAST_TAC
      )
      |> funpow 3 Drule.UNDISCH

   val write'R_rwt = Q.prove(
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
      \\ blastLib.FULL_BBLAST_TAC
      )
      |> funpow 5 Drule.UNDISCH

   val R15_rwt = Q.prove(
      `~^st.CPSR.J ==>
       (R 15w ^st = (^st.REG RName_PC + if ^st.CPSR.T then 4w else 8w, ^st))`,
      lrw [R_def, CurrentInstrSet_rwt] \\ fs []) |> Drule.UNDISCH
end

(* ---------------------------- *)

(* write PC *)

val BranchTo_rwt =
   EV [BranchTo_def] [] []
     ``BranchTo imm32`` |> hd

local
   val rwt = Q.prove (`!b. ((if b then 16 else 32) = 16n) = b`, rw [])
in
   val IncPC_rwt =
     EV [IncPC_def, BranchTo_rwt, ThisInstrLength_def, rwt] [] []
       ``IncPC ()``
       |> hd
end

local
   val a =
      ``(^st.Architecture <> ARMv4) /\ (^st.Architecture <> ARMv4T) /\
        (^st.Architecture <> ARMv5T) /\ (^st.Architecture <> ARMv5TE) \/
        aligned 2 (imm32: word32)``
   val rwt = a |> boolSyntax.mk_neg |> utilsLib.SRW_CONV [] |> Thm.SYM
in
   val BranchWritePC_rwt =
     EV [BranchWritePC_def, CurrentInstrSet_rwt, BranchTo_rwt,
         ArchVersion_rwts, arm_stepTheory.aligned_23, not_cond, rwt,
         Align_LoadWritePC]
        [[``^st.CPSR.T``], [``~^st.CPSR.T``, a]] []
        ``BranchWritePC imm32``
end

local
   val rwt =
      utilsLib.qm []
      ``(c ==> b) ==>
        ((if b then x:'a else if ~c then y else z) = (if b then x else y))``
      |> Drule.UNDISCH
in
   val BXWritePC_rwt =
      EV ([rwt, BXWritePC_def, BranchTo_rwt, CurrentInstrSet_rwt] @
          SelectInstrSet_rwt) [] []
       ``BXWritePC imm32`` |> hd
end

val align_aligned = UNDISCH_ALL (SPEC_ALL alignmentTheory.align_aligned)

local
   val rwt = Q.prove(
     `(^st.Architecture = ARMv4) \/ (^st.Architecture = ARMv4T) ==>
      (^st.Architecture <> ARMv4 /\ ^st.Architecture <> ARMv4T /\
       ^st.Architecture <> ARMv5T /\ ^st.Architecture <> ARMv5TE \/
       aligned 2 (imm32: word32) = aligned 2 imm32)`,
     lrw [] \\ lfs []) |> Drule.UNDISCH

   val LoadWritePC_rwt1 =
     EV [LoadWritePC_def, BXWritePC_rwt, CurrentInstrSet_rwt, ArchVersion_rwts]
        [[``^st.Architecture <> ARMv4 /\ ^st.Architecture <> ARMv4T``]] []
       ``LoadWritePC imm32``
       |> hd
       |> COND_UPDATE_RULE
       |> REWRITE_RULE [arm_stepTheory.Align_LoadWritePC]

   val LoadWritePC_rwt2 =
     EV [LoadWritePC_def, hd (BranchWritePC_rwt), CurrentInstrSet_rwt,
         ArchVersion_rwts, arm_stepTheory.Align_LoadWritePC]
        [[``~(^st.Architecture <> ARMv4 /\ ^st.Architecture <> ARMv4T)``]] []
       ``LoadWritePC imm32``
       |> hd
       |> utilsLib.ALL_HYP_CONV_RULE (SIMP_CONV bool_ss [])

   val LoadWritePC_rwt3 =
     EV [LoadWritePC_def, hd (tl (BranchWritePC_rwt)), CurrentInstrSet_rwt,
         ArchVersion_rwts, arm_stepTheory.Align_LoadWritePC, align_aligned]
        [[``~(^st.Architecture <> ARMv4 /\ ^st.Architecture <> ARMv4T)``]] []
       ``LoadWritePC imm32``
       |> hd
       |> utilsLib.ALL_HYP_CONV_RULE (SIMP_CONV bool_ss [])
       |> utilsLib.MATCH_HYP_CONV_RULE (PURE_REWRITE_CONV [rwt])
             ``a \/ b : bool``
in
   val LoadWritePC_rwt = [LoadWritePC_rwt1, LoadWritePC_rwt2, LoadWritePC_rwt3]
end

(* ---------------------------- *)

val NullCheckIfThumbEE_rwt =
   EV [NullCheckIfThumbEE_def, CurrentInstrSet_rwt] [] []
      ``NullCheckIfThumbEE n`` |> hd

(* read mem *)

fun fixwidth_for ty =
  bitstringTheory.fixwidth_id
    |> Q.ISPEC `w2v (w:^(ty_antiq (wordsSyntax.mk_word_type ty)))`
    |> REWRITE_RULE [bitstringTheory.length_w2v]
    |> Conv.CONV_RULE (Conv.DEPTH_CONV wordsLib.SIZES_CONV)
    |> Drule.GEN_ALL

val mem_rwt =
  EV ([mem_def, mem1_def, concat16, concat32, concat64,
       bitstringTheory.field_fixwidth] @
      List.map fixwidth_for [``:8``, ``:16``, ``:32``, ``:64``]) []
    (mapl (`n`, [``1n``,``2n``,``4n``,``8n``]))
    ``mem (a, n)``

val BigEndianReverse_rwt =
  EV [BigEndianReverse_def] [] (mapl (`n`, [``1n``,``2n``,``4n``,``8n``]))
    ``BigEndianReverse (v, n)``

local
   val rwts =
     [MemA_with_priv_def, cond_rand_thms, snd_exception_thms,
      wordsTheory.WORD_ADD_0, bitstringTheory.v2w_w2v,
      AlignedAlign, alignmentTheory.aligned_0, alignmentTheory.align_0] @
     mem_rwt @ BigEndianReverse_rwt
in
   val MemA_with_priv_1_rwt =
     EV (rwts @ [bitstringTheory.field_fixwidth, fixwidth_for ``:8``])
        [] []
       ``MemA_with_priv (v, 1, priv) : arm_state -> word8 # arm_state``
       |> hd

   val MemU_with_priv_1_rwt =
     EV (tl rwts @ [MemU_with_priv_def, MemA_with_priv_1_rwt])
        [] []
       ``MemU_with_priv (v, 1, priv) : arm_state -> word8 # arm_state``
       |> hd

   val MemA_with_priv_2_rwt =
     EV (extract16 :: rwts)
        [[``aligned 1 (v:word32)``]] []
       ``MemA_with_priv (v, 2, priv) : arm_state -> word16 # arm_state``
       |> hd

   val MemU_with_priv_2_rwt =
     EV ([extract16, MemU_with_priv_def, MemA_with_priv_2_rwt] @ tl rwts)
        [[``aligned 1 (v:word32)``]] []
       ``MemU_with_priv (v, 2, priv) : arm_state -> word16 # arm_state``
       |> hd

   val MemA_with_priv_4_rwt =
     EV (extract32 :: rwts)
        [[``aligned 2 (v:word32)``]] []
       ``MemA_with_priv (v, 4, priv) : arm_state -> word32 # arm_state``
       |> hd

   val MemU_with_priv_4_rwt =
     EV ([extract16, MemU_with_priv_def, MemA_with_priv_4_rwt] @ tl rwts)
        [[``aligned 2 (v:word32)``]] []
       ``MemU_with_priv (v, 4, priv) : arm_state -> word32 # arm_state``
       |> hd

   val MemA_with_priv_8_rwt =
     EV (extract64 :: rwts)
        [[``aligned 3 (v:word32)``]] []
       ``MemA_with_priv (v, 8, priv) : arm_state -> word64 # arm_state``
       |> hd

   val MemU_with_priv_8_rwt =
     EV ([extract16, MemU_with_priv_def, MemA_with_priv_8_rwt] @ tl rwts)
        [[``aligned 3 (v:word32)``]] []
       ``MemU_with_priv (v, 8, priv) : arm_state -> word64 # arm_state``
       |> hd
end

val MemA_unpriv_1_rwt =
   EV [MemA_unpriv_def, MemA_with_priv_1_rwt] [] []
    ``MemA_unpriv (v, 1) : arm_state -> word8 # arm_state``

val MemU_unpriv_1_rwt =
   EV [MemU_unpriv_def, MemU_with_priv_1_rwt] [] []
    ``MemU_unpriv (v, 1) : arm_state -> word8 # arm_state``

val MemA_unpriv_2_rwt =
   EV [MemA_unpriv_def, MemA_with_priv_2_rwt] [] []
    ``MemA_unpriv (v, 2) : arm_state -> word16 # arm_state``

val MemU_unpriv_2_rwt =
   EV [MemU_unpriv_def, MemU_with_priv_2_rwt] [] []
    ``MemU_unpriv (v, 2) : arm_state -> word16 # arm_state``

val MemA_unpriv_4_rwt =
   EV [MemA_unpriv_def, MemA_with_priv_4_rwt] [] []
    ``MemA_unpriv (v, 4) : arm_state -> word32 # arm_state``

val MemU_unpriv_4_rwt =
   EV [MemU_unpriv_def, MemU_with_priv_4_rwt] [] []
    ``MemU_unpriv (v, 4) : arm_state -> word32 # arm_state``

val MemA_unpriv_8_rwt =
   EV [MemA_unpriv_def, MemA_with_priv_8_rwt] [] []
    ``MemA_unpriv (v, 8) : arm_state -> word64 # arm_state``

val MemU_unpriv_8_rwt =
   EV [MemU_unpriv_def, MemU_with_priv_8_rwt] [] []
    ``MemU_unpriv (v, 8) : arm_state -> word64 # arm_state``

val MemA_1_rwt =
   EV [MemA_def, MemA_with_priv_1_rwt, CurrentModeIsNotUser_def, BadMode] [] []
    ``MemA (v, 1) : arm_state -> word8 # arm_state``

val MemU_1_rwt =
   EV [MemU_def, MemU_with_priv_1_rwt, CurrentModeIsNotUser_def, BadMode] [] []
    ``MemU (v, 1) : arm_state -> word8 # arm_state``

val MemA_2_rwt =
   EV [MemA_def, MemA_with_priv_2_rwt, CurrentModeIsNotUser_def, BadMode] [] []
    ``MemA (v, 2) : arm_state -> word16 # arm_state``

val MemU_2_rwt =
   EV [MemU_def, MemU_with_priv_2_rwt, CurrentModeIsNotUser_def, BadMode] [] []
    ``MemU (v, 2) : arm_state -> word16 # arm_state``

val MemA_4_rwt =
   EV [MemA_def, MemA_with_priv_4_rwt, CurrentModeIsNotUser_def, BadMode] [] []
    ``MemA (v, 4) : arm_state -> word32 # arm_state``

val MemU_4_rwt =
   EV [MemU_def, MemU_with_priv_4_rwt, CurrentModeIsNotUser_def, BadMode] [] []
    ``MemU (v, 4) : arm_state -> word32 # arm_state``

val MemA_8_rwt =
   EV [MemA_def, MemA_with_priv_8_rwt, CurrentModeIsNotUser_def, BadMode] [] []
    ``MemA (v, 8) : arm_state -> word64 # arm_state``

val MemU_8_rwt =
   EV [MemU_def, MemU_with_priv_8_rwt, CurrentModeIsNotUser_def, BadMode] [] []
    ``MemU (v, 8) : arm_state -> word64 # arm_state``

(* ---------------------------- *)

(* write mem *)

val write'mem_rwt =
  EV ([write'mem_def]) [] (mapl (`n`, [``1n``,``2n``,``4n``,``8n``]))
    ``write'mem (v, a, n)``

local
   val field_cond_rand = Drule.ISPEC ``field h l`` boolTheory.COND_RAND
   val rwts =
     [write'MemA_with_priv_def, cond_rand_thms, snd_exception_thms,
      wordsTheory.WORD_ADD_0, bitstringTheory.v2w_w2v, field_cond_rand,
      AlignedAlign, alignmentTheory.aligned_0, alignmentTheory.align_0] @
     write'mem_rwt @ BigEndianReverse_rwt
in
   val write'MemA_with_priv_1_rwt =
     EV (rwts @ [fixwidth_for ``:8``, bitstringTheory.field_fixwidth]) [] []
       ``write'MemA_with_priv (w: word8, v, 1, priv)``
       |> hd

   val write'MemU_with_priv_1_rwt =
     EV (tl rwts @
         [write'MemU_with_priv_def, write'MemA_with_priv_1_rwt, Align])
        [] []
       ``write'MemU_with_priv (w: word8, v, 1, priv)``
       |> hd

   val write'MemA_with_priv_2_rwt =
     EV (field16 :: rwts) [[``aligned 1 (v:word32)``]] []
       ``write'MemA_with_priv (w:word16, v, 2, priv)``
       |> hd

   val write'MemU_with_priv_2_rwt =
     EV ([write'MemU_with_priv_def, write'MemA_with_priv_2_rwt] @ tl rwts)
        [[``aligned 1 (v:word32)``]] []
       ``write'MemU_with_priv (w: word16, v, 2, priv)``
       |> hd

   val write'MemA_with_priv_4_rwt =
     EV (field32 :: rwts) [[``aligned 2 (v:word32)``]] []
       ``write'MemA_with_priv (w:word32, v, 4, priv)``
       |> hd

   val write'MemU_with_priv_4_rwt =
     EV ([write'MemU_with_priv_def, write'MemA_with_priv_4_rwt] @ tl rwts)
        [[``aligned 2 (v:word32)``]] []
       ``write'MemU_with_priv (w: word32, v, 4, priv)``
       |> hd
end

val write'MemA_unpriv_1_rwt =
   EV [write'MemA_unpriv_def, write'MemA_with_priv_1_rwt] [] []
    ``write'MemA_unpriv (w: word8, v, 1)``

val write'MemU_unpriv_1_rwt =
   EV [write'MemU_unpriv_def, write'MemU_with_priv_1_rwt] [] []
    ``write'MemU_unpriv (w: word8, v, 1)``

val write'MemA_unpriv_2_rwt =
   EV [write'MemA_unpriv_def, write'MemA_with_priv_2_rwt] [] []
    ``write'MemA_unpriv (w: word16, v, 2)``

val write'MemU_unpriv_2_rwt =
   EV [write'MemU_unpriv_def, write'MemU_with_priv_2_rwt] [] []
    ``write'MemU_unpriv (w: word16, v, 2)``

val write'MemA_unpriv_4_rwt =
   EV [write'MemA_unpriv_def, write'MemA_with_priv_4_rwt] [] []
    ``write'MemA_unpriv (w: word32, v, 4)``

val write'MemU_unpriv_4_rwt =
   EV [write'MemU_unpriv_def, write'MemU_with_priv_4_rwt] [] []
    ``write'MemU_unpriv (w: word32, v, 4)``

val write'MemA_1_rwt =
   EV [write'MemA_def, write'MemA_with_priv_1_rwt, CurrentModeIsNotUser_def,
       BadMode] [] []
    ``write'MemA (w: word8, v, 1)``

val write'MemU_1_rwt =
   EV [write'MemU_def, write'MemU_with_priv_1_rwt, CurrentModeIsNotUser_def,
       BadMode] [] []
    ``write'MemU (w: word8, v, 1)``

val write'MemA_2_rwt =
   EV [write'MemA_def, write'MemA_with_priv_2_rwt, CurrentModeIsNotUser_def,
       BadMode] [] []
    ``write'MemA (w: word16, v, 2)``

val write'MemU_2_rwt =
   EV [write'MemU_def, write'MemU_with_priv_2_rwt, CurrentModeIsNotUser_def,
       BadMode] [] []
    ``write'MemU (w: word16, v, 2)``

val write'MemA_4_rwt =
   EV [write'MemA_def, write'MemA_with_priv_4_rwt, CurrentModeIsNotUser_def,
       BadMode] [] []
    ``write'MemA (w: word32, v, 4)``

val write'MemU_4_rwt =
   EV [write'MemU_def, write'MemU_with_priv_4_rwt, CurrentModeIsNotUser_def,
       BadMode] [] []
    ``write'MemU (w: word32, v, 4)``

;

(* ---------------------------- *)

fun TF (t: term frag list) = [[t |-> boolSyntax.T], [t |-> boolSyntax.F]]

val npc_thm =
   List.map (fn r => Q.INST [`d: word4` |-> r] arm_stepTheory.R_x_not_pc)

val Shift_C_rwt =
   EV [Shift_C_def, LSL_C_def, LSR_C_def, ASR_C_def, ROR_C_def, RRX_C_def] [] []
      ``Shift_C (value,typ,amount,carry_in)
        : arm_state -> ('a word # bool) # arm_state``
      |> hd
      |> SIMP_RULE std_ss []

val SND_Shift_C_rwt = Q.prove(
   `!s. SND (Shift_C (value,typ,amount,carry_in) s) = s`,
   Cases_on `typ` \\ lrw [Shift_C_rwt]) |> Drule.GEN_ALL

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

val () = setEvConv (Conv.DEPTH_CONV
            (bitstringLib.extract_v2w_CONV
             ORELSEC bitstringLib.v2w_eq_CONV
             ORELSEC bitstringLib.FIX_CONV
             ORELSEC wordsLib.SIZES_CONV))

val arm_imm_lem = Q.prove(
   `((if n = 0 then ((w, c1), s) else ((w #>> n, c2), s)) =
     ((w #>> n, if n = 0 then c1 else c2), s)) /\
    (2 * w2n (v2w [a; b; c; d] : word4) = w2n (v2w [a; b; c; d; F] : word5))`,
   rw [] \\ wordsLib.n2w_INTRO_TAC 5 \\ blastLib.BBLAST_TAC
   )

val ARMExpandImm_C_rwt =
   EV [ARMExpandImm_C_def, Shift_C_rwt, arm_imm_lem] [] []
      ``ARMExpandImm_C (^(bitstringSyntax.mk_vec 12 0), c)``
      |> hd
      |> REWRITE_RULE [wordsTheory.w2n_eq_0]

(*
val ThumbExpandImm_C_rwt =
   EV [ThumbExpandImm_C_def, ROR_C_def, wordsTheory.w2n_eq_0,
       bitstringTheory.word_concat_v2w_rwt, merge_cond] [] []
      ``ThumbExpandImm_C (^(mk_vec 12 0), c)``
      |> hd
*)

val () = setEvConv utilsLib.WGROUND_CONV

local
   val rwt = Q.prove(
      `(if b then (((x, y), s): (word32 # bool) # arm_state) else ((m, n), s)) =
       ((if b then x else m, if b then y else n), s)`,
      rw [])
in
   val ExpandImm_C_rwt =
      EV [ExpandImm_C_def, ARMExpandImm_C_rwt, rwt]
         [[``^st.Encoding <> Encoding_Thumb2``]] []
         ``ExpandImm_C (^(bitstringSyntax.mk_vec 12 0), c)``
         |> hd
end

(* ---------------------------- *)

fun regEV npcs thms ctxt s tm =
   let
      val npc_thms = npc_thm npcs
      val thms =
         [ArchVersion_rwts, IncPC_rwt, cond_rand_thms, R_rwt, write'R_rwt] @
         npc_thms @ thms
      val rule =
         REWRITE_RULE npc_thms o FULL_DATATYPE_RULE o
         Conv.CONV_RULE
            (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt]))
   in
      EV thms ctxt s tm
      |> List.map rule
      |> addThms
   end

fun memEV rl mem thms ctxt s tm =
   let
      val thms = [NullCheckIfThumbEE_rwt, IncPC_rwt, PC_rwt, R_rwt,
                  armTheory.offset1_case_def,
                  armTheory.offset2_case_def,
                  pairTheory.pair_case_thm,
                  Shift_C_DecodeImmShift_rwt, Shift_C_LSL_rwt, Shift_def,
                  alignmentTheory.aligned_add_sub_123] @ thms
   in
      List.map (fn r => EV ([r] @ thms) ctxt s tm |> List.map rl) mem
      |> List.concat
      |> addThms
   end

fun storeEV rl mem thms ctxt s tm =
   let
      val thms = [NullCheckIfThumbEE_rwt,
                  Q.INST [`d` |-> `n`] arm_stepTheory.R_x_not_pc,
                  IncPC_rwt, PCStoreValue_def, PC_rwt, Shift_C_LSL_rwt,
                  CurrentInstrSet_rwt, Shift_def, SND_Shift_C_rwt, FST_SWAP,
                  boolTheory.COND_ID, merge_cond, cond_rand_thms,
                  armTheory.offset1_case_def,
                  armTheory.offset2_case_def,
                  pairTheory.pair_case_thm,
                  R_rwt, write'R_rwt] @ thms
      val conv = REWRITE_CONV [boolTheory.COND_ID] THENC DATATYPE_CONV
      val rule = rl o utilsLib.ALL_HYP_CONV_RULE conv
   in
      List.map (fn w => EV ([w] @ thms) ctxt s tm |> List.map rule) mem
      |> List.concat
      |> addThms
   end

(* ---------------------------- *)

fun unfold_for_loop thm =
   thm
   |> REWRITE_RULE [utilsLib.for_thm (14,0), BitCount]
   |> Drule.SPEC_ALL
   |> Conv.CONV_RULE (Conv.X_FUN_EQ_CONV st)
   |> Drule.SPEC_ALL
   |> Conv.RIGHT_CONV_RULE
        (PairedLambda.GEN_BETA_CONV
         THENC REWRITE_CONV [NullCheckIfThumbEE_rwt]
         THENC PairedLambda.let_CONV
         THENC REWRITE_CONV []
         THENC PairedLambda.GEN_LET_CONV
         THENC PairedLambda.let_CONV
         THENC Conv.ONCE_DEPTH_CONV PairedLambda.GEN_BETA_CONV)

val abs_body = snd o Term.dest_abs

local
   fun let_body t = let val (_, _, b) = pairSyntax.dest_plet t in b end
   fun let_val t = let val (_, b, _) = pairSyntax.dest_plet t in b end
   fun cond_true t = let val (_, b, _) = boolSyntax.dest_cond t in b end
   val split_memA =
      GSYM (Q.ISPEC `MemA x s : 'a word # arm_state` pairTheory.PAIR)
   val split_R = GSYM (Q.ISPEC `R x s` pairTheory.PAIR)
in
   fun simp_for_body thm =
      thm
      |> Drule.SPEC_ALL
      |> rhsc |> abs_body
      |> let_body |> cond_true |> let_body |> let_body
      |> let_val |> Term.rand |> Term.rator
      |> state_transformerSyntax.dest_for |> (fn (_, _, b) => b)
      |> abs_body |> abs_body
      |> (SIMP_CONV bool_ss
            [Once split_memA, Once split_R, pairTheory.pair_case_thm]
          THENC Conv.DEPTH_CONV PairedLambda.GEN_LET_CONV
          THENC SIMP_CONV std_ss [cond_rand_thms])
end

fun upto_enumerate thm =
   Drule.LIST_CONJ (List.tabulate (15, fn i =>
      let
         val t = numSyntax.term_of_int i
      in
         Thm.CONJ (thm |> Thm.SPEC t |> numLib.REDUCE_RULE)
                  (numLib.REDUCE_CONV ``^t + 1``)
      end))

(* -- *)

val count_list_15 = EVAL ``COUNT_LIST 15``

local
   val LDM_UPTO_SUC = upto_enumerate arm_stepTheory.LDM_UPTO_SUC

   val LDM_lem = simp_for_body dfn'LoadMultiple_def
   val LDM_thm = unfold_for_loop dfn'LoadMultiple_def

   val cond_write'R_13_rwt = Q.prove(
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
      |> Drule.UNDISCH_ALL

   val rearrange = Q.prove(
      `!p a b n s.
         (if p then write'R (a, n) s else write'R (b, n) s) =
         write'R (if p then a else b, n) s`,
      lrw [])

   fun FOR_BETA_CONV i tm =
      let
         val b = pairSyntax.dest_snd tm
         val (b, _, _) = boolSyntax.dest_cond (abs_body (rator b))
         val n = fst (wordsSyntax.dest_word_bit b)
         val _ = numLib.int_of_term n = i orelse raise ERR "FOR_BETA_CONV" ""
         val thm = if i = 13 then cond_write'R_13_rwt else write'R_rwt
      in
         (Conv.RAND_CONV
            (PairedLambda.GEN_BETA_CONV
             THENC Conv.REWR_CONV LDM_lem
             THENC utilsLib.INST_REWRITE_CONV [hd MemA_4_rwt, thm])
          THENC REWRITE_CONV [cond_rand_thms, LDM_UPTO_components,
                              LDM_UPTO_0, LDM_UPTO_SUC]) tm
      end

   val pc_conv =
      PairedLambda.let_CONV
      THENC utilsLib.INST_REWRITE_CONV [hd MemA_4_rwt]
      THENC REWRITE_CONV
              [pairTheory.pair_case_thm, EVAL ``14 + 1n``,
               alignmentTheory.aligned_numeric,
               alignmentTheory.aligned_add_sub_123,
               arm_stepTheory.Aligned_concat4,
               LDM_UPTO_components]
      THENC Conv.RAND_CONV
              (Conv.RAND_CONV
                 (Conv.RATOR_CONV PairedLambda.GEN_BETA_CONV
                  THENC PairedLambda.GEN_BETA_CONV)
               THENC PairedLambda.let_CONV)

   val pc_tm = ``word_bit 15 (registers: word16)``

   fun LDM ispc a i =
      let
         val (tm, cnv) = if ispc then (pc_tm, pc_conv)
                         else (boolSyntax.mk_neg pc_tm, ALL_CONV)
      in
         LDM_thm
         |> Q.INST [`increment` |-> a, `index` |-> i]
         |> Conv.RIGHT_CONV_RULE
              (REWRITE_CONV [R_rwt, ASSUME tm, ASSUME ``n <> 15w: word4``]
               THENC Conv.EVERY_CONV
                       (List.tabulate
                          (15, fn i => Conv.ONCE_DEPTH_CONV (FOR_BETA_CONV i)))
               THENC cnv)
         |> utilsLib.ALL_HYP_CONV_RULE
               (utilsLib.WGROUND_CONV
                THENC REWRITE_CONV
                         [alignmentTheory.aligned_numeric,
                          alignmentTheory.aligned_add_sub_123,
                          arm_stepTheory.Aligned_concat4,
                          LDM_UPTO_components]
                THENC numLib.REDUCE_CONV)
         |> REWRITE_RULE [rearrange]
      end

   val LDM_PC = LDM true
   val LDM = LDM false

   val LDMDA_PC = LDM_PC `F` `F`
   val LDMDB_PC = LDM_PC `F` `T`
   val LDMIA_PC = LDM_PC `T` `F`
   val LDMIB_PC = LDM_PC `T` `T`

   val LDMDA = LDM `F` `F`
   val LDMDB = LDM `F` `T`
   val LDMIA = LDM `T` `F`
   val LDMIB = LDM `T` `T`

   val rule =
      REWRITE_RULE [count_list_15] o
      utilsLib.ALL_HYP_CONV_RULE
        (DATATYPE_CONV
         THENC REWRITE_CONV
                 [ASSUME ``aligned 2 (^st.REG (arm_step$R_mode ^st.CPSR.M n))``,
                  alignmentTheory.aligned_numeric,
                  alignmentTheory.aligned_add_sub_123,
                  arm_stepTheory.Aligned_concat4,
                  LDM_UPTO_components])
in
   fun ldmEV wb =
      EV [LDMDA, LDMDB, LDMIA, LDMIB, LDM_UPTO_def, IncPC_rwt, LDM_UPTO_PC,
          write'R_rwt]
         (if wb
             then [[``~word_bit (w2n (n:word4)) (registers:word16)``]]
          else [])
         [[`inc` |-> ``F``, `index` |-> ``F``],
          [`inc` |-> ``F``, `index` |-> ``T``],
          [`inc` |-> ``T``, `index` |-> ``F``],
          [`inc` |-> ``T``, `index` |-> ``T``]]
        ``dfn'LoadMultiple
            (inc, index, ^(bitstringSyntax.mk_b wb), n, registers)``
        |> List.map rule
        |> addThms

   fun ldm_pcEV wb =
      List.map (fn wpc =>
         EV [LDMDA_PC, LDMDB_PC, LDMIA_PC, LDMIB_PC, LDM_UPTO_def, wpc,
             LDM_UPTO_PC, write'R_rwt]
            (if wb
                then [[``~word_bit (w2n (n:word4)) (registers:word16)``]]
             else [])
            [[`inc` |-> ``F``, `index` |-> ``F``],
             [`inc` |-> ``F``, `index` |-> ``T``],
             [`inc` |-> ``T``, `index` |-> ``F``],
             [`inc` |-> ``T``, `index` |-> ``T``]]
           ``dfn'LoadMultiple
               (inc, index, ^(bitstringSyntax.mk_b wb), n, registers)``
           |> List.map rule)
           LoadWritePC_rwt
        |> List.concat
        |> addThms
end

val () = resetThms ()

val LoadMultiple_wb_rwt = ldmEV true
val LoadMultiple_nowb_rwt = ldmEV false

val LoadMultiple_pc_wb_rwt = ldm_pcEV true
val LoadMultiple_pc_nowb_rwt = ldm_pcEV false

(* -- *)

local
   val STM_UPTO_SUC = upto_enumerate arm_stepTheory.STM_UPTO_SUC

   val STM_lem = simp_for_body dfn'StoreMultiple_def
   val STM_thm = unfold_for_loop dfn'StoreMultiple_def

   val cond_lsb = Q.prove(
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
           CountLeadingZeroBits16]
      \\ lrfs []
      \\ lfs []
      )
      |> Drule.UNDISCH_ALL

   fun FOR_BETA_CONV i tm =
      let
         val b = pairSyntax.dest_snd tm
         val (b, _, _) = boolSyntax.dest_cond (abs_body (rator b))
         val n = fst (wordsSyntax.dest_word_bit b)
         val _ = numLib.int_of_term n = i orelse raise ERR "FOR_BETA_CONV" ""
      in
         (Conv.RAND_CONV
            (PairedLambda.GEN_BETA_CONV
             THENC Conv.REWR_CONV STM_lem
             THENC utilsLib.INST_REWRITE_CONV [cond_lsb]
             THENC utilsLib.INST_REWRITE_CONV [hd write'MemA_4_rwt, R_rwt]
             THENC utilsLib.WGROUND_CONV)
          THENC REWRITE_CONV [cond_rand_thms, STM_UPTO_components,
                              STM_UPTO_0, STM_UPTO_SUC]) tm
      end
in
   fun STM a i =
      STM_thm
      |> Q.INST [`increment` |-> a, `index` |-> i]
      |> Conv.RIGHT_CONV_RULE
           (REWRITE_CONV [R_rwt, ASSUME ``n <> 15w: word4``]
            THENC Conv.EVERY_CONV
                     (List.tabulate
                         (15, fn i => Conv.ONCE_DEPTH_CONV (FOR_BETA_CONV i))))
      |> utilsLib.ALL_HYP_CONV_RULE
            (numLib.REDUCE_CONV
             THENC REWRITE_CONV
                     [alignmentTheory.aligned_numeric,
                      alignmentTheory.aligned_add_sub_123,
                      arm_stepTheory.Aligned_concat4,
                      STM_UPTO_components]
             THENC utilsLib.INST_REWRITE_CONV [R_rwt]
             THENC DATATYPE_CONV)
      |> utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV [STM_UPTO_components])
end

local
   val STMDA = STM `F` `F`
   val STMDB = STM `F` `T`
   val STMIA = STM `T` `F`
   val STMIB = STM `T` `T`

   val add4 = wordsLib.WORD_ARITH_PROVE
      ``(a: 'a word - 4w * b + 4w + 4w * c = a + 4w * (c - b + 1w)) /\
        (a - 4w * b + 4w * c = a + 4w * (c - b)) /\
        (a + 4w * (-1w + 1w) = a) /\
        (a + 4w * -1w = a - 4w)``

   val rearrange = Q.prove(
      `(if p then
          s with <|MEM := a; REG := b|>
        else
          s with <|MEM := c; REG := d|>) =
       s with <|MEM := if p then a else c; REG := if p then b else d|>`,
      rw [])
in
   val StoreMultiple_rwt =
      EV ([STMDA, STMDB, STMIA, STMIB, STM_UPTO_def, IncPC_rwt,
           STM_UPTO_components, PCStoreValue_def, PC_def, add4, rearrange,
           R_rwt, write'R_rwt, hd write'MemA_4_rwt] @ npc_thm [`n`]) []
         [[`inc` |-> ``F``, `index` |-> ``F``],
          [`inc` |-> ``F``, `index` |-> ``T``],
          [`inc` |-> ``T``, `index` |-> ``F``],
          [`inc` |-> ``T``, `index` |-> ``T``]]
        ``dfn'StoreMultiple (inc, index, wback, n, registers)``
        |> List.map
              (SIMP_RULE std_ss [count_list_15, add4, bit_count_sub] o
               utilsLib.MATCH_HYP_CONV_RULE
                  (utilsLib.INST_REWRITE_CONV
                      [Drule.UNDISCH (DECIDE ``b ==> (a \/ b \/ c = T)``)])
                  ``a \/ b \/ c : bool`` o
               utilsLib.ALL_HYP_CONV_RULE
                  (DATATYPE_CONV
                   THENC REWRITE_CONV
                            [boolTheory.COND_ID,
                             alignmentTheory.aligned_numeric,
                             alignmentTheory.aligned_add_sub_123]) o
               utilsLib.ALL_HYP_CONV_RULE
                  (DATATYPE_CONV
                   THENC SIMP_CONV std_ss
                           [pairTheory.pair_case_thm,
                            alignmentTheory.aligned_numeric,
                            alignmentTheory.aligned_add_sub_123]
                   THENC utilsLib.INST_REWRITE_CONV [hd write'MemA_4_rwt]))
        |> addThms
end

(* ----------- *)

val word_bit_16_thms =
   let
      val v = bitstringSyntax.mk_vec 16 0
      fun wb i = wordsSyntax.mk_word_bit (numSyntax.term_of_int i, v)
   in
      List.tabulate (16, fn i => bitstringLib.word_bit_CONV (wb i))
   end

local
   val word_bit_conv = wordsLib.WORD_BIT_INDEX_CONV true
   val word_index_16_thms =
      List.map (Conv.CONV_RULE (Conv.LHS_CONV word_bit_conv)) word_bit_16_thms
   val suc_rule =
      Conv.CONV_RULE
         (Conv.LHS_CONV (Conv.RATOR_CONV (Conv.RAND_CONV reduceLib.SUC_CONV)))
   fun bit_count_thms v =
      let
         fun upto_thm i =
            wordsSyntax.mk_bit_count_upto (numSyntax.term_of_int i, v)
         fun thm i t =
            let
               val thm = wordsTheory.bit_count_upto_SUC
                         |> Drule.ISPECL [v, numSyntax.term_of_int (i - 1)]
                         |> suc_rule
            in
               i |> upto_thm
                 |> (Conv.REWR_CONV thm
                     THENC Conv.LAND_CONV (REWRITE_CONV word_index_16_thms)
                     THENC Conv.RAND_CONV (Conv.REWR_CONV t)
                     THENC numLib.REDUCE_CONV)
            end
         fun loop a i = if 16 < i then a else loop (thm i (hd a) :: a) (i + 1)
      in
         loop [Drule.ISPEC v wordsTheory.bit_count_upto_0] 1
      end
   val thms = ref word_bit_16_thms
   val c = ref (PURE_REWRITE_CONV (!thms))
in
   fun BIT_THMS_CONV tm = (!c) tm
      handle Conv.UNCHANGED =>
        let
           val v =
              HolKernel.find_term
                (fn t =>
                   case Lib.total bitstringSyntax.dest_v2w t of
                      SOME (_, ty) => fcpSyntax.dest_int_numeric_type ty = 16
                    | NONE => false) tm
           val () = thms := !thms @ (bit_count_thms v)
           val () = c := PURE_REWRITE_CONV (!thms)
        in
           (!c) tm
        end
end

local
   val eq0_rwts = Q.prove(
      `(NUMERAL (BIT1 x) <> 0) /\ (NUMERAL (BIT2 x) <> 0)`,
      REWRITE_TAC [arithmeticTheory.NUMERAL_DEF, arithmeticTheory.BIT1,
                   arithmeticTheory.BIT2]
      \\ DECIDE_TAC)
   val count15 = rhsc count_list_15
   val STM1 = REWRITE_RULE [wordsTheory.word_mul_n2w] STM1_def
   val LDM1_tm = Term.prim_mk_const {Thy = "arm_step", Name = "LDM1"}
   val STM1_tm = Term.prim_mk_const {Thy = "arm_step", Name = "STM1"}
   val f_tm = Term.mk_var ("f", ``:word4 -> RName``)
   val b_tm = Term.mk_var ("b", wordsSyntax.mk_int_word_type 32)
   val r_tm = Term.mk_var ("r", ``:RName -> word32``)
   val m_tm = Term.mk_var ("r", ``:word32 -> word8``)
   val ok = Term.term_eq count15
   val FOLDL1_CONV = Conv.REWR_CONV (Thm.CONJUNCT1 listTheory.FOLDL)
   val FOLDL2_CONV = Conv.REWR_CONV (Thm.CONJUNCT2 listTheory.FOLDL)
   val CONV0 = REWRITE_CONV [Thm.CONJUNCT1 wordsTheory.WORD_ADD_0, eq0_rwts]
   val ONCE_FOLDL_LDM1_CONV =
     (FOLDL2_CONV
      THENC Conv.RATOR_CONV (Conv.RAND_CONV
              (Conv.REWR_CONV LDM1_def
               THENC Conv.RATOR_CONV (Conv.RATOR_CONV BIT_THMS_CONV)
               THENC CONV0
               THENC (Conv.REWR_CONV combinTheory.I_THM
                      ORELSEC Conv.RATOR_CONV (Conv.RAND_CONV
                                (Conv.RAND_CONV
                                    (Conv.TRY_CONV BIT_THMS_CONV
                                     THENC wordsLib.WORD_EVAL_CONV)
                                 THENC PairedLambda.let_CONV))))))
   val ONCE_FOLDL_STM1_CONV =
     (FOLDL2_CONV
      THENC Conv.RATOR_CONV (Conv.RAND_CONV
              (Conv.REWR_CONV STM1
               THENC Conv.RATOR_CONV (Conv.RATOR_CONV BIT_THMS_CONV)
               THENC CONV0
               THENC (Conv.REWR_CONV combinTheory.I_THM
                      ORELSEC (Conv.RATOR_CONV
                                  (Conv.RATOR_CONV
                                     (Conv.TRY_CONV BIT_THMS_CONV
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
           val _ = Term.term_eq LDM1_tm ldm andalso ok l
                   orelse raise ERR "FOLDL_LDM1_CONV" ""
           val df = Term.list_mk_comb (LDM1_tm, [f_tm, b_tm, v, st])
           val thm = lconv (listSyntax.mk_foldl (df, r_tm, count15))
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
           val _ = Term.term_eq STM1_tm stm andalso ok l
                   orelse raise ERR "FOLDL_STM1_CONV" ""
           val df = Term.list_mk_comb (STM1_tm, [f_tm, b_tm, v, st])
           val thm = sconv (listSyntax.mk_foldl (df, m_tm, count15))
                     |> Drule.GEN_ALL
           val () = lthms := thm :: (!lthms)
           val () = sc := PURE_REWRITE_CONV (!lthms)
        in
           Drule.SPECL [s, m, f, b] thm
        end
end

local
   val be_tm = ``^st.CPSR.E``
   val le_tm = boolSyntax.mk_neg be_tm
   fun endian_rule thm =
      REWRITE_RULE
         [ASSUME (if Lib.exists (Lib.equal le_tm) (Thm.hyp thm)
                     then le_tm
                  else be_tm)] thm
   fun NO_FREE_VARS_CONV tm =
      if List.null (Term.free_vars tm)
         then Conv.ALL_CONV tm
      else Conv.NO_CONV tm
   val LowestSetBit_CONV =
      Conv.REWR_CONV armTheory.LowestSetBit_def
      THENC NO_FREE_VARS_CONV
      THENC Conv.RAND_CONV bossLib.EVAL
      THENC Conv.REWR_CONV arm_stepTheory.CountLeadingZeroBits16
      THENC bossLib.EVAL
   fun BIT_COUNT_UPTO_CONV tm =
      case boolSyntax.dest_strip_comb tm of
         ("words$bit_count_upto", [_, _]) => NO_FREE_VARS_CONV tm
       | ("words$bit_count", [v]) =>
            (NO_FREE_VARS_CONV
             THENC Conv.REWR_CONV wordsTheory.bit_count_def
             THENC Conv.RATOR_CONV (Conv.RAND_CONV wordsLib.SIZES_CONV)) tm
       | _ => Conv.NO_CONV tm
   val BIT_COUNT_CONV = BIT_COUNT_UPTO_CONV THENC BIT_THMS_CONV
   val bit_count_rule = utilsLib.FULL_CONV_RULE (Conv.DEPTH_CONV BIT_COUNT_CONV)
   val rule = bit_count_rule o endian_rule
   fun ground_mul_conv tm =
      case Lib.total wordsSyntax.dest_word_mul tm of
         SOME (a, b) =>
            if wordsSyntax.is_word_literal a andalso
               wordsSyntax.is_word_literal b
               then wordsLib.WORD_EVAL_CONV tm
            else raise ERR "ground_mul_conv" ""
       | NONE => raise ERR "ground_mul_conv" ""
   val ground_mul_rule =
      utilsLib.FULL_CONV_RULE (Conv.DEPTH_CONV ground_mul_conv)
   val stm_rule1 =
      utilsLib.MATCH_HYP_CONV_RULE
         (Conv.RAND_CONV
            (Conv.LHS_CONV (Conv.RAND_CONV (Conv.TRY_CONV LowestSetBit_CONV))))
         ``x ==> (n2w (LowestSetBit (l: word16)) = v2w q : word4)``
   val mk_neq = boolSyntax.mk_neg o boolSyntax.mk_eq
   fun mk_stm_wb_thm t =
      let
         val l = t |> boolSyntax.lhand
                   |> boolSyntax.rand
                   |> bitstringSyntax.dest_v2w |> fst
                   |> bitstringSyntax.bitlist_of_term
                   |> List.foldl
                         (fn (b, (i, a)) => (i - 1, if b then i :: a else a))
                         (15, [])
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
         Tactical.prove(eq_thm, NTAC 4 Cases THEN EVAL_TAC)
      end
   fun stm_rule2 thm =
      case List.find boolSyntax.is_imp_only (Thm.hyp thm) of
         SOME t =>
            utilsLib.MATCH_HYP_CONV_RULE
              (PURE_REWRITE_CONV [mk_stm_wb_thm t]) ``x ==> (a: word4 = b)`` thm
       | NONE => thm
in
   fun ldm_stm_rule s =
      let
         val s' = utilsLib.uppercase s
      in
         if String.isPrefix "LDM" s'
            then ground_mul_rule o rule o
                 Conv.CONV_RULE (Conv.DEPTH_CONV FOLDL_LDM1_CONV)
         else if String.isPrefix "STM" s'
            then ground_mul_rule o stm_rule2 o stm_rule1 o rule o
                 Conv.CONV_RULE (Conv.DEPTH_CONV FOLDL_STM1_CONV)
         else Lib.I
      end
end

(*

val v = rhsc (bitstringLib.n2w_v2w_CONV ``0xFFFFw: word16``)

val tm = ``(FOLDL (LDM1 R_usr (s.REG (R_usr n) + 4w) ^v s) s.REG
              [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14])``

val tm =
  ``FOLDL (STM1 R_usr (s.REG (R_usr n) + 4w) ^v s) s.MEM
      [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]``

Count.apply FOLDL_LDM1_CONV tm
Count.apply FOLDL_STM1_CONV tm

*)

(* ========================================================================= *)

(* Fetch *)

local
   val lem = Q.prove (
      `(!p. ((if p then v2w [b1; b2; b3] else v2w [b4; b5; b6]) = 7w : word3) =
             (if p then b1 /\ b2 /\ b3 else b4 /\ b5 /\ b6)) /\
       (!p. ((if p then v2w [b1; b2] else v2w [b3; b4]) = 0w : word2) =
             (if p then ~b1 /\ ~b2 else ~b3 /\ ~b4))`,
      rw_tac std_ss []
      \\ CONV_TAC (Conv.LHS_CONV bitstringLib.v2w_eq_CONV)
      \\ decide_tac)

   val CONC_RULE =
     SIMP_RULE (srw_ss()++boolSimps.LET_ss)
        [bitstringTheory.fixwidth_def, bitstringTheory.field_def,
         bitstringTheory.shiftr_def, bitstringTheory.w2w_v2w, lem] o
     ONCE_REWRITE_RULE [bitstringTheory.word_concat_v2w_rwt]

   val Fetch_v4_rwt =
      List.map (fn m =>
         EV [Fetch_def, CurrentInstrSet_rwt, m]
            [[``^st.Architecture = ARMv4``,
              ``^st.MEM (^st.REG RName_PC) = ^(mk_byte 0)``,
              ``^st.MEM (^st.REG RName_PC + 1w) = ^(mk_byte 8)``,
              ``^st.MEM (^st.REG RName_PC + 2w) = ^(mk_byte 16)``,
              ``^st.MEM (^st.REG RName_PC + 3w) = ^(mk_byte 24)``]] []
            ``Fetch``) MemA_4_rwt
         |> List.concat
         |> List.map
              (CONC_RULE o CONC_RULE o CONC_RULE o
               utilsLib.ALL_HYP_CONV_RULE DATATYPE_CONV)

   val Fetch_arm_rwt =
      List.map (fn m =>
         EV [Fetch_def, CurrentInstrSet_rwt, m]
            [[``~^st.CPSR.T``,
              ``^st.MEM (^st.REG RName_PC) = ^(mk_byte 0)``,
              ``^st.MEM (^st.REG RName_PC + 1w) = ^(mk_byte 8)``,
              ``^st.MEM (^st.REG RName_PC + 2w) = ^(mk_byte 16)``,
              ``^st.MEM (^st.REG RName_PC + 3w) = ^(mk_byte 24)``]] []
            ``Fetch``) MemA_4_rwt
         |> List.concat
         |> List.map
              (CONC_RULE o CONC_RULE o CONC_RULE o
               utilsLib.ALL_HYP_CONV_RULE DATATYPE_CONV)

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
         bitstringTheory.word_extract_v2w, bitstringTheory.word_bits_v2w] o
      utilsLib.ALL_HYP_CONV_RULE DATATYPE_CONV

   val ALIGNED_PLUS_RULE =
      utilsLib.MATCH_HYP_CONV_RULE
        (REWRITE_CONV [alignmentTheory.aligned_numeric,
                       alignmentTheory.aligned_add_sub_123])
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
      EV [Fetch_def, CurrentInstrSet_rwt]
         [[``^st.CPSR.T``, ``^st.Architecture <> ARMv4``,
           not_thumb2_test_tm],
          [``^st.CPSR.T``, ``^st.Architecture <> ARMv4``,
           thumb2_test_tm]] []
         ``Fetch``

   fun fetch_thumb m =
      [fetch_thumb_rwts
        |> hd
        |> Thm.DISCH not_thumb2_test_tm
        |> Drule.ADD_ASSUM (List.nth (byte_tms, 0))
        |> Drule.ADD_ASSUM (List.nth (byte_tms, 1))
        |> Conv.CONV_RULE (utilsLib.INST_REWRITE_CONV [m])
        |> rule,
       fetch_thumb_rwts
        |> tl |> hd
        |> Thm.DISCH thumb2_test_tm
        |> Drule.ADD_ASSUM (List.nth (byte_tms, 0))
        |> Drule.ADD_ASSUM (List.nth (byte_tms, 1))
        |> Drule.ADD_ASSUM (List.nth (byte_tms, 2))
        |> Drule.ADD_ASSUM (List.nth (byte_tms, 3))
        |> Conv.CONV_RULE (utilsLib.INST_REWRITE_CONV [m] THENC DATATYPE_CONV)
        |> ALIGNED_PLUS_RULE
        |> rule]

   val Fetch_thumb_rwt = List.map fetch_thumb MemA_2_rwt |> List.concat

   val fetch_thms = Fetch_v4_rwt @ Fetch_arm_rwt @ Fetch_thumb_rwt

   val thumb_tm = fix_datatype ``^st.CPSR.T``
   val arm_tm = boolSyntax.mk_neg thumb_tm
   val big_tm = fix_datatype ``^st.CPSR.E``
   val little_tm = boolSyntax.mk_neg big_tm

   val v4 = fix_datatype ``^st.Architecture = ARMv4``
   val not_v4 = boolSyntax.mk_neg v4
   fun is_v4 thm = List.exists (Lib.can (Term.match_term v4)) (Thm.hyp thm)
   fun is_not_v4 thm =
      List.exists (Lib.can (Term.match_term not_v4)) (Thm.hyp thm)

   fun fix_not_v4 thm =
      if is_not_v4 thm
         then ASM_REWRITE_RULE (datatype_thms []) (Thm.DISCH not_v4 thm)
      else thm

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

   fun assign_arm e = fn v =>
      let
         val (l, ty) = listSyntax.dest_list v
         val () = ignore (ty = Type.bool andalso List.length l <= 32 orelse
                          raise ERR "fetch" "bad opcode")
         val (b1, b2, b3, b4) = bytes4 (utilsLib.padLeft boolSyntax.F 32 l)
      in
         if e then build_byte 24 b4 @ build_byte 16 b3 @
                   build_byte 8 b2 @ build_byte 0 b1
         else build_byte 24 b1 @ build_byte 16 b2 @
              build_byte 8 b3 @ build_byte 0 b4
      end

   fun ftch_thms tms =
      utilsLib.specialized "fetch"
         (utilsLib.WGROUND_CONV THENC DATATYPE_CONV, fix_datatypes tms)
         fetch_thms

   fun fetch_thm tms =
      case ftch_thms tms of
         [thm] => sumSyntax.INL (fix_not_v4 thm)
       | [thm1, thm2] =>
             if is_v4 thm1
                then sumSyntax.INL thm1
             else sumSyntax.INR (fix_not_v4 thm1, fix_not_v4 thm2)
       | _ => raise ERR "fetch_thm" "expecting 1 or 2 theorems"

   val rule =
      utilsLib.MATCH_HYP_CONV_RULE (REWRITE_CONV []) ``a /\ b : bool`` o
      utilsLib.MATCH_HYP_CONV_RULE (REWRITE_CONV []) ``a \/ b : bool``

   fun check (l, s) thm =
      if utilsLib.vacuous thm
         then raise ERR "fetch" (utilsLib.long_term_to_string l ^ " " ^ s)
      else thm
in
   fun fetch tms =
      let
         val tms = List.map fix_datatype tms
         val e = List.exists (equal big_tm) tms
         val thms = fetch_thm tms
      in
         fn v =>
            case thms of
              sumSyntax.INL thm => Thm.INST (assign_arm e v) thm
            | sumSyntax.INR (thm1, thm2) =>
                let
                   val (l, ty) = listSyntax.dest_list v
                in
                   if ty = Type.bool
                      then if List.length l <= 16
                              then check (v, "is a Thumb-2 prefix")
                                      (rule (Thm.INST (assign_thumb e l) thm1))
                           else if List.length l = 32
                              then check (v, "is not a Thumb-2 instruction")
                                      (rule (Thm.INST (assign_thumb2 e l) thm2))
                           else raise ERR "fetch" "length must be 16 or 32"
                   else raise ERR "fetch" "not a bool list"
                end
      end
end

fun fetch_hex tms =
   let
      val ftch = fetch tms
   in
      ftch o bitstringSyntax.bitstring_of_hexstring
   end

(*

val ftch = fetch_hex (arm_configLib.mk_config_terms "v4,16,le")
val ftch = fetch_hex (arm_configLib.mk_config_terms "16,le")
val ftch = fetch_hex (arm_configLib.mk_config_terms "")

Count.apply ftch "8F1FF3BF"
Count.apply ftch "8F1F"
Count.apply ftch "F3BF8F1F"

*)

(* ========================================================================= *)

(* Decode *)

val DECODE_UNPREDICTABLE_rwt =
   EV [DECODE_UNPREDICTABLE_def, MachineCode_case_def]
      [] (mapl (`mc`, [``Thumb opc``, ``ARM opc``, ``Thumb2 (opc1, opc2)``]))
      ``DECODE_UNPREDICTABLE (mc, e)``
      |> List.map Drule.GEN_ALL

val Do_rwt = EV [Do_def] [] [] ``Do (c, def)`` |> hd

val ConditionPassed_rwt =
   EV [ConditionPassed_def, CurrentCond_def] [] []
      ``ConditionPassed ()`` |> hd

local
   fun ConditionPassed cond =
      ConditionPassed_rwt
      |> Thm.INST
           [st |-> fix_datatype ``^st with CurrentCondition := ^cond``]
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

val UndefinedARM_rwt =
   EV (UndefinedARM_def :: iConditionPassed_rwts) []
      (mapl (`c`, fst (Lib.front_last opcodes)))
      ``UndefinedARM c``

val Skip_rwt = EV [Skip_def] [] [] ``Skip ()`` |> hd |> GEN_ALL

val HaveDSPSupport_rwt =
   EV [HaveDSPSupport_def, utilsLib.SET_CONV ``a IN {ARMv4; ARMv4T; ARMv5T}``]
      [] []
      ``HaveDSPSupport ()`` |> hd

val DecodeImmShift_rwt =
   pairTheory.PAIR
   |> Q.ISPEC `DecodeImmShift x`
   |> Thm.SYM
   |> Drule.GEN_ALL

val DecodeHint_rwt =
   EV [DecodeHint_def, boolify8_v2w, Skip_rwt, ArchVersion_rwts, Do_rwt] [] []
     ``DecodeHint (c, ^(bitstringSyntax.mk_vec 8 0))``
     |> hd

local
   fun hasValueIn s =
      fn tm => let val i = wordsSyntax.uint_of_word tm in Lib.mem i s end

   fun selective_v2w_eq_CONV tm =
      let
         val r = boolSyntax.rhs tm
      in
         if wordsSyntax.size_of r = Arbnum.fromInt 4
            andalso (bitstringSyntax.is_v2w r orelse hasValueIn [13, 15] r)
            then raise ERR "selective_v2w_eq_CONV" ""
         else bitstringLib.v2w_eq_CONV tm
      end

   val DecodeARM =
      DecodeARM_def
      |> Thm.SPEC (bitstringSyntax.mk_vec 32 0)
      |> Lib.C Thm.AP_THM st
      |> Conv.RIGHT_CONV_RULE
             (Thm.BETA_CONV
              THENC Conv.DEPTH_CONV bitstringLib.extract_v2w_CONV
              THENC REWRITE_CONV
                     ([Do_rwt, ArchVersion_rwts, Skip_rwt,
                       ARMExpandImm_def, ARMExpandImm_C_rwt,
                       (* DecodeImmShift_rwt, *)
                       HaveDSPSupport_rwt,
                       HaveThumb2_def, DecodeHint_rwt,
                       armTheory.boolify28_v2w, Decode_simps,
                       Q.ISPEC `x: Extensions set` pred_setTheory.SPECIFICATION,
                       utilsLib.SET_CONV ``a IN {ARMv6T2; ARMv7_A; ARMv7_R}``,
                       utilsLib.SET_CONV ``a IN {ARMv6K; ARMv7_A; ARMv7_R}``,
                       utilsLib.SET_CONV ``(n:word4) IN {13w; 15w}``] @
                      iConditionPassed_rwts)
              THENC ONCE_REWRITE_CONV [DecodeImmShift_rwt]
              THENC Conv.DEPTH_CONV PairedLambda.let_CONV
              THENC Conv.DEPTH_CONV bitstringLib.word_bit_CONV
              THENC Conv.DEPTH_CONV bitstringLib.extract_v2w_CONV
              THENC Conv.DEPTH_CONV selective_v2w_eq_CONV
              THENC EVAL_DATATYPE_CONV
              THENC REWRITE_CONV
                      ([armTheory.boolify4_v2w, (*DecodeImmShift_rwt, *)
                        Decode_simps, BitCount, bit_count_lt_1] @
                        DECODE_UNPREDICTABLE_rwt)
              THENC Conv.DEPTH_CONV PairedLambda.PAIRED_BETA_CONV)

   fun inst_cond f =
      Thm.INST
         (List.tabulate (4, fn i => bitstringSyntax.mk_bit (i + 28) |-> f i))

   val cond_case =
      utilsLib.qm []
         ``!z b x y. (z = if b then x:'a else y) ==> (~b ==> (z = y))``
in
   val DecodeVFP =
      DecodeVFP_def
      |> Thm.SPEC (bitstringSyntax.mk_vec 32 0)
      |> Lib.C Thm.AP_THM st
      |> Conv.RIGHT_CONV_RULE
             (Thm.BETA_CONV
              THENC Conv.DEPTH_CONV bitstringLib.extract_v2w_CONV
              THENC REWRITE_CONV
                      [armTheory.boolify28_v2w, boolTheory.literal_case_THM]
              THENC Conv.ONCE_DEPTH_CONV Thm.BETA_CONV
              THENC Conv.DEPTH_CONV PairedLambda.GEN_LET_CONV
              THENC REWRITE_CONV [cond_rand_thms]
              THENC Conv.DEPTH_CONV bitstringLib.word_bit_CONV
              THENC Conv.DEPTH_CONV bitstringLib.extract_v2w_CONV
              THENC Conv.DEPTH_CONV selective_v2w_eq_CONV
              THENC REWRITE_CONV
                      [armTheory.boolify4_v2w, Decode_simps, VFPExpandImm,
                       utilsLib.SET_CONV ``a IN {VFPv3; VFPv4}``])

   val DecodeARM_15 = DecodeARM |> inst_cond (K boolSyntax.T) |> REG_RULE

   val DecodeARM_14 =
      DecodeARM
      |> inst_cond (fn i => bitstringSyntax.mk_b (0 < i))
      |> REWRITE_RULE ([v2w_13_15_rwts, v2w_ground4] @ iConditionPassed_rwts)

   val DecodeARM_other = Drule.UNDISCH (Drule.MATCH_MP cond_case DecodeARM)

   val DecodeARM_fall =
      DATATYPE_RULE (Thm.INST [state_with_enc ``Encoding_ARM``] DecodeARM)
end

local
   val rand_uncurry = utilsLib.mk_cond_rand_thms [``UNCURRY f : 'a # 'b -> 'c``]
   val ConditionPassed_enc = Q.prove(
      `!s c.
         ConditionPassed ()
           (s with <|CurrentCondition := c; Encoding := Encoding_ARM |>) =
         ConditionPassed () (s with CurrentCondition := c)`,
      lrw [ConditionPassed_rwt]) |> DATATYPE_RULE
   val v = fst (bitstringSyntax.dest_v2w (bitstringSyntax.mk_vec 28 0))
   val dual_rwt =
      blastLib.BBLAST_PROVE
        ``v2w [b2; b1; b0; F] + 1w = v2w [b2; b1; b0; T] : word4``
in
   fun DecodeARM_rwt thm pat =
      let
         val s = state_with_enc ``Encoding_ARM`` :: fst (Term.match_term v pat)
      in
         thm |> Thm.INST s
             |> REWRITE_RULE [dual_rwt, DecodeVFP]
             |> Conv.RIGHT_CONV_RULE EVAL_DATATYPE_CONV
             |> SIMP_RULE bool_ss
                  [pairTheory.UNCURRY_DEF, rand_uncurry, ConditionPassed_enc]
      end
end

(* -- *)

fun epattern s = utilsLib.pattern (s ^ "____")

val arm_patterns = List.map (I ## epattern)
  [("BranchExchange",                       "FFFTFFTF____________FFFT"),
   ("CountLeadingZeroes",                   "FFFTFTTF____________FFFT"),
   ("BranchLinkExchangeRegister",           "FFFTFFTF____________FFTT"),
   ("SaturatingAddSubtract",                "FFFTF__F____________FTFT"),
   ("Signed16Multiply32Accumulate",         "FFFTFFFF____________T__F"),
   ("Signed16x32Multiply32Accumulate",      "FFFTFFTF____________T_FF"),
   ("Signed16x32Multiply32Result",          "FFFTFFTF____________T_TF"),
   ("Signed16Multiply64Accumulate",         "FFFTFTFF____________T__F"),
   ("Signed16Multiply32Result",             "FFFTFTTF____________T__F"),
   ("ExtendByte",                           "FTTFT_TF____________FTTT"),
   ("ExtendByte16",                         "FTTFT_FF__________FFFTTT"),
   ("ExtendHalfword",                       "FTTFT_TT__________FFFTTT"),
   ("SelectBytes",                          "FTTFTFFF________TTTTTFTT"),
   ("ByteReverse",                          "FTTFTFTTTTTT____TTTTFFTT"),
   ("ByteReversePackedHalfword",            "FTTFTFTTTTTT____TTTTTFTT"),
   ("ByteReverseSignedHalfword",            "FTTFTTTTTTTT____TTTTTFTT"),
   ("ReverseBits",                          "FTTFTTTTTTTT____TTTTFFTT"),
   ("BitFieldExtract",                      "FTTTT_T______________TFT"),
   ("BitFieldClearOrInsert",                "FTTTTTF______________FFT"),
   ("Register",                             "FFFF___________________F"),
   ("Register ORR/BIC",                     "FFFTT_F________________F"),
   ("ShiftImmediate",                       "FFFTT_T________________F"),
   ("TestCompareRegister",                  "FFFTF__T_______________F"),
   ("RegisterShiftedRegister",              "FFFF________________F__T"),
   ("RegisterShiftedRegister ORR/BIC",      "FFFTT_F_____________F__T"),
   ("ShiftRegister",                        "FFFTT_T_____________F__T"),
   ("TestCompareRegisterShiftedRegister",   "FFFTF__T____________F__T"),
   ("Multiply32",                           "FFFFFFF_____________TFFT"),
   ("MultiplyAccumulate",                   "FFFFFFT_____________TFFT"),
   ("MultiplyLong",                         "FFFFT_______________TFFT"),
   ("Swap",                                 "FFFTF_FF____________TFFT"),
   ("ArithLogicImmediate",                  "FFTF____________________"),
   ("ArithLogicImmediate ORR/BIC",          "FFTTT_F_________________"),
   ("Move",                                 "FFTTT_T_________________"),
   ("TestCompareImmediate",                 "FFTTF__T________________"),
   ("MoveHalfword",                         "FFTTF_FF________________"),
   ("BranchTarget",                         "TFTF____________________"),
   ("BranchLinkExchangeImmediate (to ARM)", "TFTT____________________"),
   ("LoadUnprivileged (imm)",               "FTFF_FTT________________"),
   ("LoadWord (imm,post)",                  "FTFF_FFT________________"),
   ("LoadWord (imm,pre;lit)",               "FTFT_F_T________________"),
   ("LoadByteUnprivileged (imm)",           "FTFF_TTT________________"),
   ("LoadByte (imm,post)",                  "FTFF_TFT________________"),
   ("LoadByte (imm,pre;lit)",               "FTFT_T_T________________"),
   ("LoadUnprivileged (reg)",               "FTTF_FTT_______________F"),
   ("LoadWord (reg,post)",                  "FTTF_FFT_______________F"),
   ("LoadWord (reg,pre)",                   "FTTT_F_T_______________F"),
   ("LoadByteUnprivileged (reg)",           "FTTF_TTT_______________F"),
   ("LoadByte (reg,post)",                  "FTTF_TFT_______________F"),
   ("LoadByte (reg,pre)",                   "FTTT_T_T_______________F"),
   ("LoadHalfUnprivileged (reg)",           "FFFF_FTT____________T_TT"),
   ("LoadSignedByteUnprivileged (reg)",     "FFFF_FTT____________TTFT"),
   ("LoadHalf (reg,post)",                  "FFFF_FFT____________T_TT"),
   ("LoadSignedByte (reg,post)",            "FFFF_FFT____________TTFT"),
   ("LoadHalf (reg,pre)",                   "FFFT_F_T____________T_TT"),
   ("LoadSignedByte (reg,pre)",             "FFFT_F_T____________TTFT"),
   ("LoadHalfUnprivileged (imm)",           "FFFF_TTT____________T_TT"),
   ("LoadSignedByteUnprivileged (imm)",     "FFFF_TTT____________TTFT"),
   ("LoadHalf (imm,post;lit)",              "FFFF_TFT____________T_TT"),
   ("LoadSignedByte (imm,post;lit)",        "FFFF_TFT____________TTFT"),
   ("LoadHalf (imm,pre)",                   "FFFT_T_T____________T_TT"),
   ("LoadSignedByte (imm,pre)",             "FFFT_T_T____________TTFT"),
   ("LoadDual (reg)",                       "FFF__F_F_______F____TTFT"),
   ("LoadDual (imm;lit)",                   "FFF__T_F_______F____TTFT"),
   ("LoadMultiple",                         "TFF__F_T________________"),
   ("StoreUnprivileged (imm)",              "FTFF_FTF________________"),
   ("StoreWord (imm,post)",                 "FTFF_FFF________________"),
   ("StoreWord (imm,pre)",                  "FTFT_F_F________________"),
   ("StoreByteUnprivileged (imm)",          "FTFF_TTF________________"),
   ("StoreByte (imm,post)",                 "FTFF_TFF________________"),
   ("StoreByte (imm,pre)",                  "FTFT_T_F________________"),
   ("StoreUnprivileged (reg)",              "FTTF_FTF_______________F"),
   ("StoreWord (reg,post)",                 "FTTF_FFF_______________F"),
   ("StoreWord (reg,pre)",                  "FTTT_F_F_______________F"),
   ("StoreByteUnprivileged (reg)",          "FTTF_TTF_______________F"),
   ("StoreByte (reg,post)",                 "FTTF_TFF_______________F"),
   ("StoreByte (reg,pre)",                  "FTTT_T_F_______________F"),
   ("StoreHalfUnprivileged (reg)",          "FFFF_FTF____________TFTT"),
   ("StoreHalf (reg,post)",                 "FFFF_FFF____________TFTT"),
   ("StoreHalf (reg,pre)",                  "FFFT_F_F____________TFTT"),
   ("StoreHalfUnprivileged (imm)",          "FFFF_TTF____________TFTT"),
   ("StoreSignedByteUnprivileged (imm)",    "FFFF_TTF____________TTFT"),
   ("StoreHalf (imm,post)",                 "FFFF_TFF____________TFTT"),
   ("StoreHalf (imm,pre)",                  "FFFT_T_F____________TFTT"),
   ("StoreDual (reg)",                      "FFF__F_F_______F____TTTT"),
   ("StoreDual (imm)",                      "FFF__T_F_______F____TTTT"),
   ("StoreMultiple",                        "TFF__F_F________________"),
   ("VFPLoadStore",                         "TTFT__F_________TFT_____"),
   ("VFPData",                              "TTTF____________TFT____F"),
   ("VFPTransfer",                          "TTTF____________TFTF___T"),
   ("VFPTransfer2",                         "TTFFFTF_________TFT_FF_T"),
   ("MoveToRegisterFromSpecial",            "FFFTFFFF__________F_FFFF"),
   ("MoveToSpecialFromRegister",            "FFFTFFTF__________F_FFFF"),
   ("MoveToSpecialFromImmediate",           "FFTTFFTF________________"),
   ("Hint",                                 "FFTTFFTFFFFFTTTTFFFF____")
  ]

val arm_patterns15 = List.map (I ## epattern)
  [("Setend",                                 "FFFTFFFF___T________FFFF"),
   ("ChangeProcessorState",                   "FFFTFFFF___F__________F_"),
   ("DataMemoryBarrier",                      "FTFTFTTTTTTTTTTTFFFFFTFT"),
   ("ReturnFromException",                    "TFF__F_T________________"),
   ("BranchLinkExchangeImmediate (to Thumb)", "TFT_____________________")
  ]

(* -- *)

datatype condition = Cond15 | Cond14 | Cond of (term, term) subst

local
   val mk_bit = bitstringSyntax.mk_bit
   fun mk_condition l =
      let
         val cond = Lib.with_exn (List.map bitstringSyntax.dest_b) l
                      (ERR "mk_condition" "condition code not specified")
      in
         case cond of
            [b31, b30, b29, b28] =>
               if b31 andalso b30 andalso b29
                  then if b28 then Cond15 else Cond14
               else Cond [mk_bit 31 |-> List.nth (l, 0),
                          mk_bit 30 |-> List.nth (l, 1),
                          mk_bit 29 |-> List.nth (l, 2),
                          mk_bit 28 |-> List.nth (l, 3)]
          | _ => raise ERR "mk_condition" "expecting 4 element list"
      end
   val w32 = fcpSyntax.mk_int_numeric_type 32
   fun pad32_opcode v =
      let
         val (l, ty) = listSyntax.dest_list v
         val () = ignore (ty = Type.bool andalso List.length l <= 32
                          orelse raise ERR "mk_opcode" "bad Bool list")
      in
         utilsLib.padLeft boolSyntax.F 32 l
      end
in
   val hex_to_bits_32 = pad32_opcode o bitstringSyntax.bitstring_of_hexstring
   fun mk_opcode v =
      let
         val opc = pad32_opcode v
      in
         (mk_condition (List.take (opc, 4)),
          bitstringSyntax.mk_v2w (listSyntax.mk_list (opc, Type.bool), w32))
      end
   fun mk_pattern_opcode c p =
      listSyntax.mk_list
         (fst (listSyntax.dest_list (utilsLib.pattern c)) @
          fst (listSyntax.dest_list p), Type.bool)
end

local
   val arm_pats = Redblackmap.fromList String.compare arm_patterns
   val arm_pats15 = Redblackmap.fromList String.compare arm_patterns15
   val alias =
      fn "LoadByte (imm,pre)" => ("LoadByte (imm,pre;lit)", [true, false])
       | "LoadSignedByte (imm,post)" =>
            ("LoadSignedByte (imm,post;lit)", [true, false])
       | "LoadHalf (imm,post)" => ("LoadHalf (imm,post;lit)", [true, false])
       | "LoadWord (imm,pre)" => ("LoadWord (imm,pre;lit)", [true, false])
       | "LoadDual (imm)" => ("LoadDual (imm;lit)", [true, false])
       | "LoadByte (lit)" => ("LoadByte (imm,pre;lit)", [false, true])
       | "LoadSignedByte (lit)" =>
            ("LoadSignedByte (imm,post;lit)", [false, true])
       | "LoadHalf (lit)" => ("LoadHalf (imm,post;lit)", [false, true])
       | "LoadWord (lit)" => ("LoadWord (imm,pre;lit)", [false, true])
       | "LoadDual (lit)" => ("LoadDual (imm;lit)", [false, true])
       | s as "LoadByte (imm,post)" => (s, [true, false])
       | s as "LoadSignedByte (imm,pre)" => (s, [true, false])
       | s as "LoadHalf (imm,pre)" => (s, [true, false])
       | s as "LoadWord (imm,post)" => (s, [true, false])
       | s as "SpecialFromImmediate" =>
            ("MoveTo" ^ s, [true, false, false, false, false, false, false])
       | s => (s, [true])
   val c14 = utilsLib.pattern "TTTF"
   val c15 = utilsLib.pattern "TTTT"
   fun unconditional c =
      let
         val cond = Term.term_eq (utilsLib.pattern c)
      in
         cond c14 orelse cond c15
      end
   fun doubleup l = List.concat (List.map (fn x => [x, x]) l)
in
   (*
   fun raw_pattern_opcode s =
      ([]: bool list, mk_pattern_opcode "TTTF" (Redblackmap.find (arm_pats, s)))
   *)
   fun mk_arm_pattern_opcode c s =
      let
         val (a, x) = alias s
         val v = case Redblackmap.peek (arm_pats, a) of
                    SOME p => mk_pattern_opcode c p
                  | NONE =>
                      (case Redblackmap.peek (arm_pats15, a) of
                          SOME p => mk_pattern_opcode "TTTT" p
                        | NONE => raise ERR "mk_arm_pattern_opcode"
                                            (a ^ "; not found"))
      in
         (if unconditional c then x else doubleup x, v)
      end
end

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
   fun reg_list_subst s =
      let
         val a = reg_array s
      in
         List.tabulate
           (16, fn i => Term.mk_var ("x" ^ Int.toString (i + 7), Type.bool) |->
                        Array.sub (a, 15 - i))
      end
end

local
   val prefix = fst o splitAtSpace
   fun x i = Term.mk_var ("x" ^ Int.toString i, Type.bool)
   fun xF i = x i |-> boolSyntax.F
   fun xT i = x i |-> boolSyntax.T
   val ast = Redblackmap.fromList String.compare
    [("B", ("BranchTarget", [])),
     ("BX", ("BranchExchange", [])),
     ("BX (pc)", ("BranchExchange", [xT 12, xT 13, xT 14, xT 15])),
     ("BL", ("BranchLinkExchangeImmediate (to ARM)", [])),
     ("BLX (imm)", ("BranchLinkExchangeImmediate (to Thumb)", [])),
     ("BLX (reg)", ("BranchLinkExchangeRegister", [])),
     ("CLZ", ("CountLeadingZeroes", [])),
     ("DMB", ("DataMemoryBarrier", [])),
     ("MOVT", ("MoveHalfword", [xT 0])),
     ("MOVW", ("MoveHalfword", [xF 0])),
     ("MOV (imm)", ("Move", [xF 0, xF 1])),
     ("MVN (imm)", ("Move", [xT 0, xF 1])),
     ("MOVS (imm)",("Move", [xF 0, xT 1])),
     ("MVNS (imm)",("Move", [xT 0, xT 1])),
     ("AND (imm)", ("ArithLogicImmediate", [xF 0, xF 1, xF 2, xF 3])),
     ("EOR (imm)", ("ArithLogicImmediate", [xF 0, xF 1, xT 2, xF 3])),
     ("SUB (imm)", ("ArithLogicImmediate", [xF 0, xT 1, xF 2, xF 3])),
     ("RSB (imm)", ("ArithLogicImmediate", [xF 0, xT 1, xT 2, xF 3])),
     ("ADD (imm)", ("ArithLogicImmediate", [xT 0, xF 1, xF 2, xF 3])),
     ("ADC (imm)", ("ArithLogicImmediate", [xT 0, xF 1, xT 2, xF 3])),
     ("SBC (imm)", ("ArithLogicImmediate", [xT 0, xT 1, xF 2, xF 3])),
     ("RSC (imm)", ("ArithLogicImmediate", [xT 0, xT 1, xT 2, xF 3])),
     ("ANDS (imm)",("ArithLogicImmediate", [xF 0, xF 1, xF 2, xT 3])),
     ("EORS (imm)",("ArithLogicImmediate", [xF 0, xF 1, xT 2, xT 3])),
     ("SUBS (imm)",("ArithLogicImmediate", [xF 0, xT 1, xF 2, xT 3])),
     ("RSBS (imm)",("ArithLogicImmediate", [xF 0, xT 1, xT 2, xT 3])),
     ("ADDS (imm)",("ArithLogicImmediate", [xT 0, xF 1, xF 2, xT 3])),
     ("ADCS (imm)",("ArithLogicImmediate", [xT 0, xF 1, xT 2, xT 3])),
     ("SBCS (imm)",("ArithLogicImmediate", [xT 0, xT 1, xF 2, xT 3])),
     ("RSCS (imm)",("ArithLogicImmediate", [xT 0, xT 1, xT 2, xT 3])),
     ("ORR (imm)", ("ArithLogicImmediate ORR/BIC", [xF 0, xF 1])),
     ("BIC (imm)", ("ArithLogicImmediate ORR/BIC", [xT 0, xF 1])),
     ("ORRS (imm)",("ArithLogicImmediate ORR/BIC", [xF 0, xT 1])),
     ("BICS (imm)",("ArithLogicImmediate ORR/BIC", [xT 0, xT 1])),
     ("TST (imm)", ("TestCompareImmediate", [xF 0, xF 1])),
     ("TEQ (imm)", ("TestCompareImmediate", [xF 0, xT 1])),
     ("CMP (imm)", ("TestCompareImmediate", [xT 0, xF 1])),
     ("CMN (imm)", ("TestCompareImmediate", [xT 0, xT 1])),
     ("MOV (reg)", ("ShiftImmediate", [xF 0, xF 1])),
     ("MVN (reg)", ("ShiftImmediate", [xT 0, xF 1])),
     ("MOVS (reg)",("ShiftImmediate", [xF 0, xT 1])),
     ("MVNS (reg)",("ShiftImmediate", [xT 0, xT 1])),
     ("AND (reg)", ("Register", [xF 0, xF 1, xF 2, xF 3])),
     ("EOR (reg)", ("Register", [xF 0, xF 1, xT 2, xF 3])),
     ("SUB (reg)", ("Register", [xF 0, xT 1, xF 2, xF 3])),
     ("RSB (reg)", ("Register", [xF 0, xT 1, xT 2, xF 3])),
     ("ADD (reg)", ("Register", [xT 0, xF 1, xF 2, xF 3])),
     ("ADC (reg)", ("Register", [xT 0, xF 1, xT 2, xF 3])),
     ("SBC (reg)", ("Register", [xT 0, xT 1, xF 2, xF 3])),
     ("RSC (reg)", ("Register", [xT 0, xT 1, xT 2, xF 3])),
     ("ANDS (reg)",("Register", [xF 0, xF 1, xF 2, xT 3])),
     ("EORS (reg)",("Register", [xF 0, xF 1, xT 2, xT 3])),
     ("SUBS (reg)",("Register", [xF 0, xT 1, xF 2, xT 3])),
     ("RSBS (reg)",("Register", [xF 0, xT 1, xT 2, xT 3])),
     ("ADDS (reg)",("Register", [xT 0, xF 1, xF 2, xT 3])),
     ("ADCS (reg)",("Register", [xT 0, xF 1, xT 2, xT 3])),
     ("SBCS (reg)",("Register", [xT 0, xT 1, xF 2, xT 3])),
     ("RSCS (reg)",("Register", [xT 0, xT 1, xT 2, xT 3])),
     ("ORR (reg)", ("Register ORR/BIC", [xF 0, xF 1])),
     ("BIC (reg)", ("Register ORR/BIC", [xT 0, xF 1])),
     ("ORRS (reg)",("Register ORR/BIC", [xF 0, xT 1])),
     ("BICS (reg)",("Register ORR/BIC", [xT 0, xT 1])),
     ("TST (reg)", ("TestCompareRegister", [xF 0, xF 1])),
     ("TEQ (reg)", ("TestCompareRegister", [xF 0, xT 1])),
     ("CMP (reg)", ("TestCompareRegister", [xT 0, xF 1])),
     ("CMN (reg)", ("TestCompareRegister", [xT 0, xT 1])),
     ("MOV (reg-shift)", ("ShiftRegister", [xF 0, xF 1])),
     ("MVN (reg-shift)", ("ShiftRegister", [xT 0, xF 1])),
     ("MOVS (reg-shift)",("ShiftRegister", [xF 0, xT 1])),
     ("MVNS (reg-shift)",("ShiftRegister", [xT 0, xT 1])),
     ("AND (reg-shift)", ("RegisterShiftedRegister", [xF 0, xF 1, xF 2, xF 3])),
     ("EOR (reg-shift)", ("RegisterShiftedRegister", [xF 0, xF 1, xT 2, xF 3])),
     ("SUB (reg-shift)", ("RegisterShiftedRegister", [xF 0, xT 1, xF 2, xF 3])),
     ("RSB (reg-shift)", ("RegisterShiftedRegister", [xF 0, xT 1, xT 2, xF 3])),
     ("ADD (reg-shift)", ("RegisterShiftedRegister", [xT 0, xF 1, xF 2, xF 3])),
     ("ADC (reg-shift)", ("RegisterShiftedRegister", [xT 0, xF 1, xT 2, xF 3])),
     ("SBC (reg-shift)", ("RegisterShiftedRegister", [xT 0, xT 1, xF 2, xF 3])),
     ("RSC (reg-shift)", ("RegisterShiftedRegister", [xT 0, xT 1, xT 2, xF 3])),
     ("ANDS (reg-shift)",("RegisterShiftedRegister", [xF 0, xF 1, xF 2, xT 3])),
     ("EORS (reg-shift)",("RegisterShiftedRegister", [xF 0, xF 1, xT 2, xT 3])),
     ("SUBS (reg-shift)",("RegisterShiftedRegister", [xF 0, xT 1, xF 2, xT 3])),
     ("RSBS (reg-shift)",("RegisterShiftedRegister", [xF 0, xT 1, xT 2, xT 3])),
     ("ADDS (reg-shift)",("RegisterShiftedRegister", [xT 0, xF 1, xF 2, xT 3])),
     ("ADCS (reg-shift)",("RegisterShiftedRegister", [xT 0, xF 1, xT 2, xT 3])),
     ("SBCS (reg-shift)",("RegisterShiftedRegister", [xT 0, xT 1, xF 2, xT 3])),
     ("RSCS (reg-shift)",("RegisterShiftedRegister", [xT 0, xT 1, xT 2, xT 3])),
     ("ORR (reg-shift)", ("RegisterShiftedRegister ORR/BIC", [xF 0, xF 1])),
     ("BIC (reg-shift)", ("RegisterShiftedRegister ORR/BIC", [xT 0, xF 1])),
     ("ORRS (reg-shift)",("RegisterShiftedRegister ORR/BIC", [xF 0, xT 1])),
     ("BICS (reg-shift)",("RegisterShiftedRegister ORR/BIC", [xT 0, xT 1])),
     ("TST (reg-shift)", ("TestCompareRegisterShiftedRegister", [xF 0, xF 1])),
     ("TEQ (reg-shift)", ("TestCompareRegisterShiftedRegister", [xF 0, xT 1])),
     ("CMP (reg-shift)", ("TestCompareRegisterShiftedRegister", [xT 0, xF 1])),
     ("CMN (reg-shift)", ("TestCompareRegisterShiftedRegister", [xT 0, xT 1])),
     ("MUL", ("Multiply32", [xF 0])),
     ("MLA", ("MultiplyAccumulate", [xF 0])),
     ("UMULL", ("MultiplyLong", [xF 0, xF 1, xF 2])),
     ("SMULL", ("MultiplyLong", [xT 0, xF 1, xF 2])),
     ("UMLAL", ("MultiplyLong", [xF 0, xT 1, xF 2])),
     ("SMLAL", ("MultiplyLong", [xT 0, xT 1, xF 2])),
     ("UMULLS", ("MultiplyLong", [xF 0, xF 1, xT 2])),
     ("SMULLS", ("MultiplyLong", [xT 0, xF 1, xT 2])),
     ("UMLALS", ("MultiplyLong", [xF 0, xT 1, xT 2])),
     ("SMLALS", ("MultiplyLong", [xT 0, xT 1, xT 2])),
     ("MULS", ("Multiply32", [xT 0])),
     ("MLAS", ("MultiplyAccumulate", [xT 0])),
     ("SMLA<XY>", ("Signed16Multiply32Accumulate", [])),
     ("SXT{A}B,UXT{A}B", ("ExtendByte", [])),
     ("SXT{A}B16,UXT{A}B16", ("ExtendByte16", [])),
     ("SXT{A}H,UXT{A}H", ("ExtendHalfword", [])),
     ("SEL", ("SelectBytes", [])),
     ("REV", ("ByteReverse", [])),
     ("REV16", ("ByteReversePackedHalfword", [])),
     ("REVSH", ("ByteReverseSignedHalfword", [])),
     ("RBIT", ("ReverseBits", [])),
     ("SBFX,UBFX", ("BitFieldExtract", [])),
     ("BFC", ("BitFieldClearOrInsert", [])),
     ("LDR (+imm,pre,wb)", ("LoadWord (imm,pre)", [xT 0, xT 1])),
     ("LDR (-imm,pre,wb)", ("LoadWord (imm,pre)", [xF 0, xT 1])),
     ("LDR (+imm,pre)", ("LoadWord (imm,pre)", [xT 0, xF 1])),
     ("LDR (-imm,pre)", ("LoadWord (imm,pre)", [xF 0, xF 1])),
     ("LDR (imm,post)", ("LoadWord (imm,post)", [])),
     ("LDR (+lit)", ("LoadWord (imm,pre;lit)", [xT 0, xT 2, xT 3, xT 4, xT 5])),
     ("LDR (-lit)", ("LoadWord (imm,pre;lit)", [xF 0, xT 2, xT 3, xT 4, xT 5])),
     ("LDR (+reg,pre,wb)", ("LoadWord (reg,pre)", [xT 0, xT 1])),
     ("LDR (-reg,pre,wb)", ("LoadWord (reg,pre)", [xF 0, xT 1])),
     ("LDR (+reg,pre)", ("LoadWord (reg,pre)", [xT 0, xF 1])),
     ("LDR (-reg,pre)", ("LoadWord (reg,pre)", [xF 0, xF 1])),
     ("LDR (+reg,pre,pc)",
        ("LoadWord (reg,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("LDR (-reg,pre,pc)",
        ("LoadWord (reg,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("LDR (reg,post)", ("LoadWord (reg,post)", [])),
     ("LDR (pc,+imm,pre,wb)",
        ("LoadWord (imm,pre)", [xT 0, xT 1, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,-imm,pre,wb)",
        ("LoadWord (imm,pre)", [xF 0, xT 1, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,+imm,pre)",
        ("LoadWord (imm,pre)", [xT 0, xF 1, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,-imm,pre)",
        ("LoadWord (imm,pre)", [xF 0, xF 1, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,imm,post)",
        ("LoadWord (imm,post)", [xT 5, xT 6, xT 7, xT 8])),
     ("LDR (pc,+reg,pre,wb)",
        ("LoadWord (reg,pre)", [xT 0, xT 1, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,-reg,pre,wb)",
        ("LoadWord (reg,pre)", [xF 0, xT 1, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,+reg,pre)",
        ("LoadWord (reg,pre)", [xT 0, xF 1, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,-reg,pre)",
        ("LoadWord (reg,pre)", [xF 0, xF 1, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,+reg,pre,pc)",
        ("LoadWord (reg,pre)",
         [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,-reg,pre,pc)",
        ("LoadWord (reg,pre)",
         [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5, xT 6, xT 7, xT 8, xT 9])),
     ("LDR (pc,reg,post)", ("LoadWord (reg,post)", [])),
     ("LDRB (+imm,pre,wb)", ("LoadByte (imm,pre)", [xT 0, xT 1])),
     ("LDRB (-imm,pre,wb)", ("LoadByte (imm,pre)", [xF 0, xT 1])),
     ("LDRB (+imm,pre)", ("LoadByte (imm,pre)", [xT 0, xF 1])),
     ("LDRB (-imm,pre)", ("LoadByte (imm,pre)", [xF 0, xF 1])),
     ("LDRB (imm,post)", ("LoadByte (imm,post)", [])),
     ("LDRB (+lit)",
        ("LoadByte (imm,pre;lit)", [xT 0, xT 2, xT 3, xT 4, xT 5])),
     ("LDRB (-lit)",
        ("LoadByte (imm,pre;lit)", [xF 0, xT 2, xT 3, xT 4, xT 5])),
     ("LDRB (+reg,pre,wb)", ("LoadByte (reg,pre)", [xT 0, xT 1])),
     ("LDRB (-reg,pre,wb)", ("LoadByte (reg,pre)", [xF 0, xT 1])),
     ("LDRB (+reg,pre)", ("LoadByte (reg,pre)", [xT 0, xF 1])),
     ("LDRB (-reg,pre)", ("LoadByte (reg,pre)", [xF 0, xF 1])),
     ("LDRB (+reg,pre,pc)",
        ("LoadByte (reg,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("LDRB (-reg,pre,pc)",
        ("LoadByte (reg,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("LDRB (reg,post)", ("LoadByte (reg,post)", [])),
     ("LDRSB (+imm,pre,wb)", ("LoadSignedByte (imm,pre)", [xT 0, xT 1])),
     ("LDRSB (-imm,pre,wb)", ("LoadSignedByte (imm,pre)", [xF 0, xT 1])),
     ("LDRSB (+imm,pre)", ("LoadSignedByte (imm,pre)", [xT 0, xF 1])),
     ("LDRSB (-imm,pre)", ("LoadSignedByte (imm,pre)", [xF 0, xF 1])),
     ("LDRSB (imm,post)", ("LoadSignedByte (imm,post)", [])),
     ("LDRSB (+lit)",
        ("LoadSignedByte (imm,post;lit)", [xT 0, xT 1, xT 2, xT 3, xT 4])),
     ("LDRSB (-lit)",
        ("LoadSignedByte (imm,post;lit)", [xF 0, xT 1, xT 2, xT 3, xT 4])),
     ("LDRSB (+reg,pre,wb)", ("LoadSignedByte (reg,pre)", [xT 0, xT 1])),
     ("LDRSB (-reg,pre,wb)", ("LoadSignedByte (reg,pre)", [xF 0, xT 1])),
     ("LDRSB (+reg,pre)", ("LoadSignedByte (reg,pre)", [xT 0, xF 1])),
     ("LDRSB (-reg,pre)", ("LoadSignedByte (reg,pre)", [xF 0, xF 1])),
     ("LDRSB (+reg,pre,pc)",
        ("LoadSignedByte (reg,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("LDRSB (-reg,pre,pc)",
        ("LoadSignedByte (reg,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("LDRSB (reg,post)", ("LoadSignedByte (reg,post)", [])),
     ("LDRBT (+imm)", ("LoadByteUnprivileged (imm)", [xT 0])),
     ("LDRBT (-imm)", ("LoadByteUnprivileged (imm)", [xF 0])),
     ("LDRBT (+reg)", ("LoadByteUnprivileged (reg)", [xT 0])),
     ("LDRBT (-reg)", ("LoadByteUnprivileged (reg)", [xF 0])),
     ("LDRH (+imm,pre,wb)", ("LoadHalf (imm,pre)", [xT 0, xT 1, xF 13])),
     ("LDRH (-imm,pre,wb)", ("LoadHalf (imm,pre)", [xF 0, xT 1, xF 13])),
     ("LDRH (+imm,pre)", ("LoadHalf (imm,pre)", [xT 0, xF 1, xF 13])),
     ("LDRH (-imm,pre)", ("LoadHalf (imm,pre)", [xF 0, xF 1, xF 13])),
     ("LDRH (imm,post)", ("LoadHalf (imm,post)", [xF 13])),
     ("LDRH (+lit)",
        ("LoadHalf (imm,post;lit)", [xT 0, xT 1, xT 2, xT 3, xT 4, xF 13])),
     ("LDRH (-lit)",
        ("LoadHalf (imm,post;lit)", [xF 0, xT 1, xT 2, xT 3, xT 4, xF 13])),
     ("LDRH (+reg,pre,wb)", ("LoadHalf (reg,pre)", [xT 0, xT 1, xF 13])),
     ("LDRH (-reg,pre,wb)", ("LoadHalf (reg,pre)", [xF 0, xT 1, xF 13])),
     ("LDRH (+reg,pre)", ("LoadHalf (reg,pre)", [xT 0, xF 1, xF 13])),
     ("LDRH (-reg,pre)", ("LoadHalf (reg,pre)", [xF 0, xF 1, xF 13])),
     ("LDRH (+reg,pre,pc)",
        ("LoadHalf (reg,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5, xF 13])),
     ("LDRH (-reg,pre,pc)",
        ("LoadHalf (reg,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5, xF 13])),
     ("LDRH (reg,post)", ("LoadHalf (reg,post)", [xF 13])),
     ("LDRSH (+imm,pre,wb)", ("LoadHalf (imm,pre)", [xT 0, xT 1, xT 13])),
     ("LDRSH (-imm,pre,wb)", ("LoadHalf (imm,pre)", [xF 0, xT 1, xT 13])),
     ("LDRSH (+imm,pre)", ("LoadHalf (imm,pre)", [xT 0, xF 1, xT 13])),
     ("LDRSH (-imm,pre)", ("LoadHalf (imm,pre)", [xF 0, xF 1, xT 13])),
     ("LDRSH (imm,post)", ("LoadHalf (imm,post)", [xT 13])),
     ("LDRSH (+lit)",
      ("LoadHalf (imm,post;lit)", [xT 0, xT 1, xT 2, xT 3, xT 4, xT 13])),
     ("LDRSH (-lit)",
      ("LoadHalf (imm,post;lit)", [xF 0, xT 1, xT 2, xT 3, xT 4, xT 13])),
     ("LDRSH (+reg,pre,wb)", ("LoadHalf (reg,pre)", [xT 0, xT 1, xT 13])),
     ("LDRSH (-reg,pre,wb)", ("LoadHalf (reg,pre)", [xF 0, xT 1, xT 13])),
     ("LDRSH (+reg,pre)", ("LoadHalf (reg,pre)", [xT 0, xF 1, xT 13])),
     ("LDRSH (-reg,pre)", ("LoadHalf (reg,pre)", [xF 0, xF 1, xT 13])),
     ("LDRSH (+reg,pre,pc)",
        ("LoadHalf (reg,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5, xT 13])),
     ("LDRSH (-reg,pre,pc)",
        ("LoadHalf (reg,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5, xT 13])),
     ("LDRSH (reg,post)", ("LoadHalf (reg,post)", [xT 13])),
     ("LDRD (+imm,pre,wb)", ("LoadDual (imm)", [xT 0, xT 1, xT 2])),
     ("LDRD (-imm,pre,wb)", ("LoadDual (imm)", [xT 0, xF 1, xT 2])),
     ("LDRD (+imm,pre)", ("LoadDual (imm)", [xT 0, xT 1, xF 2])),
     ("LDRD (-imm,pre)", ("LoadDual (imm)", [xT 0, xF 1, xF 2])),
     ("LDRD (imm,post)", ("LoadDual (imm)", [xF 0, xF 2])),
     ("LDRD (+lit)", ("LoadDual (imm;lit)", [xT 1, xT 3, xT 4, xT 5, xT 6])),
     ("LDRD (-lit)", ("LoadDual (imm;lit)", [xF 1, xT 3, xT 4, xT 5, xT 6])),
     ("LDRD (+reg,pre,wb)", ("LoadDual (reg)", [xT 0, xT 1, xT 2])),
     ("LDRD (-reg,pre,wb)", ("LoadDual (reg)", [xT 0, xF 1, xT 2])),
     ("LDRD (+reg,pre)", ("LoadDual (reg)", [xT 0, xT 1, xF 2])),
     ("LDRD (-reg,pre)", ("LoadDual (reg)", [xT 0, xF 1, xF 2])),
     ("LDRD (+reg,pre,pc)",
        ("LoadDual (reg)", [xT 0, xT 1, xF 2, xT 3, xT 4, xT 5, xT 6])),
     ("LDRD (-reg,pre,pc)",
        ("LoadDual (reg)", [xT 0, xF 1, xF 2, xT 3, xT 4, xT 5, xT 6])),
     ("LDRD (reg,post)", ("LoadDual (reg)", [xF 0, xF 2])),
     ("STR (+imm,pre,wb)", ("StoreWord (imm,pre)", [xT 0, xT 1])),
     ("STR (-imm,pre,wb)", ("StoreWord (imm,pre)", [xF 0, xT 1])),
     ("STR (+imm,pre)", ("StoreWord (imm,pre)", [xT 0, xF 1])),
     ("STR (-imm,pre)", ("StoreWord (imm,pre)", [xF 0, xF 1])),
     ("STR (+imm,pre,pc)",
        ("StoreWord (imm,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STR (-imm,pre,pc)",
        ("StoreWord (imm,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STR (imm,post)", ("StoreWord (imm,post)", [])),
     ("STR (+reg,pre,wb)", ("StoreWord (reg,pre)", [xT 0, xT 1])),
     ("STR (-reg,pre,wb)", ("StoreWord (reg,pre)", [xF 0, xT 1])),
     ("STR (+reg,pre)", ("StoreWord (reg,pre)", [xT 0, xF 1])),
     ("STR (-reg,pre)", ("StoreWord (reg,pre)", [xF 0, xF 1])),
     ("STR (+reg,pre,pc)",
        ("StoreWord (reg,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STR (-reg,pre,pc)",
        ("StoreWord (reg,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STR (reg,post)", ("StoreWord (reg,post)", [])),
     ("STRB (+imm,pre,wb)", ("StoreByte (imm,pre)", [xT 0, xT 1])),
     ("STRB (-imm,pre,wb)", ("StoreByte (imm,pre)", [xF 0, xT 1])),
     ("STRB (+imm,pre)", ("StoreByte (imm,pre)", [xT 0, xF 1])),
     ("STRB (-imm,pre)", ("StoreByte (imm,pre)", [xF 0, xF 1])),
     ("STRB (+imm,pre,pc)",
        ("StoreByte (imm,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STRB (-imm,pre,pc)",
        ("StoreByte (imm,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STRB (imm,post)", ("StoreByte (imm,post)", [])),
     ("STRB (+reg,pre,wb)", ("StoreByte (reg,pre)", [xT 0, xT 1])),
     ("STRB (-reg,pre,wb)", ("StoreByte (reg,pre)", [xF 0, xT 1])),
     ("STRB (+reg,pre)", ("StoreByte (reg,pre)", [xT 0, xF 1])),
     ("STRB (-reg,pre)", ("StoreByte (reg,pre)", [xF 0, xF 1])),
     ("STRB (+reg,pre,pc)",
        ("StoreByte (reg,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STRB (-reg,pre,pc)",
        ("StoreByte (reg,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STRB (reg,post)", ("StoreByte (reg,post)", [])),
     ("STRH (+imm,pre,wb)", ("StoreHalf (imm,pre)", [xT 0, xT 1])),
     ("STRH (-imm,pre,wb)", ("StoreHalf (imm,pre)", [xF 0, xT 1])),
     ("STRH (+imm,pre)", ("StoreHalf (imm,pre)", [xT 0, xF 1])),
     ("STRH (-imm,pre)", ("StoreHalf (imm,pre)", [xF 0, xF 1])),
     ("STRH (+imm,pre,pc)",
        ("StoreHalf (imm,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STRH (-imm,pre,pc)",
        ("StoreHalf (imm,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STRH (imm,post)", ("StoreHalf (imm,post)", [])),
     ("STRH (+reg,pre,wb)", ("StoreHalf (reg,pre)", [xT 0, xT 1])),
     ("STRH (-reg,pre,wb)", ("StoreHalf (reg,pre)", [xF 0, xT 1])),
     ("STRH (+reg,pre)", ("StoreHalf (reg,pre)", [xT 0, xF 1])),
     ("STRH (-reg,pre)", ("StoreHalf (reg,pre)", [xF 0, xF 1])),
     ("STRH (+reg,pre,pc)",
        ("StoreHalf (reg,pre)", [xT 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STRH (-reg,pre,pc)",
        ("StoreHalf (reg,pre)", [xF 0, xF 1, xT 2, xT 3, xT 4, xT 5])),
     ("STRH (reg,post)", ("StoreHalf (reg,post)", [])),
     ("STRD (+imm,pre,wb)", ("StoreDual (imm)", [xT 0, xT 1, xT 2])),
     ("STRD (-imm,pre,wb)", ("StoreDual (imm)", [xT 0, xF 1, xT 2])),
     ("STRD (+imm,pre)", ("StoreDual (imm)", [xT 0, xT 1, xF 2])),
     ("STRD (-imm,pre)", ("StoreDual (imm)", [xT 0, xF 1, xF 2])),
     ("STRD (imm,post)", ("StoreDual (imm)", [xF 0, xF 2])),
     ("STRD (+reg,pre,wb)", ("StoreDual (reg)", [xT 0, xT 1, xT 2])),
     ("STRD (-reg,pre,wb)", ("StoreDual (reg)", [xT 0, xF 1, xT 2])),
     ("STRD (+reg,pre)", ("StoreDual (reg)", [xT 0, xT 1, xF 2])),
     ("STRD (-reg,pre)", ("StoreDual (reg)", [xT 0, xF 1, xF 2])),
     ("STRD (reg,post)", ("StoreDual (reg)", [xF 0, xF 2])),
     ("LDMDA", ("LoadMultiple", [xF 0, xF 1, xF 2])),
     ("LDMDB", ("LoadMultiple", [xT 0, xF 1, xF 2])),
     ("LDMIA", ("LoadMultiple", [xF 0, xT 1, xF 2])),
     ("LDMIB", ("LoadMultiple", [xT 0, xT 1, xF 2])),
     ("LDMDA (wb)", ("LoadMultiple", [xF 0, xF 1, xT 2])),
     ("LDMDB (wb)", ("LoadMultiple", [xT 0, xF 1, xT 2])),
     ("LDMIA (wb)", ("LoadMultiple", [xF 0, xT 1, xT 2])),
     ("LDMIB (wb)", ("LoadMultiple", [xT 0, xT 1, xT 2])),
     ("STMDA", ("StoreMultiple", [xF 0, xF 1, xF 2])),
     ("STMDB", ("StoreMultiple", [xT 0, xF 1, xF 2])),
     ("STMIA", ("StoreMultiple", [xF 0, xT 1, xF 2])),
     ("STMIB", ("StoreMultiple", [xT 0, xT 1, xF 2])),
     ("STMDA (wb)", ("StoreMultiple", [xF 0, xF 1, xT 2])),
     ("STMDB (wb)", ("StoreMultiple", [xT 0, xF 1, xT 2])),
     ("STMIA (wb)", ("StoreMultiple", [xF 0, xT 1, xT 2])),
     ("STMIB (wb)", ("StoreMultiple", [xT 0, xT 1, xT 2])),
     ("SWP" , ("Swap", [xF 0])),
     ("SWPB", ("Swap", [xT 0])),
     ("SETEND", ("Setend", [xF 0])),
     ("VADD (single)", ("VFPData", [xF 0, xT 2, xT 3, xF 12, xF 14])),
     ("VADD (double)", ("VFPData", [xF 0, xT 2, xT 3, xT 12, xF 14])),
     ("VSUB (single)", ("VFPData", [xF 0, xT 2, xT 3, xF 12, xT 14])),
     ("VSUB (double)", ("VFPData", [xF 0, xT 2, xT 3, xT 12, xT 14])),
     ("VMUL (single)", ("VFPData", [xF 0, xT 2, xF 3, xF 12, xF 14])),
     ("VMUL (double)", ("VFPData", [xF 0, xT 2, xF 3, xT 12, xF 14])),
     ("VNMUL (single)", ("VFPData", [xF 0, xT 2, xF 3, xF 12, xT 14])),
     ("VNMUL (double)", ("VFPData", [xF 0, xT 2, xF 3, xT 12, xT 14])),
     ("VMLA (single)", ("VFPData", [xF 0, xF 2, xF 3, xF 12, xF 14])),
     ("VMLA (double)", ("VFPData", [xF 0, xF 2, xF 3, xT 12, xF 14])),
     ("VMLS (single)", ("VFPData", [xF 0, xF 2, xF 3, xF 12, xT 14])),
     ("VMLS (double)", ("VFPData", [xF 0, xF 2, xF 3, xT 12, xT 14])),
     ("VNMLA (single)", ("VFPData", [xF 0, xF 2, xT 3, xF 12, xT 14])),
     ("VNMLA (double)", ("VFPData", [xF 0, xF 2, xT 3, xT 12, xT 14])),
     ("VNMLS (single)", ("VFPData", [xF 0, xF 2, xT 3, xF 12, xF 14])),
     ("VNMLS (double)", ("VFPData", [xF 0, xF 2, xT 3, xT 12, xF 14])),
     ("VFMA (single)", ("VFPData", [xT 0, xT 2, xF 3, xF 12])),
     ("VFMA (double)", ("VFPData", [xT 0, xT 2, xF 3, xT 12])),
     ("VFNMA (single)", ("VFPData", [xT 0, xF 2, xT 3, xF 12])),
     ("VFNMA (double)", ("VFPData", [xT 0, xF 2, xT 3, xT 12])),
     ("VMOV (single,reg)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xF 5, xF 6, xF 7, xF 12, xF 13, xT 14])),
     ("VMOV (double,reg)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xF 5, xF 6, xF 7, xT 12, xF 13, xT 14])),
     ("VMOV (single,imm)", ("VFPData", [xT 0, xT 2, xT 3, xF 12, xF 14])),
     ("VMOV (double,imm)", ("VFPData", [xT 0, xT 2, xT 3, xT 12, xF 14])),
     ("VCMP (single,zero)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xT 5, xF 6, xT 7, xF 12, xT 13, xT 14])),
     ("VCMP (double,zero)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xT 5, xF 6, xT 7, xT 12, xT 13, xT 14])),
     ("VCMP (single)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xT 5, xF 6, xF 7, xF 12, xT 13, xT 14])),
     ("VCMP (double)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xT 5, xF 6, xF 7, xT 12, xT 13, xT 14])),
     ("VABS (single)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xF 5, xF 6, xF 7, xF 12, xT 13, xT 14])),
     ("VABS (double)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xF 5, xF 6, xF 7, xT 12, xT 13, xT 14])),
     ("VNEG (single)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xF 5, xF 6, xT 7, xF 12, xF 13, xT 14])),
     ("VNEG (double)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xF 5, xF 6, xT 7, xT 12, xF 13, xT 14])),
     ("VSQRT (single)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xF 5, xF 6, xT 7, xF 12, xT 13, xT 14])),
     ("VSQRT (double)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xF 5, xF 6, xT 7, xT 12, xT 13, xT 14])),
     ("VDIV (single)", ("VFPData", [xT 0, xF 2, xF 3, xF 12, xF 14])),
     ("VDIV (double)", ("VFPData", [xT 0, xF 2, xF 3, xT 12, xF 14])),
     ("VCVT (single,double)",
        ("VFPData",
         [xT 0, xT 2, xT 3, xF 4, xT 5, xT 6, xT 7, xT 12, xT 13, xT 14])),
     ("VCVT (double,single,lo)",
        ("VFPData",
         [xT 0, xF 1, xT 2, xT 3, xF 4, xT 5, xT 6, xT 7, xF 12, xT 13,
          xT 14])),
     ("VCVT (double,single,hi)",
        ("VFPData",
         [xT 0, xT 1, xT 2, xT 3, xF 4, xT 5, xT 6, xT 7, xF 12, xT 13,
          xT 14])),
     ("VCVT (signed int,single)",
        ("VFPData", [xT 0, xT 2, xT 3, xT 4, xT 5, xF 6, xT 7, xF 12, xT 14])),
     ("VCVT (unsigned int,single)",
        ("VFPData", [xT 0, xT 2, xT 3, xT 4, xT 5, xF 6, xF 7, xF 12, xT 14])),
     ("VCVT (signed int,double)",
        ("VFPData", [xT 0, xT 2, xT 3, xT 4, xT 5, xF 6, xT 7, xT 12, xT 14])),
     ("VCVT (unsigned int,double)",
        ("VFPData", [xT 0, xT 2, xT 3, xT 4, xT 5, xF 6, xF 7, xT 12, xT 14])),
     ("VCVT (single,int)",
        ("VFPData", [xT 0, xT 2, xT 3, xT 4, xF 5, xF 6, xF 7, xF 12, xT 14])),
     ("VCVT (double,int,lo)",
        ("VFPData",
         [xT 0, xF 1, xT 2, xT 3, xT 4, xF 5, xF 6, xF 7, xT 12, xT 14])),
     ("VCVT (double,int,hi)",
        ("VFPData",
         [xT 0, xT 1, xT 2, xT 3, xT 4, xF 5, xF 6, xF 7, xT 12, xT 14])),
     ("VLDR (single,+imm)", ("VFPLoadStore", [xT 0, xT 2, xF 11])),
     ("VLDR (single,-imm)", ("VFPLoadStore", [xF 0, xT 2, xF 11])),
     ("VLDR (double,+imm)", ("VFPLoadStore", [xT 0, xT 2, xT 11])),
     ("VLDR (double,-imm)", ("VFPLoadStore", [xF 0, xT 2, xT 11])),
     ("VLDR (single,+imm,pc)",
        ("VFPLoadStore", [xT 0, xT 2, xT 3, xT 4, xT 5, xT 6, xF 11])),
     ("VLDR (single,-imm,pc)",
        ("VFPLoadStore", [xF 0, xT 2, xT 3, xT 4, xT 5, xT 6, xF 11])),
     ("VLDR (double,+imm,pc)",
        ("VFPLoadStore", [xT 0, xT 2, xT 3, xT 4, xT 5, xT 6, xT 11])),
     ("VLDR (double,-imm,pc)",
        ("VFPLoadStore", [xF 0, xT 2, xT 3, xT 4, xT 5, xT 6, xT 11])),
     ("VSTR (single,+imm)", ("VFPLoadStore", [xT 0, xF 2, xF 11])),
     ("VSTR (single,-imm)", ("VFPLoadStore", [xF 0, xF 2, xF 11])),
     ("VSTR (double,+imm)", ("VFPLoadStore", [xT 0, xF 2, xT 11])),
     ("VSTR (double,-imm)", ("VFPLoadStore", [xF 0, xF 2, xT 11])),
     ("VSTR (single,+imm,pc)",
        ("VFPLoadStore", [xT 0, xF 2, xT 3, xT 4, xT 5, xT 6, xF 11])),
     ("VSTR (single,-imm,pc)",
        ("VFPLoadStore", [xF 0, xF 2, xT 3, xT 4, xT 5, xT 6, xF 11])),
     ("VSTR (double,+imm,pc)",
        ("VFPLoadStore", [xT 0, xF 2, xT 3, xT 4, xT 5, xT 6, xT 11])),
     ("VSTR (double,-imm,pc)",
        ("VFPLoadStore", [xF 0, xF 2, xT 3, xT 4, xT 5, xT 6, xT 11])),
     ("VMOV (single from arm)", ("VFPTransfer", [xF 0, xF 1, xF 2, xF 3])),
     ("VMOV (single to arm)", ("VFPTransfer", [xF 0, xF 1, xF 2, xT 3])),
     ("VMOV (singles from arm,lo)", ("VFPTransfer2", [xF 0, xF 9, xF 10])),
     ("VMOV (singles from arm,hi)", ("VFPTransfer2", [xF 0, xF 9, xT 10])),
     ("VMOV (singles to arm,lo)", ("VFPTransfer2", [xT 0, xF 9, xF 10])),
     ("VMOV (singles to arm,hi)", ("VFPTransfer2", [xT 0, xF 9, xT 10])),
     ("VMOV (double from arm)", ("VFPTransfer2", [xF 0, xT 9])),
     ("VMOV (double to arm)", ("VFPTransfer2", [xT 0, xT 9])),
     ("VMRS (nzcv)",
        ("VFPTransfer",
         [xT 0, xT 1, xT 2, xT 3, xF 4, xF 5, xF 6, xT 7,
          xT 8, xT 9, xT 10, xT 11])),
     ("VMRS",
        ("VFPTransfer", [xT 0, xT 1, xT 2, xT 3, xF 4, xF 5, xF 6, xT 7])),
     ("VMSR",
        ("VFPTransfer", [xT 0, xT 1, xT 2, xF 3, xF 4, xF 5, xF 6, xT 7])),
     ("MRS (cpsr)", ("MoveToRegisterFromSpecial", [])),
     ("MSR (cpsr, reg)", ("MoveToSpecialFromRegister", [xF 3])),
     ("MSR (cpsr, imm)", ("SpecialFromImmediate", [xF 3])),
     ("MSR (cpsr, reg, control)", ("MoveToSpecialFromRegister", [xT 3])),
     ("MSR (cpsr, imm, control)", ("MoveToSpecialFromImmediate", [xT 3])),
     ("RFEDA", ("ReturnFromException", [xF 0, xF 1, xF 2])),
     ("RFEDB", ("ReturnFromException", [xT 0, xF 1, xF 2])),
     ("RFEIA", ("ReturnFromException", [xF 0, xT 1, xF 2])),
     ("RFEIB", ("ReturnFromException", [xT 0, xT 1, xF 2])),
     ("RFEDA (wb)", ("ReturnFromException", [xF 0, xF 1, xT 2])),
     ("RFEDB (wb)", ("ReturnFromException", [xT 0, xF 1, xT 2])),
     ("RFEIA (wb)", ("ReturnFromException", [xF 0, xT 1, xT 2])),
     ("RFEIB (wb)", ("ReturnFromException", [xT 0, xT 1, xT 2])),
     ("NOP", ("Hint", List.tabulate (8, xF)))
     ]
   fun list_instructions () = List.map fst (Redblackmap.listItems ast)
   fun printn s = TextIO.print (s ^ "\n")
   fun lsub s i = Char.toUpper (String.sub (s, i))
   fun sharePrefix3 s1 s2 =
      let
         val n = Int.min (3, Int.min (String.size s1, String.size s2))
         val f1 = lsub s1
         val f2 = lsub s2
         fun loop i = i >= n orelse f1 i = f2 i andalso loop (i + 1)
      in
         loop 0
      end
   val condMap =
      fn "EQ" => SOME "FFFF"
       | "NE" => SOME "FFFT"
       | "CS" => SOME "FFTF"
       | "CC" => SOME "FFTT"
       | "MI" => SOME "FTFF"
       | "PL" => SOME "FTFT"
       | "VS" => SOME "FTTF"
       | "VC" => SOME "FTTT"
       | "HI" => SOME "TFFF"
       | "LS" => SOME "TFFT"
       | "GE" => SOME "TFTF"
       | "LT" => SOME "TFTT"
       | "GT" => SOME "TTFF"
       | "LE" => SOME "TTFT"
       | "AL" => SOME "TTTF"
       | _ => NONE
   val condMapInv =
      fn "FFFF" => "EQ"
       | "FFFT" => "NE"
       | "FFTF" => "CS"
       | "FFTT" => "CC"
       | "FTFF" => "MI"
       | "FTFT" => "PL"
       | "FTTF" => "VS"
       | "FTTT" => "VC"
       | "TFFF" => "HI"
       | "TFFT" => "LS"
       | "TFTF" => "GE"
       | "TFTT" => "LT"
       | "TTFF" => "GT"
       | "TTFT" => "LE"
       | _ => ""
   fun insertCond c s =
      let
         val (a, b) = splitAtSpace s
      in
         a ^ c ^ b
      end
   fun LDM_STM s = String.isPrefix "LDM" s orelse String.isPrefix "STM" s
   fun comma i =
      let
         val is = Int.toString i
      in
         fn "" => is
          | s => is ^ "," ^ s
      end
   fun insertRegList opc s =
      if LDM_STM s
         then s ^ ";" ^
              snd (List.foldr
                     (fn (t, (i, s)) =>
                         (i + 1, if t = boolSyntax.T then comma i s else s))
                     (0, "") (List.drop (opc, 16)))
      else s
   val prefixes = List.rev (mlibUseful.sort_map String.size Int.compare
                              (List.map prefix (list_instructions ())))
   val splitAtSemi = utilsLib.splitAtChar (Lib.equal #";")
   fun splitOpcode s =
      let
         val (a, b) =
            (utilsLib.uppercase ## utilsLib.lowercase) (splitAtSpace s)
         val (a, b, c) =
            if b = ""
               then let val (a, c) = splitAtSemi a in (a, b, c) end
            else let val (b, c) = splitAtSemi b in (a, b, c) end
         val c = if c <> "" then String.extract (c, 1, NONE) else "none"
         val d = ("TTTF", a ^ b, c)
         val pfx = if String.size a = 3 andalso String.isPrefix "BL" a
                      then SOME "B"
                   else if String.size a = 5 andalso String.isPrefix "STRH" a
                      then SOME "STR"
                   else if String.size a = 5 andalso String.isPrefix "LDRH" a
                      then SOME "LDR"
                   else List.find (fn p => String.isPrefix p a) prefixes
      in
         case pfx of
            SOME p =>
               let
                  val a' = String.extract (a, String.size p, NONE)
                  val n = String.size a'
               in
                  if 1 < n
                     then let
                             val (l, r) = utilsLib.splitAtPos (n - 2) a'
                          in
                             case condMap r of
                                SOME cond => (cond, p ^ l ^ b, c)
                              | NONE => d
                          end
                  else d
               end
          | NONE => d
      end
   fun bit tm = if bitstringSyntax.dest_b tm then #"T" else #"F"
   val bitstring = String.implode o List.map bit
in
   val list_instructions = list_instructions
   fun print_instructions () = List.app printn (list_instructions ())
   fun mk_arm_opcode s =
      let
         val (c, s, l) = splitOpcode s
         val lm = if LDM_STM s andalso l <> "none" then reg_list_subst l else []
      in
         case Redblackmap.peek (ast, s) of
            SOME (s, m) =>
              (I ## Term.subst (m @ lm)) (mk_arm_pattern_opcode c s)
          | NONE =>
              let
                 val p = List.filter (sharePrefix3 s) (list_instructions ())
                         |> Lib.commafy
                         |> String.concat
                 val p = if p = "" then "." else ". Try: " ^ p
              in
                 raise ERR "mk_arm_opcode" ("Not found: " ^ s ^ p)
              end
      end
   fun arm_instruction i =
      let
         val c = bitstring (List.take (i, 4))
         val opc = listSyntax.mk_list (i, Type.bool)
         val ins = insertCond (condMapInv c)
         fun mtch s = Term.match_term (snd (mk_arm_opcode (ins s))) opc
      in
         List.map (insertRegList i o ins)
           (List.filter (Lib.can mtch) (list_instructions()))
      end
end

(* -- *)

local
   fun f thm ps = List.map (DecodeARM_rwt thm) (List.map snd ps)
   val rwts_14 = f DecodeARM_14 arm_patterns
   val rwts_15 = f DecodeARM_15 arm_patterns15
   val rwts_other = f DecodeARM_other arm_patterns
   val undef =
      List.map (DATATYPE_RULE o Thm.INST [state_with_enc ``Encoding_ARM``])
               UndefinedARM_rwt
   val se = fix_datatype ``^st with Encoding := Encoding_ARM``
   val DecodeARM_tm = mk_arm_const "DecodeARM"
   fun mk_decode_arm t = Term.list_mk_comb (DecodeARM_tm, [t, se])
   val rewrites =
      [v2w_13_15_rwts,
       bitstringLib.v2n_CONV ``v2n [F;F;F;F;F]``,
       blastLib.BBLAST_PROVE
         ``((v2w [T;T;b;T] = 13w: word4) \/ (v2w [T;T;b;T] = 15w: word4)) = T``]
   val COND_RULE =
      Conv.RIGHT_CONV_RULE (REG_CONV THENC REWRITE_CONV iConditionPassed_rwts) o
      utilsLib.ALL_HYP_CONV_RULE REG_CONV
   val raise_tm = mk_arm_const "raise'exception"
   val avoid =
      List.filter
         (not o Lib.can (HolKernel.find_term (Term.same_const raise_tm) o rhsc))
   val FINISH_RULE =
      List.map
        (utilsLib.MATCH_HYP_CONV_RULE (Conv.REWR_CONV bool_not_pc)
            ``~(b3 /\ b2 /\ b1 /\ b0)`` o
         Conv.RIGHT_CONV_RULE
            (REG_CONV THENC Conv.DEPTH_CONV bitstringLib.v2n_CONV))
   val rwconv = REWRITE_CONV rewrites
in
   fun arm_decode tms =
      let
         val x = (DATATYPE_CONV, fix_datatypes tms)
         fun gen_rws m r = rewrites @ utilsLib.specialized m x r
         val rw14 = REWRITE_CONV (gen_rws "decode ARM (cond = 14)" rwts_14)
         val rw15 = REWRITE_CONV (gen_rws "decode ARM (cond = 15)" rwts_15)
         val net =
            utilsLib.mk_rw_net utilsLib.lhsc
               (utilsLib.specialized
                  "decode ARM (cond not in {14, 15})" x rwts_other)
         fun find_rw_other tm =
            Lib.singleton_of_list (utilsLib.find_rw net tm)
            handle HOL_ERR {message = "not found", ...} => raise Conv.UNCHANGED
                 | HOL_ERR {message = m,
                            origin_function = "singleton_of_list", ...} =>
                               raise ERR "arm_decode"
                                         "more than one matching decode pattern"
         val FALL_CONV =
            REWRITE_CONV
               (DecodeVFP :: datatype_thms [v2w_ground4] @ undef @
                iConditionPassed_rwts @
                gen_rws "decode ARM (fallback)" [DecodeARM_fall])
      in
         fn (x : bool list, v) =>
            let
               val (c, t) = mk_opcode v
               val tm = mk_decode_arm t
            in
               ((case c of
                    Cond14 => rw14 tm
                  | Cond15 => rw15 tm
                  | Cond cnd =>
                      let
                         val rwt = tm |> find_rw_other
                                      |> Thm.INST cnd
                                      |> COND_RULE
                      in
                         (Conv.REWR_CONV rwt THENC rwconv) tm
                      end)
                handle Conv.UNCHANGED =>
                           ( WARN "arm_decode" "fallback (slow) decode"
                           ; FALL_CONV tm ))
               |> utilsLib.split_conditions
               |> avoid
               |> utilsLib.pick x
               |> FINISH_RULE
            end
      end
end

local
   fun uncond c = Lib.mem (Char.toUpper c) [#"E", #"F"]
in
   fun arm_decode_hex opt =
      let
         val dec = arm_decode (arm_configLib.mk_config_terms opt)
      in
         fn s =>
            let
               val s = utilsLib.removeSpaces s
               val v = bitstringSyntax.bitstring_of_hexstring s
               val x = if String.size s = 8 andalso uncond (String.sub (s, 0))
                          then [true]
                       else [true, true]
            in
               dec (x, v)
            end
      end
end

(* ========================================================================= *)

(* Run *)

val NoOperation_rwt =
   EV [dfn'NoOperation_def, IncPC_rwt] [] []
      ``dfn'NoOperation``
   |> addThms

val DataMemoryBarrier_rwt =
   EV [dfn'DataMemoryBarrier_def, IncPC_rwt] [] []
      ``dfn'DataMemoryBarrier opt``
   |> addThms

(* ---------------------------- *)

val Setend_rwt =
   EV [dfn'Setend_def, IncPC_rwt] [] []
      ``dfn'Setend b``
   |> addThms

(* ---------------------------- *)

val BranchTarget_rwts =
   let
      val thms = [dfn'BranchTarget_def, PC_rwt, not_cond, align_aligned]
      val tm =
         ``aligned 2 (s.REG RName_PC + (if s.CPSR.T then 4w else 8w) + imm32)``
   in
     (
      EV (hd BranchWritePC_rwt :: thms) [] []
        ``dfn'BranchTarget imm32``
      |> List.map (utilsLib.ALL_HYP_RULE
                     (utilsLib.INST_REWRITE_RULE [Aligned_BranchTarget_thumb]))
     )
      @
     (
      EV (tl BranchWritePC_rwt @ thms) [] []
        ``dfn'BranchTarget imm32``
      |> List.map (utilsLib.ALL_HYP_CONV_RULE
                     (utilsLib.INST_REWRITE_CONV [ASSUME tm]
                      THENC REWRITE_CONV []))
      |> List.map (utilsLib.ALL_HYP_RULE
                     (utilsLib.INST_REWRITE_RULE [Aligned_BranchTarget_arm]))
     )
     |> addThms
   end

(* ---------------------------- *)

val BranchExchange_rwt =
   EV ([dfn'BranchExchange_def, R_rwt, BXWritePC_rwt, CurrentInstrSet_rwt,
        Align_LoadWritePC] @ SelectInstrSet_rwt)
      [[``m <> 15w: word4``]] []
      ``dfn'BranchExchange m``
     |> List.map COND_UPDATE_RULE
     |> addThms

val BranchExchange_pc_arm_rwt =
   EV ([dfn'BranchExchange_def, BXWritePC_rwt, R15_rwt,
        arm_stepTheory.Aligned4_bit0, CurrentInstrSet_rwt] @ SelectInstrSet_rwt)
      [[``~^st.CPSR.T``]] []
      ``dfn'BranchExchange 15w``
     |> List.map
          (utilsLib.MATCH_HYP_CONV_RULE
              (utilsLib.INST_REWRITE_CONV
                  [arm_stepTheory.Aligned4_bit0, arm_stepTheory.Aligned4_bit1]
               THENC REWRITE_CONV []) ``a ==> b``)

val BranchExchange_pc_thumb_rwt =
   EV ([dfn'BranchExchange_def, BXWritePC_rwt, R15_rwt,
        Aligned4_bit0_t, CurrentInstrSet_rwt] @ SelectInstrSet_rwt)
      [[``^st.CPSR.T``]] []
      ``dfn'BranchExchange 15w``
     |> List.map
          (utilsLib.MATCH_HYP_CONV_RULE
              (utilsLib.INST_REWRITE_CONV
                  [arm_stepTheory.Aligned4_bit0_t,
                   arm_stepTheory.Aligned4_bit1_t]
               THENC REWRITE_CONV []) ``a ==> b``)

(* ---------------------------- *)

val R_x_14_not_pc =
   arm_stepTheory.R_x_not_pc
   |> Q.INST [`d` |-> `14w: word4`]
   |> utilsLib.ALL_HYP_CONV_RULE wordsLib.WORD_EVAL_CONV

val BranchLinkExchangeRegister_rwt =
   EV ([dfn'BranchLinkExchangeRegister_def, R_rwt, write'R_rwt, PC_rwt,
        BXWritePC_rwt, CurrentInstrSet_rwt, write'LR_def, R_x_14_not_pc,
        not_cond, Align_LoadWritePC] @ SelectInstrSet_rwt)
      [[``m <> 15w: word4``]] []
      ``dfn'BranchLinkExchangeRegister m``
     |> List.map
          (COND_UPDATE_RULE o
           utilsLib.ALL_HYP_CONV_RULE
             (DATATYPE_CONV
              THENC REWRITE_CONV [PC_rwt, boolTheory.COND_ID]
              THENC wordsLib.WORD_EVAL_CONV) o
           utilsLib.SRW_RULE [])
     |> addThms

(* ---------------------------- *)

fun BranchLinkExchangeImmediate_rwt (c, t, rwt) =
   EV ([dfn'BranchLinkExchangeImmediate_def, write'R_rwt, PC_rwt,
        CurrentInstrSet_rwt, write'LR_def, R_x_14_not_pc] @
        SelectInstrSet_rwt) [[c]] []
     ``dfn'BranchLinkExchangeImmediate (^t, imm32)``
     |> List.map
          (utilsLib.ALL_HYP_CONV_RULE
             (DATATYPE_CONV
              THENC REWRITE_CONV [PC_rwt, boolTheory.COND_ID]
              THENC wordsLib.WORD_EVAL_CONV))
     |> List.map
          (utilsLib.MATCH_HYP_CONV_RULE
              (REWRITE_CONV [Aligned_Align_plus_minus]) ``a \/ b : bool`` o
           FULL_DATATYPE_RULE o
           Conv.CONV_RULE (utilsLib.INST_REWRITE_CONV [rwt]))

val BranchLinkExchangeImmediate_thumb_arm_rwt =
   BranchLinkExchangeImmediate_rwt
     (``^st.CPSR.T``, ``InstrSet_ARM``, hd (tl BranchWritePC_rwt))
     |> addThms

val BranchLinkExchangeImmediate_thumb_thumb_rwt =
   BranchLinkExchangeImmediate_rwt
     (``^st.CPSR.T``, ``InstrSet_Thumb``, hd BranchWritePC_rwt)
     |> List.map
          (utilsLib.INST_REWRITE_RULE
             [AlignedPC_plus_xthumb, AlignedPC_plus_thumb])
     |> addThms

local
   val rule =
      REWRITE_RULE [blastLib.BBLAST_PROVE ``w + 8w - 4w = w + 4w: word32``]
in
   val BranchLinkExchangeImmediate_arm_arm_rwt =
      BranchLinkExchangeImmediate_rwt
        (``~^st.CPSR.T``, ``InstrSet_ARM``, hd (tl BranchWritePC_rwt))
        |> List.map
             (rule o utilsLib.INST_REWRITE_RULE [AlignedPC_plus_align_arm])
        |> addThms
   val BranchLinkExchangeImmediate_arm_thumb_rwt =
      BranchLinkExchangeImmediate_rwt
        (``~^st.CPSR.T``, ``InstrSet_Thumb``, hd BranchWritePC_rwt)
        |> List.map (rule o utilsLib.INST_REWRITE_RULE [AlignedPC_plus_xarm])
        |> addThms
end

(* ---------------------------- *)

val IfThen_rwt =
   EV [dfn'IfThen_def, IncPC_rwt] [] []
      ``dfn'IfThen (firstcond, mask)``
      |> addThms

(* ---------------------------- *)

(*
val () = setEvConv (Conv.DEPTH_CONV
            (bitstringLib.extract_v2w_CONV
             ORELSEC bitstringLib.v2w_eq_CONV
             ORELSEC bitstringLib.word_bit_CONV))
*)

val () = setEvConv utilsLib.WGROUND_CONV

(*
val DataProcessingPC_nsetflags_rwt =
   List.map (fn (r, w) =>
      EV [r, addInstTag w, arm_stepTheory.R_x_not_pc,
          SET_RULE DataProcessingPC_def, DataProcessingALU_def,
          AddWithCarry, wordsTheory.FST_ADD_WITH_CARRY,
          ArithmeticOpcode_def, PC_rwt, IncPC_rwt, cond_rand_thms] []
         (mapl (`opc`, utilsLib.tab_fixedwidth 16 4))
         ``DataProcessingPC (opc, F, n, imm32)``) reg_rwts
      |> List.concat
*)

local
   val x = ``x: word32 # bool``
   val DataProcessing =
      DataProcessing_def
      |> Q.SPECL [`opc`, `setflags`, `d`, `n`, `FST ^x`, `SND ^x`]
      |> REWRITE_RULE [pairTheory.PAIR]
      |> utilsLib.SET_RULE
   val DataProcessing_rwts =
      List.map
         (fn opc =>
            let
               val i = wordsSyntax.uint_of_word opc
               val wr = if i < 8 orelse 11 < i then [write'R_rwt] else []
            in
               EV ([R_rwt, arm_stepTheory.R_x_not_pc,
                   DataProcessing, DataProcessingALU_def,
                   AddWithCarry, wordsTheory.FST_ADD_WITH_CARRY,
                   ArithmeticOpcode_def, PC_rwt, IncPC_rwt, cond_rand_thms,
                   unit_state_cond] @ wr) [] [[`opc` |-> opc]]
                  ``DataProcessing (opc, setflags, d, n, imm32_c)``
            end
            |> List.map
                 (utilsLib.ALL_HYP_CONV_RULE
                     (REWRITE_CONV [boolTheory.COND_ID]) o
                  SIMP_RULE bool_ss [])) opcodes
in
   fun dp n = List.nth (DataProcessing_rwts, n)
end

val mov_mvn = dp 13 @ dp 15
val al = List.concat (List.tabulate (8, fn i => dp i) @ [dp 12, dp 14])
val tc = List.concat (List.tabulate (4, fn i => dp (8 + i)))

(* ---------------------------- *)

val () = setEvConv utilsLib.WGROUND_CONV

(*
val AddSub_rwt =
   EV [dfn'AddSub_def] [] (TF `sub`)
      ``dfn'AddSub (sub, d, n, imm12)``
      |> addThms
*)

val Move_rwt =
   EV ([dfn'Move_def, ExpandImm_C_rwt, bitstringTheory.word_concat_v2w_rwt,
        utilsLib.map_conv bitstringLib.v2w_n2w_CONV
           [``v2w [T] : word1``, ``v2w [F] : word1``],
        wordsTheory.WORD_OR_CLAUSES] @ mov_mvn)
      [[``d <> 15w: word4``]] (TF `negate`)
      ``dfn'Move (setflags, negate, d, ^(bitstringSyntax.mk_vec 12 0))``
   |> List.map (utilsLib.MATCH_HYP_CONV_RULE
                   (REWRITE_CONV [wordsTheory.WORD_OR_CLAUSES])
                   ``a \/ b \/ c : bool``)
   |> addThms

val () = setEvConv (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV
                    THENC utilsLib.WGROUND_CONV)

val TestCompareImmediate_rwt =
   EV ([dfn'TestCompareImmediate_def, bitstringTheory.word_concat_v2w_rwt,
        ExpandImm_C_rwt] @ tc) []
      (mapl (`op`, utilsLib.tab_fixedwidth 4 2))
      ``dfn'TestCompareImmediate (op, n, ^(bitstringSyntax.mk_vec 12 0))``
   |> addThms

val ArithLogicImmediate_rwt =
   EV ([dfn'ArithLogicImmediate_def, bitstringTheory.word_concat_v2w_rwt,
       ExpandImm_C_rwt] @ al)
      [[``d <> 15w: word4``]] (mapl (`op`, arithlogic))
      ``dfn'ArithLogicImmediate
           (op, setflags, d, n, ^(bitstringSyntax.mk_vec 12 0))``
   |> addThms

(* ---------------------------- *)

val () = setEvConv utilsLib.WGROUND_CONV

val ShiftImmediate_rwt =
   EV ([dfn'ShiftImmediate_def, R_rwt, doRegister_def, ArithmeticOpcode_def,
        Shift_C_DecodeImmShift_rwt, wordsTheory.WORD_OR_CLAUSES] @ mov_mvn)
      [[``d <> 15w: word4``]] (TF `negate`)
      ``dfn'ShiftImmediate
          (negate, setflags, d, m,
           FST (DecodeImmShift (v2w [a; b], imm5)),
           SND (DecodeImmShift (v2w [a; b], imm5)))``
      |> List.map (utilsLib.ALL_HYP_CONV_RULE
                     (REWRITE_CONV [wordsTheory.WORD_OR_CLAUSES]) o
                   REWRITE_RULE [])
      |> addThms

val () = setEvConv (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV
                    THENC utilsLib.WGROUND_CONV)

val TestCompareRegister_rwt =
   EV ([dfn'TestCompareRegister_def, R_rwt, bitstringTheory.word_concat_v2w_rwt,
        doRegister_def, ArithmeticOpcode_def, Shift_C_DecodeImmShift_rwt] @ tc)
      []
      (mapl (`op`, utilsLib.tab_fixedwidth 4 2))
      ``dfn'TestCompareRegister
          (op, n, m,
           FST (DecodeImmShift (v2w [a; b], imm5)),
           SND (DecodeImmShift (v2w [a; b], imm5)))``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV []) o
                REWRITE_RULE [])
   |> addThms

val () = setEvConv utilsLib.WGROUND_CONV

val Register_rwt =
   EV ([dfn'Register_def, R_rwt, doRegister_def, ArithmeticOpcode_def,
        Shift_C_DecodeImmShift_rwt] @ al)
      [[``d <> 15w: word4``]] (mapl (`op`, arithlogic))
      ``dfn'Register
          (op, setflags, d, n, m,
           FST (DecodeImmShift (v2w [a; b], imm5)),
           SND (DecodeImmShift (v2w [a; b], imm5)))``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV []) o
                REWRITE_RULE [])
   |> addThms

(* ---------------------------- *)

val () = setEvConv utilsLib.WGROUND_CONV

val ShiftRegister_rwt =
   EV ([dfn'ShiftRegister_def, R_rwt, doRegisterShiftedRegister_def,
        ArithmeticOpcode_def, Shift_C_DecodeRegShift_rwt,
        wordsTheory.WORD_OR_CLAUSES] @ mov_mvn)
      [[``d <> 15w: word4``, ``n <> 15w: word4``, ``m <> 15w: word4``]]
      (TF `negate`)
      ``dfn'ShiftRegister
          (negate, setflags, d, n, DecodeRegShift (v2w [a; b]), m)``
   |> List.map
        (utilsLib.ALL_HYP_CONV_RULE
           (REWRITE_CONV [Shift_C_DecodeRegShift_rwt,
                          wordsTheory.WORD_OR_CLAUSES]))
   |> addThms

val TestCompareRegisterShiftedRegister_rwt =
   EV ([dfn'RegisterShiftedRegister_def, R_rwt, doRegisterShiftedRegister_def,
        ArithmeticOpcode_def, Shift_C_DecodeRegShift_rwt] @ tc)
      [[``n <> 15w: word4``, ``m <> 15w: word4``, ``r <> 15w: word4``]]
      (mapl (`op`, testcompare))
      ``dfn'RegisterShiftedRegister
          (op, T, d, n, m, DecodeRegShift (v2w [a; b]), r)``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE
                  (REWRITE_CONV [Shift_C_DecodeRegShift_rwt]))
   |> addThms

val RegisterShiftedRegister_rwt =
   EV ([dfn'RegisterShiftedRegister_def, R_rwt, doRegisterShiftedRegister_def,
        ArithmeticOpcode_def, Shift_C_DecodeRegShift_rwt] @ al)
      [[``d <> 15w: word4``, ``n <> 15w: word4``, ``m <> 15w: word4``,
        ``r <> 15w: word4``]]
      (mapl (`op`, arithlogic))
      ``dfn'RegisterShiftedRegister
          (op, setflags, d, n, m, DecodeRegShift (v2w [a; b]), r)``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE
                   (REWRITE_CONV [Shift_C_DecodeRegShift_rwt]))
   |> addThms

(* ---------------------------- *)

val () = resetEvConv ()

val CountLeadingZeroes_rwt =
   regEV [`d`] [dfn'CountLeadingZeroes_def] [] []
      ``dfn'CountLeadingZeroes (d, m)``

val MoveHalfword_rwt =
   regEV [`d`] [dfn'MoveHalfword_def] [] (TF `neg`)
      ``dfn'MoveHalfword (neg, d, imm16)``

(* ---------------------------- *)

val Multiply32_rwt =
   regEV [`d`] [dfn'Multiply32_def, unit_state_cond]
      [[``n <> 15w: word4``, ``m <> 15w: word4``]] []
      ``dfn'Multiply32 (setflags, d, n, m)``

val MultiplyAccumulate_rwt =
   regEV [`d`] [dfn'MultiplyAccumulate_def, unit_state_cond]
      [[``n <> 15w: word4``, ``m <> 15w: word4``, ``a <> 15w: word4``]] []
      ``dfn'MultiplyAccumulate (setflags, d, n, m, a)``

val MultiplyLong_rwt =
   regEV [`dhi: word4`, `dlo: word4`] [dfn'MultiplyLong_def, unit_state_cond]
      [[``dhi <> 15w: word4``, ``dlo <> 15w: word4``,
        ``n <> 15w: word4``, ``m <> 15w: word4``]] (TF `signed`)
      ``dfn'MultiplyLong (accumulate, signed, setflags, dhi, dlo, n, m)``

val Signed16Multiply32Accumulate_rwt =
   EV ([dfn'Signed16Multiply32Accumulate_def, IncPC_rwt, R_rwt, write'R_rwt] @
       npc_thm [`d`])
      [[``d <> 15w: word4``, ``n <> 15w: word4``,
        ``m <> 15w: word4``, ``a <> 15w: word4``]] []
      ``dfn'Signed16Multiply32Accumulate (m_high, n_high, d, n, m, a)``
   |> List.map (FULL_DATATYPE_RULE o COND_UPDATE_RULE)
   |> addThms

(* ---------------------------- *)

(* Media *)

val ExtendByte_rwt =
  regEV [`d`] [dfn'ExtendByte_def, ROR_rwt]
     [[``d <> 15w: word4``, ``m <> 15w: word4``]] []
     ``dfn'ExtendByte (u, d, n, m, rot)``

val ExtendByte16_rwt =
   regEV [`d`] [dfn'ExtendByte16_def, ROR_rwt]
      [[``d <> 15w: word4``, ``m <> 15w: word4``]] []
      ``dfn'ExtendByte16 (U, d, n, m, rot)``

val ExtendHalfword_rwt =
  regEV [`d`] [dfn'ExtendHalfword_def, ROR_rwt]
     [[``d <> 15w: word4``, ``m <> 15w: word4``]] []
     ``dfn'ExtendHalfword (u, d, n, m, rot)``

val SelectBytes_rwt =
  regEV [`d`] [dfn'SelectBytes_def]
     [[``d <> 15w: word4``, ``n <> 15w: word4``, ``m <> 15w: word4``]] []
     ``dfn'SelectBytes (d, n, m)``

val ByteReverse_rwt =
   regEV [`d`] [dfn'ByteReverse_def]
      [[``d <> 15w: word4``, ``m <> 15w:word4``]] []
      ``dfn'ByteReverse (d, m)``

val ByteReversePackedHalfword_rwt =
   regEV [`d`] [dfn'ByteReversePackedHalfword_def]
      [[``d <> 15w: word4``, ``m <> 15w:word4``]] []
      ``dfn'ByteReversePackedHalfword (d, m)``

val ByteReverseSignedHalfword_rwt =
   regEV [`d`] [dfn'ByteReverseSignedHalfword_def]
      [[``d <> 15w: word4``, ``m <> 15w:word4``]] []
      ``dfn'ByteReverseSignedHalfword (d, m)``

val ReverseBits_rwt =
   regEV [`d`] [dfn'ReverseBits_def]
      [[``d <> 15w: word4``, ``m <> 15w:word4``]] []
      ``dfn'ReverseBits (d, m)``

val BitFieldExtract_rwt =
   regEV [`d`] [dfn'BitFieldExtract_def]
      [[``d <> 15w: word4``, ``n <> 15w: word4``]] []
      ``dfn'BitFieldExtract (U, d, n, lsb, widthminus1)``

val BitFieldClearOrInsert_rwt =
   regEV [`d`] [dfn'BitFieldClearOrInsert_def, field_insert]
     [[``d <> 15w: word4``]] []
      ``dfn'BitFieldClearOrInsert (d, n, lsb, msb)``

(* Add a few more multiplies and SIMD instructions *)

(* ---------------------------- *)

local
   local
      fun mapCons l (x: {redex: term frag list, residue: term}) =
         List.map (fn s => (x :: s)) l
   in
      fun substCases cs f l = List.concat (List.map (mapCons l) (f cs))
   end

   fun immediate1 f =
      substCases
         [`m` |-> ``immediate_form1 imm32``,
          `m` |-> ``register_form1
                       (r, FST (DecodeImmShift (v2w [b1; b0], imm5)),
                           SND (DecodeImmShift (v2w [b1; b0], imm5)))``] f

   fun immediate2 f =
      substCases [`m` |-> ``immediate_form2 imm32``,
                  `m` |-> ``register_form2 r``] f

   fun immediate3 f =
      substCases
         [`m` |-> ``immediate_form1 imm32``,
          `m` |-> ``register_form1 (r, SRType_LSL, imm2)``] f
in
   val addr =
      [[`idx` |-> ``T``, `wb` |-> ``F``, `a` |-> ``T``],
       [`idx` |-> ``T``, `wb` |-> ``F``, `a` |-> ``F``],
       [`idx` |-> ``F``, `wb` |-> ``T``],
       [`idx` |-> ``T``, `wb` |-> ``T``, `a` |-> ``T``],
       [`idx` |-> ``T``, `wb` |-> ``T``, `a` |-> ``F``]]
   val bpc_addr = List.take (addr, 2)
   val addr1 = immediate1 Lib.I addr
   val addr2 = immediate2 Lib.I addr
   val addr3 = immediate3 Lib.I addr
   val bpc_addr1 = immediate1 List.tl bpc_addr
   val bpc_addr2 = immediate2 List.tl bpc_addr
   val bpc_addr3 = immediate3 List.tl bpc_addr
   val plain_addr1 = immediate1 Lib.I [[`a` |-> ``T``], [`a` |-> ``F``]]
end

(* ---------------------------- *)

val rule_sp =
   utilsLib.MATCH_HYP_RULE
     (PURE_ASM_REWRITE_RULE [boolTheory.OR_CLAUSES] o
      Conv.CONV_RULE (utilsLib.INST_REWRITE_CONV [Aligned_plus_minus]))
     ``a \/ b \/ c : bool``

val rule_pc =
   rule_sp o
   FULL_DATATYPE_RULE o
   utilsLib.ALL_HYP_CONV_RULE
      (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])) o
   Conv.CONV_RULE (utilsLib.INST_REWRITE_CONV [write'R_rwt]) o
   ASM_REWRITE_RULE []

fun rule_npc b =
   (if b then rule_sp else Lib.I) o
   REWRITE_RULE (npc_thm [`t`, `n`]) o
   FULL_DATATYPE_RULE o
   Conv.CONV_RULE (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])) o
   ASM_REWRITE_RULE []

val align_base_pc_rule =
   utilsLib.MATCH_HYP_CONV_RULE
      (utilsLib.INST_REWRITE_CONV
         [Aligned2_base_pc_plus, Aligned2_base_pc_minus,
          Aligned4_base_pc_plus, Aligned4_base_pc_minus])
      ``aligned n (w: word32)``

val rule_base_pc =
   align_base_pc_rule o
   REWRITE_RULE (npc_thm [`t`]) o
   FULL_DATATYPE_RULE o
   Conv.CONV_RULE (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])) o
   DATATYPE_RULE o
   ASM_REWRITE_RULE []

val rule_literal_pc =
   utilsLib.MATCH_HYP_CONV_RULE (REWRITE_CONV [Aligned_Align_plus_minus])
      ``aligned 2 (w: word32)`` o
   ASM_REWRITE_RULE []

val rule_literal =
   utilsLib.MATCH_HYP_CONV_RULE (REWRITE_CONV [Aligned_Align_plus_minus])
      ``aligned n (w: word32)`` o
   utilsLib.INST_REWRITE_RULE [Align4_base_pc_plus, Align4_base_pc_minus] o
   REWRITE_RULE (npc_thm [`t`]) o
   DATATYPE_RULE o
   Conv.CONV_RULE (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])) o
   ASM_REWRITE_RULE []

val rule_npc2 =
   rule_sp o
   utilsLib.ALL_HYP_CONV_RULE
      (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])
       THENC DATATYPE_CONV
       THENC REWRITE_CONV [alignmentTheory.aligned_numeric,
                           alignmentTheory.aligned_add_sub_123]) o
   REWRITE_RULE (npc_thm [`t`, `t2`, `n`]) o
   FULL_DATATYPE_RULE o
   Conv.CONV_RULE (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])) o
   ASM_REWRITE_RULE []

val rule_base_pc2 =
   utilsLib.ALL_HYP_CONV_RULE
      (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])
       THENC DATATYPE_CONV
       THENC REWRITE_CONV [alignmentTheory.aligned_numeric,
                           alignmentTheory.aligned_add_sub_123]
       THENC utilsLib.INST_REWRITE_CONV
                [Aligned4_base_pc_plus, Aligned4_base_pc_minus]) o
   REWRITE_RULE (npc_thm [`t`, `t2`]) o
   FULL_DATATYPE_RULE o
   Conv.CONV_RULE (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])) o
   DATATYPE_RULE o
   ASM_REWRITE_RULE []

val rule_literal2 =
   utilsLib.MATCH_HYP_CONV_RULE (REWRITE_CONV [Aligned_Align_plus_minus])
      ``aligned n (w: word32)`` o
   utilsLib.INST_REWRITE_RULE [Align4_base_pc_plus, Align4_base_pc_minus] o
   utilsLib.ALL_HYP_CONV_RULE
      (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])
       THENC DATATYPE_CONV
       THENC REWRITE_CONV [alignmentTheory.aligned_numeric,
                           alignmentTheory.aligned_add_sub_123]) o
   REWRITE_RULE (npc_thm [`t`, `t2`]) o
   FULL_DATATYPE_RULE o
   Conv.CONV_RULE (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [write'R_rwt])) o
   ASM_REWRITE_RULE []

(* ---------------------------- *)

val LoadWord_pc_rwt =
   List.map (fn wpc =>
      memEV rule_pc MemU_4_rwt [dfn'LoadWord_def, wpc]
        [[``n <> 15w: word4``, ``r <> 15w: word4``]] addr1
        ``dfn'LoadWord (a, idx, wb, 15w, n, m)``
     ) LoadWritePC_rwt
     |> List.concat

val LoadWord_pc_pc_rwt =
   List.map (fn wpc =>
      memEV rule_pc MemU_4_rwt [dfn'LoadWord_def, wpc]
        [[``r <> 15w: word4``]] bpc_addr1
        ``dfn'LoadWord (a, idx, wb, 15w, 15w, m)``
     ) LoadWritePC_rwt
     |> List.concat

val LoadWord_rwt =
   memEV (rule_npc true) MemU_4_rwt [dfn'LoadWord_def]
     [[``t <> 15w: word4``, ``n <> 15w: word4``, ``r <> 15w: word4``]] addr1
     ``dfn'LoadWord (a, idx, wb, t, n, m)``

val LoadWord_base_pc_rwt =
   memEV rule_base_pc MemU_4_rwt [dfn'LoadWord_def, ROR_rwt]
     [[``t <> 15w: word4``, ``r <> 15w: word4``]] bpc_addr1
     ``dfn'LoadWord (a, idx, wb, t, 15w, m)``

(*
val LoadLiteral_pc_rwt =
   memEV (K rule_literal_pc) MemU_4_rwt [dfn'LoadLiteral_def] [] (TF `a`)
     ``dfn'LoadLiteral (a, 15w, imm32)``
*)

val LoadLiteral_rwt =
   memEV rule_literal MemU_4_rwt [dfn'LoadLiteral_def]
     [[``t <> 15w: word4``]] (TF `a`)
     ``dfn'LoadLiteral (a, t, imm32)``

(* ---------------------------- *)

val Extend_rwt =
    List.map (REWRITE_CONV [Extend_def])
         [``Extend (T, w:'a word): 'b word``,
          ``Extend (F, w:'a word): 'b word``]

val LoadByte_rwts =
   memEV (rule_npc false) MemU_1_rwt [dfn'LoadByte_def]
     [[``t <> 15w: word4``, ``n <> 15w: word4``, ``r <> 15w: word4``]] addr1
     ``dfn'LoadByte (u, a, idx, wb, t, n, m)``

val LoadByte_base_pc_rwts =
   memEV rule_base_pc MemU_1_rwt [dfn'LoadByte_def]
     [[``t <> 15w: word4``, ``r <> 15w: word4``]] bpc_addr1
     ``dfn'LoadByte (u, a, idx, wb, t, 15w, m)``

val LoadByteLiteral_rwt =
   memEV rule_literal MemU_1_rwt [dfn'LoadByteLiteral_def]
     [[``t <> 15w: word4``]] (TF `a`)
     ``dfn'LoadByteLiteral (u, a, t, imm32)``

val LoadSignedByte_rwts =
   memEV (rule_npc false) MemU_1_rwt (dfn'LoadByte_def :: Extend_rwt)
     [[``t <> 15w: word4``, ``n <> 15w: word4``, ``r <> 15w: word4``]] addr
     ``dfn'LoadByte
         (F, a, idx, wb, t, n, register_form1 (r, SRType_LSL, imm2))``

val LoadSignedByte_base_pc_rwts =
   memEV rule_base_pc MemU_1_rwt (dfn'LoadByte_def :: Extend_rwt)
     [[``t <> 15w: word4``, ``r <> 15w: word4``]] bpc_addr
     ``dfn'LoadByte
         (F, a, idx, wb, t, 15w, register_form1 (r, SRType_LSL, imm2))``

val LoadByteUnprivileged_rwts =
   memEV (rule_npc false) MemU_unpriv_1_rwt [dfn'LoadByteUnprivileged_def]
     [[``t <> 15w: word4``, ``n <> 15w: word4``, ``r <> 15w: word4``]]
     plain_addr1
     ``dfn'LoadByteUnprivileged (a, T, t, n, m)``

(* ---------------------------- *)

val LoadHalf_rwts =
   memEV (rule_npc false) MemU_2_rwt [dfn'LoadHalf_def]
     [[``t <> 15w: word4``, ``n <> 15w: word4``, ``r <> 15w: word4``]] addr3
     ``dfn'LoadHalf (u, a, idx, wb, t, n, m)``

val LoadHalf_base_pc_rwts =
   memEV rule_base_pc MemU_2_rwt [dfn'LoadHalf_def]
     [[``t <> 15w: word4``, ``r <> 15w: word4``]] bpc_addr3
     ``dfn'LoadHalf (u, a, idx, wb, t, 15w, m)``

val LoadHalfLiteral_rwt =
   memEV rule_literal MemU_2_rwt [dfn'LoadHalfLiteral_def]
     [[``t <> 15w: word4``]] (TF `a`)
     ``dfn'LoadHalfLiteral (u, a, t, imm32)``

(* ---------------------------- *)

val LoadDual_rwt =
   memEV rule_npc2 MemA_4_rwt [dfn'LoadDual_def]
     [[``t <> 15w: word4``, ``t2 <> 15w: word4``,
       ``n <> 15w: word4``, ``r <> 15w: word4``]] addr2
     ``dfn'LoadDual (a, idx, wb, t, t2, n, m)``

val LoadDual_base_pc_rwt =
   memEV rule_base_pc2 MemA_4_rwt [dfn'LoadDual_def]
     [[``t <> 15w: word4``, ``t2 <> 15w: word4``, ``r <> 15w: word4``]]
     bpc_addr2
     ``dfn'LoadDual (a, idx, wb, t, t2, 15w, m)``

val LoadDualLiteral_rwt =
   memEV rule_literal2 MemA_4_rwt [dfn'LoadDualLiteral_def]
     [[``t <> 15w: word4``, ``t2 <> 15w: word4``]] (TF `a`)
     ``dfn'LoadDualLiteral (a, t, t2, imm32)``

(* ---------------------------- *)

val Shift_C_DecodeImmShift_rule =
   REWRITE_RULE [cond_rand_thms, FST_SWAP] o
   utilsLib.ALL_HYP_RULE
      (REWRITE_RULE [cond_rand_thms, FST_SWAP, Shift_C_DecodeImmShift_rwt])

val rule_npc =
   Shift_C_DecodeImmShift_rule o
   rule_sp o
   utilsLib.MATCH_HYP_CONV_RULE
     (utilsLib.INST_REWRITE_CONV [Aligned_plus_minus]) ``a \/ b \/ c : bool``

val rule_npc2 =
   FULL_DATATYPE_RULE o
   utilsLib.ALL_HYP_CONV_RULE
      (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [R_rwt])
       THENC DATATYPE_CONV
       THENC REWRITE_CONV [alignmentTheory.aligned_numeric,
                           alignmentTheory.aligned_add_sub_123]) o
   rule_sp o
   utilsLib.MATCH_HYP_CONV_RULE
      (utilsLib.INST_REWRITE_CONV [Aligned_plus_minus]) ``a \/ b \/ c : bool`` o
   FULL_DATATYPE_RULE o
   Conv.CONV_RULE (Conv.DEPTH_CONV (utilsLib.INST_REWRITE_CONV [R_rwt]))

(* ---------------------------- *)

val () = resetEvConv ()

val StoreWord_rwt =
   storeEV rule_npc
     write'MemU_4_rwt [dfn'StoreWord_def]
     [[``Aligned (^st.REG (R_mode ^st.CPSR.M n), 4)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) +
              FST (FST (Shift_C (^st.REG (R_mode ^st.CPSR.M r),
                                 FST (DecodeImmShift (v2w [b1; b0],imm5)),
                                 SND (DecodeImmShift (v2w [b1; b0],imm5)),
                                 ^st.CPSR.C) s)), 4)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) -
              FST (FST (Shift_C (^st.REG (R_mode ^st.CPSR.M r),
                                 FST (DecodeImmShift (v2w [b1; b0],imm5)),
                                 SND (DecodeImmShift (v2w [b1; b0],imm5)),
                                 ^st.CPSR.C) s)), 4)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) + imm32, 4)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) - imm32, 4)``,
       ``n <> 15w: word4``, ``r <> 15w: word4``]] addr1
     ``dfn'StoreWord (a, idx, wb, t, n, m)``

val StoreWord_base_pc_rwt =
   storeEV (align_base_pc_rule o Shift_C_DecodeImmShift_rule)
     write'MemU_4_rwt [dfn'StoreWord_def]
     [[``Aligned (^st.REG RName_PC + (if ^st.CPSR.T then 4w else 8w) +
              FST (FST (Shift_C (^st.REG (R_mode ^st.CPSR.M r),
                                 FST (DecodeImmShift (v2w [b1; b0],imm5)),
                                 SND (DecodeImmShift (v2w [b1; b0],imm5)),
                                 ^st.CPSR.C) s)), 4)``,
       ``Aligned
              (^st.REG RName_PC + (if ^st.CPSR.T then 4w else 8w) + imm32, 4)``,
       ``Aligned (^st.REG RName_PC + (if ^st.CPSR.T then 4w else 8w) -
              FST (FST (Shift_C (^st.REG (R_mode ^st.CPSR.M r),
                                 FST (DecodeImmShift (v2w [b1; b0],imm5)),
                                 SND (DecodeImmShift (v2w [b1; b0],imm5)),
                                 ^st.CPSR.C) s)), 4)``,
       ``Aligned
             (^st.REG RName_PC + (if ^st.CPSR.T then 4w else 8w) - imm32, 4)``,
       ``r <> 15w: word4``]] bpc_addr1
     ``dfn'StoreWord (a, idx, wb, t, 15w, m)``

(* ---------------------------- *)

val StoreByte_rwt =
   storeEV Lib.I write'MemU_1_rwt
     [dfn'StoreByte_def, Shift_C_DecodeImmShift_rwt]
     [[``n <> 15w: word4``, ``r <> 15w: word4``]] addr1
     ``dfn'StoreByte (a, idx, wb, t, n, m)``

val StoreByte_base_pc_rwt =
   storeEV Lib.I write'MemU_1_rwt
     [dfn'StoreByte_def, Shift_C_DecodeImmShift_rwt]
     [[``r <> 15w: word4``]] bpc_addr1
     ``dfn'StoreByte (a, idx, wb, t, 15w, m)``

(* ---------------------------- *)

val extract_rwt =
   List.map utilsLib.EXTRACT_CONV [
     ``(15 >< 8) ((15 >< 0) (w: word32) : word16) : word8``,
     ``(7 >< 0) ((15 >< 0) (w: word32) : word16) : word8``
   ] |> Drule.LIST_CONJ

val StoreHalf_rwt =
   storeEV Shift_C_DecodeImmShift_rule
     write'MemU_2_rwt [dfn'StoreHalf_def, extract_rwt]
     [[``Aligned (^st.REG (R_mode ^st.CPSR.M n),2)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) +
                  ^st.REG (R_mode ^st.CPSR.M r) << imm2, 2)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) -
                  ^st.REG (R_mode ^st.CPSR.M r) << imm2, 2)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) + imm32, 2)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) - imm32, 2)``,
       ``n <> 15w: word4``, ``r <> 15w: word4``]] addr3
     ``dfn'StoreHalf (a, idx, wb, t, n, m)``

val StoreHalf_base_pc_rwt =
   storeEV align_base_pc_rule
     write'MemU_2_rwt [dfn'StoreHalf_def, extract_rwt]
     [[``Aligned (^st.REG RName_PC + (if ^st.CPSR.T then 4w else 8w) +
                  ^st.REG (R_mode ^st.CPSR.M r) << imm2, 2)``,
       ``Aligned
           (^st.REG RName_PC + (if ^st.CPSR.T then 4w else 8w) + imm32, 2)``,
       ``Aligned (^st.REG RName_PC + (if ^st.CPSR.T then 4w else 8w) -
                  ^st.REG (R_mode ^st.CPSR.M r) << imm2, 2)``,
       ``Aligned
          (^st.REG RName_PC + (if ^st.CPSR.T then 4w else 8w) - imm32, 2)``,
       ``r <> 15w: word4``]] bpc_addr3
     ``dfn'StoreHalf (a, idx, wb, t, 15w, m)``

(* ---------------------------- *)

val StoreDual_rwt =
   storeEV rule_npc2
     write'MemA_4_rwt [dfn'StoreDual_def, alignmentTheory.aligned_add_sub_123]
     [[``Aligned (^st.REG (R_mode ^st.CPSR.M n), 4)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) +
            FST (FST (Shift_C (^st.REG (R_mode ^st.CPSR.M r),
                               FST (DecodeImmShift (v2w [b1; b0],imm5)),
                               SND (DecodeImmShift (v2w [b1; b0],imm5)),
                               ^st.CPSR.C) s)), 4)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) -
            FST (FST (Shift_C (^st.REG (R_mode ^st.CPSR.M r),
                               FST (DecodeImmShift (v2w [b1; b0],imm5)),
                               SND (DecodeImmShift (v2w [b1; b0],imm5)),
                               ^st.CPSR.C) s)), 4)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) + imm32, 4)``,
       ``Aligned (^st.REG (R_mode ^st.CPSR.M n) - imm32, 4)``,
       ``t <> 15w: word4``, ``t2 <> 15w: word4``,
       ``n <> 15w: word4``, ``r <> 15w: word4``]] addr2
     ``dfn'StoreDual (a, idx, wb, t, t2, n, m)``

(* ---------------------------- *)

val Swap_rwts =
   EV ([R_rwt, write'R_rwt, Q.INST [`d` |-> `t`] arm_stepTheory.R_x_not_pc,
       dfn'Swap_def, IncPC_rwt, ROR_rwt,
       EVAL ``(a: word32) #>> (8 * w2n (0w: word2))``] @
       MemA_1_rwt @ write'MemA_1_rwt @ MemA_4_rwt @ write'MemA_4_rwt)
      [[``^st.Encoding = Encoding_ARM``, ``~^st.CPSR.T``,
        ``t <> 15w: word4``, ``t2 <> 15w: word4``, ``n <> 15w: word4``]]
      (TF `b`)
      ``dfn'Swap (b, t, t2, n)``
    |> List.map
          (utilsLib.ALL_HYP_RULE
             (PURE_ASM_REWRITE_RULE
                [boolTheory.COND_CLAUSES, boolTheory.NOT_CLAUSES,
                 boolTheory.OR_CLAUSES]) o
           utilsLib.ALL_HYP_CONV_RULE
             (DATATYPE_CONV
              THENC REWRITE_CONV [boolTheory.COND_ID]
              THENC utilsLib.INST_REWRITE_CONV (MemA_1_rwt @ MemA_4_rwt)
              THENC DATATYPE_CONV))
    |> addThms

(* ---------------------------- *)

(* Floating-point *)

val fpscr_thm = Q.prove(
  `FPSCR a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
         a17 a18 a19 a20 a21 =
   ^st.FP.FPSCR with
   <|AHP := a0; C := a1; DN := a2; DZC := a3; DZE := a4;
     FZ := a5; IDC := a6; IDE := a7; IOC := a8; IOE := a9;
     IXC := a10; IXE := a11; N := a12; OFC := a13; OFE := a14;
     QC := a15; RMode := a16; UFC := a17; UFE := a18; V := a19; Z := a20;
     fpscr'rst := a21|>`,
   simp [FPSCR_component_equality])

val mov_two_singles =
  List.map (blastLib.BBLAST_PROVE o Term)
    [`(v2w [b9; b8; b7; b6; F] + 1w) // 2w = v2w [F; b9; b8; b7; b6] : word5`,
     `word_bit 0 (v2w [b9; b8; b7; b6; F] + 1w : word5)`,
     `~word_bit 0 (v2w [b9; b8; b7; b6; T] + 1w : word5)`,
     `v2w [F; b9; b8; b7; b6] <> (v2w [b9; b8; b7; b6; T] + 1w) // 2w : word5`,
     `bit_field_insert 63 32 (a : word32)
        (bit_field_insert 31 0 (b : word32) (c : word64)) = a @@ b`]
  |> Drule.LIST_CONJ

val UnsignedSatQ_32_rwt =
  EV [UnsignedSatQ_def, wordsTheory.word_len_def, wordsTheory.dimindex_32,
      EVAL ``i2w 4294967295 : word32``] [] []
    ``UnsignedSatQ (i, 32) : arm_state -> (word32 # bool) # arm_state``
    |> hd

val SignedSatQ_32_rwt =
  EV [SignedSatQ_def, wordsTheory.word_len_def, wordsTheory.dimindex_32,
      EVAL ``2147483648i - 1i``, EVAL ``i2w 2147483647i : word32``,
      EVAL ``i2w (-2147483648i) : word32``] [] []
    ``SignedSatQ (i, 32) : arm_state -> (word32 # bool) # arm_state``
    |> hd

val ev =
  EV [FPToFixed32_def, FPToFixed64_def, RoundingMode,
      UnsignedSatQ_32_rwt, SignedSatQ_32_rwt, SatQ_def,
      intLib.ARITH_PROVE ``i > 4294967295i = ~(i <= 4294967295i)``,
      intLib.ARITH_PROVE ``i > 2147483647i = ~(i <= 2147483647i)``,
      intLib.ARITH_PROVE ``i < -2147483648i = ~(-2147483648i <= i)``,
      intLib.ARITH_PROVE ``i < 0i = ~(0i <= i)``
     ]
     [[``fp32_to_int
           (if round_towards_zero then roundTowardZero
            else DecodeRoundingMode s.FP.FPSCR.RMode) operand = SOME i``,
       ``fp64_to_int
           (if round_towards_zero then roundTowardZero
            else DecodeRoundingMode s.FP.FPSCR.RMode) operand = SOME i``,
       ``0i <= i``, ``i <= 4294967295i``,
       ``-2147483648i <= i``, ``i <= 2147483647i``]]
     (TF `unsigned`)

val (FPToFixed32_unsigned_rwt, FPToFixed32_signed_rwt) =
  ev ``FPToFixed32 (operand,unsigned,round_towards_zero)``
  |> Lib.pair_of_list

val (FPToFixed64_unsigned_rwt, FPToFixed64_signed_rwt) =
  ev ``FPToFixed64 (operand,unsigned,round_towards_zero)``
  |> Lib.pair_of_list

val rule = utilsLib.INST_REWRITE_RULE
              [arm_stepTheory.Align4_base_pc_plus,
               arm_stepTheory.Align4_base_pc_minus] o
           SIMP_RULE std_ss [] o
           REWRITE_RULE
             [GSYM arm_stepTheory.UpdateSingleOfDouble_def,
              GSYM arm_stepTheory.SingleOfDouble_def] o
           SIMP_RULE (pure_ss++wordsLib.SIZES_ss)
              [wordsTheory.WORD_EXTRACT_COMP_THM] o
           COND_UPDATE_RULE

fun fpMemEV c tm =
   EV ([dfn'vldr_def, dfn'vstr_def, R_rwt, IncPC_rwt, PC_rwt, fpreg_div2,
        write'S_def, write'D_def, S_def, D_def, BigEndian_def] @
        MemA_4_rwt @ write'MemA_4_rwt) c
     [[`single_reg` |-> boolSyntax.F, `add` |-> boolSyntax.F],
      [`single_reg` |-> boolSyntax.F, `add` |-> boolSyntax.T],
      [`single_reg` |-> boolSyntax.T, `add` |-> boolSyntax.F],
      [`single_reg` |-> boolSyntax.T, `add` |-> boolSyntax.T]]
     tm
    |> List.map (utilsLib.ALL_HYP_CONV_RULE
                   (DATATYPE_CONV
                    THENC REWRITE_CONV
                            [arm_stepTheory.Aligned_Align_plus_minus,
                             alignmentTheory.aligned_add_sub_123,
                             alignmentTheory.aligned_numeric]) o rule)

fun fpEV c tm =
   EV [dfn'vadd_def, dfn'vsub_def, dfn'vmul_def, dfn'vneg_mul_def,
       dfn'vmla_vmls_def, dfn'vfma_vfms_def, dfn'vfnma_vfnms_def,
       dfn'vdiv_def, dfn'vabs_def, dfn'vneg_def, dfn'vsqrt_def,
       dfn'vmov_imm_def, dfn'vmov_def, dfn'vmov_single_def,
       dfn'vmov_two_singles_def, dfn'vmov_double_def, dfn'vcmp_def,
       dfn'vcvt_float_def, dfn'vcvt_to_integer_def, dfn'vcvt_from_integer_def,
       IncPC_rwt, S_def, D_def, write'S_def, write'D_def,
       FPAdd64_def, FPAdd32_def, FPSub64_def, FPSub32_def, fpreg_div2,
       FPMul64_def, FPMul32_def, FPZero64_def, FPZero32_def,
       FixedToFP32_def, FixedToFP64_def,
       FPToFixed32_signed_rwt, FPToFixed32_unsigned_rwt,
       FPToFixed64_signed_rwt, FPToFixed64_unsigned_rwt,
       R_rwt, write'R_rwt, arm_stepTheory.R_x_not_pc,
       write'reg'FPSCR_def, fpscr_nzcv,
       arm_stepTheory.RoundingMode, arm_stepTheory.get_vfp_imm32,
       wordsTheory.word_concat_0_0, mov_two_singles, updateTheory.UPDATE_EQ]
      [[``^st.Encoding = Encoding_ARM``, ``~^st.CPSR.T``]] c tm
   |> List.map rule

val mk_fpreg = bitstringSyntax.mk_vec 5
val () = setEvConv (Conv.DEPTH_CONV bitstringLib.word_bit_CONV)

val vmov_rwt =
   fpEV (TF `single`)
      ``dfn'vmov (single, ^(mk_fpreg 0), ^(mk_fpreg 5))``
   |> addThms

val vmov_imm_rwt =
   fpEV [[`single` |-> boolSyntax.F],
         [`single` |-> boolSyntax.T,
          `imm64` |-> bitstringSyntax.mk_v2w
                        (bitstringSyntax.mk_bstring 32 5, ``:64``)]]
      ``dfn'vmov_imm (single, ^(mk_fpreg 0), imm64)``
   |> addThms

val vmov_single_rwt =
   fpEV (TF `to_arm_register`)
      ``dfn'vmov_single (to_arm_register, t, ^(mk_fpreg 5))``
   |> addThms

val vmov_two_singles_rwt =
   fpEV [[`to_arm_registers` |-> boolSyntax.F, `b5` |->  boolSyntax.F],
         [`to_arm_registers` |-> boolSyntax.T, `b5` |->  boolSyntax.F],
         [`to_arm_registers` |-> boolSyntax.F, `b5` |->  boolSyntax.T],
         [`to_arm_registers` |-> boolSyntax.T, `b5` |->  boolSyntax.T]]
      ``dfn'vmov_two_singles (to_arm_registers, t, t2, ^(mk_fpreg 5))``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE
                  (DATATYPE_CONV THENC REWRITE_CONV [ASSUME ``~^st.CPSR.T``]) o
                DATATYPE_RULE)
   |> addThms

val vmov_double_rwt =
   fpEV (TF `to_arm_registers`)
      ``dfn'vmov_double (to_arm_registers, t, t2, ^(mk_fpreg 5))``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE
                  (DATATYPE_CONV THENC REWRITE_CONV [ASSUME ``~^st.CPSR.T``]))
   |> addThms

val vcmp_rwt =
   fpEV [[`dp` |-> boolSyntax.F, `m_w_z` |-> ``NONE:word5 option``],
         [`dp` |-> boolSyntax.T, `m_w_z` |-> ``NONE:word5 option``],
         [`dp` |-> boolSyntax.F, `m_w_z` |-> ``SOME (^(mk_fpreg 5))``],
         [`dp` |-> boolSyntax.T, `m_w_z` |-> ``SOME (^(mk_fpreg 5))``]]
      ``dfn'vcmp (dp, ^(mk_fpreg 0), m_w_z)``
   |> addThms

val vmrs_rwt =
   EV [dfn'vmrs_def, IncPC_rwt, R_rwt, write'R_rwt, reg_fpscr]
      [[``t <> 15w: word4``]] []
      ``dfn'vmrs t``
   |> List.map (utilsLib.MATCH_HYP_CONV_RULE
                   (REWRITE_CONV [ASSUME ``~^st.CPSR.T``])
                   ``a \/ b \/ c : bool``)
   |> addThms

val vmrs15_rwt =
   EV [dfn'vmrs_def, IncPC_rwt] [] []
      ``dfn'vmrs 15w``
      |> addThms

val vmsr_rwt =
   EV [dfn'vmsr_def, IncPC_rwt, R_rwt, write'reg'FPSCR_def,
       REWRITE_RULE [fpscr_thm] rec'FPSCR_def] [[``~^st.CPSR.T``]] []
      ``dfn'vmsr t``
      |> addThms

val vabs_rwt =
   fpEV (TF `dp`)
      ``dfn'vabs (dp, ^(mk_fpreg 0), ^(mk_fpreg 5))``
   |> addThms

val vneg_rwt =
   fpEV (TF `dp`)
      ``dfn'vneg (dp, ^(mk_fpreg 0), ^(mk_fpreg 5))``
   |> addThms

val vsqrt_rwt =
   fpEV (TF `dp`)
      ``dfn'vsqrt (dp, ^(mk_fpreg 0), ^(mk_fpreg 5))``
   |> addThms

val vadd_rwt =
   fpEV (TF `dp`)
      ``dfn'vadd (dp, ^(mk_fpreg 0), ^(mk_fpreg 5), ^(mk_fpreg 10))``
   |> addThms

val vsub_rwt =
   fpEV (TF `dp`)
      ``dfn'vsub (dp, ^(mk_fpreg 0), ^(mk_fpreg 5), ^(mk_fpreg 10))``
   |> addThms

val vmul_rwt =
   fpEV (TF `dp`)
       ``dfn'vmul (dp, ^(mk_fpreg 0), ^(mk_fpreg 5), ^(mk_fpreg 10))``
   |> addThms

val vdiv_rwt =
   fpEV (TF `dp`)
       ``dfn'vdiv (dp, ^(mk_fpreg 0), ^(mk_fpreg 5), ^(mk_fpreg 10))``
   |> addThms

val vfma_vfms_rwt =
   fpEV (TF `dp`)
       ``dfn'vfma_vfms (dp, add, ^(mk_fpreg 0), ^(mk_fpreg 5), ^(mk_fpreg 10))``
   |> addThms

val vfnma_vfnms_rwt =
   fpEV (TF `dp`)
     ``dfn'vfnma_vfnms (dp, add, ^(mk_fpreg 0), ^(mk_fpreg 5), ^(mk_fpreg 10))``
   |> addThms

val vmla_mls_rwt =
   fpEV [[`dp` |-> boolSyntax.F, `add` |-> boolSyntax.F],
         [`dp` |-> boolSyntax.F, `add` |-> boolSyntax.T],
         [`dp` |-> boolSyntax.T, `add` |-> boolSyntax.F],
         [`dp` |-> boolSyntax.T, `add` |-> boolSyntax.T]]
       ``dfn'vmla_vmls (dp, add, ^(mk_fpreg 0), ^(mk_fpreg 5), ^(mk_fpreg 10))``
   |> addThms

val vneg_mul_rwt =
   fpEV [[`dp` |-> boolSyntax.T, `typ` |-> ``VFPNegMul_VNMLA``],
         [`dp` |-> boolSyntax.F, `typ` |-> ``VFPNegMul_VNMLA``],
         [`dp` |-> boolSyntax.T, `typ` |-> ``VFPNegMul_VNMLS``],
         [`dp` |-> boolSyntax.F, `typ` |-> ``VFPNegMul_VNMLS``],
         [`dp` |-> boolSyntax.T, `typ` |-> ``VFPNegMul_VNMUL``],
         [`dp` |-> boolSyntax.F, `typ` |-> ``VFPNegMul_VNMUL``]]
      ``dfn'vneg_mul (dp, typ, ^(mk_fpreg 0), ^(mk_fpreg 5), ^(mk_fpreg 10))``
   |> addThms

val vcvt_float_rwt =
   fpEV [[`double_to_single` |-> boolSyntax.F, `b4` |-> boolSyntax.F],
         [`double_to_single` |-> boolSyntax.F, `b4` |-> boolSyntax.T],
         [`double_to_single` |-> boolSyntax.T]]
       ``dfn'vcvt_float (double_to_single, ^(mk_fpreg 0), ^(mk_fpreg 5))``
   |> addThms

val vcvt_from_integer_rwt =
   fpEV [[`dp` |-> boolSyntax.T, `b4` |-> boolSyntax.F],
         [`dp` |-> boolSyntax.T, `b4` |-> boolSyntax.T],
         [`dp` |-> boolSyntax.F]]
       ``dfn'vcvt_from_integer (dp, unsigned, ^(mk_fpreg 0), ^(mk_fpreg 5))``
   |> addThms

val vcvt_to_integer_rwt =
   fpEV [[`dp` |-> boolSyntax.F, `unsigned` |-> boolSyntax.F],
         [`dp` |-> boolSyntax.F, `unsigned` |-> boolSyntax.T],
         [`dp` |-> boolSyntax.T, `unsigned` |-> boolSyntax.F],
         [`dp` |-> boolSyntax.T, `unsigned` |-> boolSyntax.T]]
       ``dfn'vcvt_to_integer
           (dp, unsigned, round_zero, ^(mk_fpreg 0), ^(mk_fpreg 5))``
   |> addThms

val vldr_pc_rwt =
   fpMemEV [] ``dfn'vldr (single_reg, add, ^(mk_fpreg 0), 15w, imm32)``
   |> addThms

val vldr_npc_rwt =
   fpMemEV [[``n <> 15w: word4``]]
      ``dfn'vldr (single_reg, add, ^(mk_fpreg 0), n, imm32)``
   |> addThms

val vstr_pc_rwt =
   fpMemEV [] ``dfn'vstr (single_reg, add, ^(mk_fpreg 0), 15w, imm32)``
   |> addThms

val vstr_npc_rwt =
   fpMemEV [[``n <> 15w: word4``]]
      ``dfn'vstr (single_reg, add, ^(mk_fpreg 0), n, imm32)``
   |> addThms

val () = resetEvConv ()

(* ---------------------------- *)

val COND_B_CONV = Conv.RATOR_CONV o Conv.RATOR_CONV o Conv.RAND_CONV
val COND_T_CONV = Conv.RATOR_CONV o Conv.RAND_CONV
val COND_E_CONV = Conv.RAND_CONV

fun COND_UPDATE2_CONV l =
   COND_UPDATE_CONV
   THENC DATATYPE_CONV
   THENC COND_UPDATE_CONV
   THENC SIMP_CONV (srw_ss()) l

val PSR_CONV = utilsLib.BIT_FIELD_INSERT_CONV "arm" "PSR"
val PSR_TAC = utilsLib.REC_REG_BIT_FIELD_INSERT_TAC "arm" "PSR"

val PSR_FIELDS = Q.prove(
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

val PSR_FLAGS = Q.prove(
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

val IT_extract =
   utilsLib.map_conv utilsLib.EXTRACT_CONV
      [``(2 >< 1) ((26 >< 24) (v: word32) : word3) : word2``,
       ``w2w ((15 >< 10) (w: word32) : word6) : word8``,
       ``w2w ((26 >< 25) (w: word32) : word2) : word8``]

val IT_concat = Q.prove(
   `(!v: word6 w: word8.
       bit_field_insert 7 2 v w = w2w v << 2 || (w && 0b11w)) /\
    (!v: word2 w: word8.
       bit_field_insert 1 0 v w = w2w v || (w && 0b11111100w)) /\
    (!v1: word6 v2: word2 w: word8.
      bit_field_insert 7 2 v1 (bit_field_insert 1 0 v2 w) = v1 @@ v2)`,
   REPEAT strip_tac
   \\ rewrite_tac [wordsTheory.bit_field_insert_def]
   \\ blastLib.BBLAST_TAC)

val insert_mode = Q.prove(
   `!w: word32.
       bit_field_insert 4 0 ((4 >< 0) w : word5) (v: word5) = (4 >< 0) w`,
   blastLib.BBLAST_TAC)

val CPSRWriteByInstr =
   CPSRWriteByInstr_def
   |> Q.SPECL [`value`, `bytemask`, `is_exc_return`]
   |> (fn th => Thm.AP_THM th st)
   |> Conv.RIGHT_CONV_RULE
         (Thm.BETA_CONV
          THENC REWRITE_CONV
                  [write'reg'PSR_def, CurrentModeIsNotUser_def,
                   PSR_FIELDS, PSR_FLAGS]
          THENC Conv.RAND_CONV
                   (Thm.BETA_CONV
                    THENC PairedLambda.let_CONV
                    THENC utilsLib.INST_REWRITE_CONV [BadMode]
                    THENC REWRITE_CONV []
                   )
          THENC PairedLambda.let_CONV
          THENC REWRITE_CONV []
          THENC Conv.RAND_CONV
                   (COND_T_CONV PairedLambda.let_CONV
                    THENC PSR_CONV
                   )
          THENC PairedLambda.let_CONV
          THENC Conv.RAND_CONV
                   (PSR_CONV
                    THENC COND_UPDATE2_CONV [IT_extract]
                   )
          THENC PairedLambda.let_CONV
          THENC Conv.RAND_CONV
                   (PSR_CONV
                    THENC COND_T_CONV
                             (PairedLambda.let_CONV
                              THENC RAND_CONV DATATYPE_CONV
                              THENC PairedLambda.let_CONV
                              THENC DATATYPE_CONV
                              THENC utilsLib.INST_REWRITE_CONV [IsSecure]
                              THENC SIMP_CONV (srw_ss()) [PSR_FLAGS]
                              )
                    THENC COND_UPDATE2_CONV
                             [addressTheory.IF_IF,
                              Q.SPEC `bytemask ' 3` CONJ_COMM]
                   )
          THENC PairedLambda.let_CONV
          THENC COND_T_CONV
                   (Conv.RAND_CONV
                      (REWRITE_CONV [PSR_FLAGS]
                       THENC COND_UPDATE2_CONV [])
                    THENC PairedLambda.let_CONV
                    THENC DATATYPE_CONV
                    THENC utilsLib.INST_REWRITE_CONV [IsSecure]
                    THENC REWRITE_CONV []
                    THENC Conv.RAND_CONV
                             (DATATYPE_CONV
                              THENC REWRITE_CONV [PSR_FLAGS]
                              THENC COND_UPDATE2_CONV []
                             )
                    THENC PairedLambda.let_CONV
                    THENC Conv.RAND_CONV (COND_UPDATE2_CONV [])
                    THENC PairedLambda.let_CONV)
          THENC REWRITE_CONV [PSR_FIELDS, addressTheory.IF_IF, IT_extract]
          THENC Conv.DEPTH_CONV (wordsLib.WORD_BIT_INDEX_CONV true))
   |> utilsLib.ALL_HYP_CONV_RULE
        (DATATYPE_CONV THENC REWRITE_CONV [boolTheory.COND_ID])

val CPSRWriteByInstr_no_control =
   REWRITE_RULE [ASSUME ``~((bytemask: word4) ' 0)``] CPSRWriteByInstr

val CPSRWriteByInstr_control_usr =
   REWRITE_RULE [ASSUME ``(bytemask: word4) ' 0``,
                 ASSUME ``^st.CPSR.M = 16w``] CPSRWriteByInstr

val CPSRWriteByInstr_control_not_usr =
   CPSRWriteByInstr
   |> Conv.RIGHT_CONV_RULE
        (REWRITE_CONV [ASSUME ``(bytemask: word4) ' 0``,
                       ASSUME ``^st.CPSR.M <> 16w``]
         THENC utilsLib.INST_REWRITE_CONV [BadMode]
         THENC REWRITE_CONV []
         THENC utilsLib.INST_REWRITE_CONV [IsSecure]
         THENC REWRITE_CONV []
         THENC Conv.RAND_CONV PairedLambda.let_CONV
         THENC PairedLambda.let_CONV
         THENC REWRITE_CONV []
         THENC PairedLambda.let_CONV
         THENC utilsLib.INST_REWRITE_CONV [IsSecure]
         THENC REWRITE_CONV []
         THENC Conv.RAND_CONV PairedLambda.let_CONV
         THENC PairedLambda.let_CONV
         THENC RAND_CONV DATATYPE_CONV
         THENC utilsLib.INST_REWRITE_CONV [NotHyp]
         THENC REWRITE_CONV []
         THENC PairedLambda.let_CONV
         THENC utilsLib.INST_REWRITE_CONV [NotHyp]
         THENC REWRITE_CONV []
         THENC PairedLambda.let_CONV
         THENC DATATYPE_CONV
         THENC REWRITE_CONV [PSR_FIELDS])
   |> utilsLib.ALL_HYP_CONV_RULE DATATYPE_CONV

val CPSRWriteByInstr_exn_return =
   CPSRWriteByInstr_control_not_usr
   |> Q.INST [`bytemask` |-> `0b1111w`, `is_exc_return` |-> `T`]
   |> Conv.CONV_RULE (Conv.RHS_CONV utilsLib.WGROUND_CONV
                      THENC REWRITE_CONV [IT_concat, insert_mode])
   |> utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV [EVAL ``15w: word4 ' 0``])

(* Partial support for PSR updates, e.g. RFE, MRS, MSR) *)

fun rule tm = REWRITE_RULE [] o utilsLib.INST_REWRITE_RULE [ASSUME tm]
val tm = bitstringSyntax.mk_vec 4 0
val thms =
   List.tabulate
     (4, fn i => EVAL (fcpSyntax.mk_fcp_index (tm, numLib.term_of_int i)))

fun is_j tm =
   case Lib.total fcpSyntax.dest_fcp_index tm of
      SOME (_, i) => i = numLib.term_of_int 24
    | NONE => false

fun unset_j_conv tm =
   let
      val t = HolKernel.find_term is_j tm
   in
      PURE_REWRITE_CONV [ASSUME (boolSyntax.mk_neg t)] tm
   end

val ReturnFromException_le_rwts =
   EV [dfn'ReturnFromException_def, CurrentModeIsHyp,
       CurrentModeIsNotUser_def, BadMode, pairTheory.FST, CurrentInstrSet_rwt,
       CPSRWriteByInstr_exn_return, NotHyp, List.last BranchWritePC_rwt,
       rule ``~^st.CPSR.E`` (hd MemA_4_rwt),
       rule ``n <> 15w: word4`` R_rwt, write'R_rwt,
       arm_stepTheory.Align_LoadWritePC,
       wordsTheory.WORD_SUB_ADD, wordsTheory.WORD_ADD_SUB,
       simpLib.SIMP_PROVE (srw_ss()) []
          ``(!w: word32. w + 4w + 4w = w + 8w) /\
            (!w: word32. w - 8w + 4w = w - 4w)``]
      [[``^st.CPSR.M <> 16w``]]
      [[`inc` |-> ``F``, `wordhigher` |-> ``F``, `wback` |-> ``T``],
       [`inc` |-> ``F``, `wordhigher` |-> ``T``, `wback` |-> ``T``],
       [`inc` |-> ``T``, `wordhigher` |-> ``F``, `wback` |-> ``T``],
       [`inc` |-> ``T``, `wordhigher` |-> ``T``, `wback` |-> ``T``],
       [`inc` |-> ``F``, `wordhigher` |-> ``F``, `wback` |-> ``F``],
       [`inc` |-> ``F``, `wordhigher` |-> ``T``, `wback` |-> ``F``],
       [`inc` |-> ``T``, `wordhigher` |-> ``F``, `wback` |-> ``F``],
       [`inc` |-> ``T``, `wordhigher` |-> ``T``, `wback` |-> ``F``]]
      ``dfn'ReturnFromException (inc, wordhigher, wback, n)``
   |> List.map (Conv.CONV_RULE unset_j_conv o
                utilsLib.ALL_HYP_CONV_RULE
                  (DATATYPE_CONV
                   THENC REWRITE_CONV
                            [alignmentTheory.aligned_add_sub_123,
                             alignmentTheory.aligned_numeric,
                             ASSUME ``^st.CPSR.M <> 16w``]))
   |> addThms

val MoveToRegisterFromSpecial_cpsr_rwts =
   EV [dfn'MoveToRegisterFromSpecial_def, write'R_rwt,
       arm_stepTheory.R_x_not_pc, utilsLib.mk_reg_thm "arm" "PSR",
       CurrentModeIsUserOrSystem_def, BadMode, IncPC_rwt] [] []
      ``dfn'MoveToRegisterFromSpecial (F, d)``
   |> addThms

fun MoveToSpecialFromImmediate_cpsr_rwts thm c =
   EV ([dfn'MoveToSpecialFromImmediate_def, CurrentInstrSet_rwt, IncPC_rwt] @
       thm :: thms) [] c
      ``dfn'MoveToSpecialFromImmediate (F, imm, ^tm)``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE
                  (DATATYPE_CONV THENC REWRITE_CONV thms))
   |> addThms

val MoveToSpecialFromImmediate_cpsr_no_control_rwts =
   MoveToSpecialFromImmediate_cpsr_rwts CPSRWriteByInstr_no_control
      [[`b0` |-> ``F``]]

val MoveToSpecialFromImmediate_cpsr_control_usr_rwts =
   MoveToSpecialFromImmediate_cpsr_rwts CPSRWriteByInstr_control_usr
      [[`b0` |-> ``T``]]

fun MoveToSpecialFromRegister_cpsr_rwts thm c =
   EV ([dfn'MoveToSpecialFromRegister_def, CurrentInstrSet_rwt, R_rwt,
        IncPC_rwt] @ thm :: thms)
      [[``n <> 15w: word4``]] c
      ``dfn'MoveToSpecialFromRegister (F, n, ^tm)``
   |> List.map (utilsLib.ALL_HYP_CONV_RULE
                  (DATATYPE_CONV THENC REWRITE_CONV thms THENC DATATYPE_CONV))
   |> addThms

val MoveToSpecialFromRegister_cpsr_no_control_rwts =
   MoveToSpecialFromRegister_cpsr_rwts CPSRWriteByInstr_no_control
      [[`b0` |-> ``F``]]

val MoveToSpecialFromRegister_cpsr_control_usr_rwts =
   MoveToSpecialFromRegister_cpsr_rwts CPSRWriteByInstr_control_usr
      [[`b0` |-> ``T``]]

(* ========================================================================= *)

(* Evaluator *)

local
   val lsl_0 = hd (Drule.CONJUNCTS wordsTheory.SHIFT_ZERO)
   val word_bit_15 = List.last word_bit_16_thms
   val both_rwts = [lsl_0, v2w_13_15_rwts, word_bit_15]
   val hyps_rwts = both_rwts
   val conc_rwts = [LDM_UPTO_RUN, STM_UPTO_RUN,
                    Align_branch_immediate, Align_branch_exchange_immediate] @
                   Extend_rwt @ both_rwts
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
   fun eval enc tms =
      let
         val net = utilsLib.mk_rw_net utilsLib.lhsc (getThms enc tms)
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
   val get_pair = pairSyntax.dest_pair o rhsc
   val get_val = fst o get_pair
   val get_state = snd o get_pair
   val state_exception_tm = mk_arm_const "arm_state_exception"
   val state_encoding_tm = mk_arm_const "arm_state_Encoding"
   fun mk_proj_exception r = Term.mk_comb (state_exception_tm, r)
   fun mk_proj_encoding r = Term.mk_comb (state_encoding_tm, r)
   fun mk_state e c = Term.subst [state_with_pre (c, e)]
   fun get_cond l =
      let
         val cond = List.take (fst (listSyntax.dest_list l), 4)
      in
         listSyntax.mk_list (cond, Type.bool)
      end
   val enc = mk_arm_const "Encoding_ARM"
   fun set_cond thm1 =
      thm1 |> get_val
           |> Term.rand
           |> bitstringSyntax.dest_v2w |> fst
           |> get_cond
           |> bitstringSyntax.num_of_term
           |> Arbnum.toInt
           |> (fn i => wordsSyntax.mk_wordii (if i = 15 then 14 else i, 4))
           |> mk_state enc
   val default_tms = List.map fix_datatype
                        [``~^st.CPSR.T``, ``^st.Encoding = Encoding_ARM``]
   val MP_Next  = Drule.MATCH_MP arm_stepTheory.NextStateARM_arm
   val MP_Next0 = Drule.MATCH_MP arm_stepTheory.NextStateARM_arm0
   val Run_CONV = utilsLib.Run_CONV ("arm", st) o get_val
in
   fun arm_eval config =
      let
         val tms =
            Lib.mk_set (default_tms @ arm_configLib.mk_config_terms config)
         val ftch = fetch tms
         val dec = arm_decode tms
         val run = eval enc tms
      in
         fn (x, v) =>
            let
               val thm1 = ftch v
               val thm2 = hd (dec (x, v))
               val thm3 = Run_CONV thm2
               val thm4 = thm3 |> Drule.SPEC_ALL
                               |> rhsc
                               |> set_cond thm1
                               |> run
               val r = rhsc thm4
               val thm5 = STATE_CONV (mk_proj_encoding r)
               val thm6 = STATE_CONV (mk_proj_exception r)
               val thm = Drule.LIST_CONJ [thm1, thm2, thm3, thm4, thm5, thm6]
            in
               MP_Next thm
               handle HOL_ERR {message = "different constructors", ...} =>
                 MP_Next0 thm
            end
      end
end

local
   fun uncond c = Lib.mem (Char.toUpper c) [#"E", #"F"]
in
   fun arm_step_hex config =
      let
         val ev = arm_eval config
      in
         fn s =>
            let
               val s = utilsLib.removeSpaces s
               val v = bitstringSyntax.bitstring_of_hexstring s
            in
               if String.size s = 8 andalso uncond (String.sub (s, 0))
                  then [ev ([true], v)]
               else [ev ([false, true], v), ev ([true, false], v)]
            end
      end
end

fun arm_step_code config =
   let
      val step_hex = List.map (arm_step_hex config)
      open assemblerLib
   in
      fn q: string quotation =>
         let
            val (code, warnings) = armAssemblerLib.arm_code_with_warnings q
         in
            if List.null warnings
               then ()
            else ( printn "\n>>>> Warning: contains UNPREDICTABLE code. >>>>\n"
                 ; printLines warnings
                 ; printn "\n<<<<\n"
                 )
          ; step_hex code
         end
   end

local
   fun cases l =
      let
         val n = List.length l
      in
         List.foldl
            (fn (b, (i, a)) =>
               (i + 1, if b then List.tabulate (n, Lib.equal i) :: a else a))
            (0, []) l
         |> snd
      end
in
   fun arm_step config =
      let
         val ev = arm_eval config
      in
         fn s =>
            let
               val (x, v) = mk_arm_opcode s
            in
               List.map (fn x => ldm_stm_rule s (ev (x, v))) (cases x)
            end
      end
end

val () = Parse.reveal "add"

(* ---------------------------- *)

(*

val tms =
   List.map fix_datatype [``~^st.CPSR.T``, ``^st.Encoding = Encoding_ARM``]

val dec = arm_decode tms

val config = ""
val tms = arm_configLib.mk_config_terms config


dec (mk_arm_opcode "MSR (cpsr, imm, control)")

val (x, v) = mk_arm_opcode "RFEIA"
val (x, v) = mk_arm_opcode "MSR (cpsr, imm, control)"

dec (mk_arm_opcode "MSR (cpsr, imm)")
dec (mk_arm_opcode "RFEIA")

val dec = arm_decode_hex ""
dec "E10F1000"
dec "E12FF001"
dec "E32FF0FF"
dec "E328F40F"

val ev = arm_step ""

ev "MSR (cpsr, imm)";
ev "MSR (cpsr, reg)";
ev "MSR (cpsr, imm, control)";
ev "MSR (cpsr, reg, control)";
ev "MRS (cpsr)";
ev "RFEIA";
ev "RFEIB";
ev "RFEDA";
ev "RFEDB";
ev "RFEIA (wb)";
ev "RFEIB (wb)";
ev "RFEDA (wb)";
ev "RFEDB (wb)";

*)


end
