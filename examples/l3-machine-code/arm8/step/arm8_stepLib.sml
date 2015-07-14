(* ------------------------------------------------------------------------
   ARMv8 step evaluator
   ------------------------------------------------------------------------ *)

structure arm8_stepLib :> arm8_stepLib =
struct

open HolKernel boolLib bossLib
open lcsymtacs arm8Theory arm8_stepTheory arm8AssemblerLib
open blastLib

structure Parse =
struct
   open Parse
   fun remove (s, tmg) = fst (term_grammar.mfupdate_overload_info
                                (Overload.remove_overloaded_form s) tmg)
   val (tyg, tmg) = arm8_stepTheory.arm8_step_grammars
   val tmg = List.foldl remove tmg ["cond", "size"]
   val (Type, Term) = parse_from_grammars (tyg, tmg)
end
open Parse

(*
val _ = List.map Parse.hide ["cond", "size"]
val () = List.map Parse.reveal ["cond", "size"]
*)

val ERR = Feedback.mk_HOL_ERR "arm8_stepLib"
val WARN = Feedback.HOL_WARNING "arm8_stepLib"

val () = show_assums := true

(* ========================================================================= *)

val rhsc = utilsLib.rhsc
fun mapl x = utilsLib.augment x [[]]
val reg_ty = wordsSyntax.mk_int_word_type 5
fun reg_var v = Term.mk_var (v, reg_ty)
val r31 = wordsSyntax.mk_wordii (31, 5)
fun NetFromList l = List.foldl (Lib.uncurry Net.insert) Net.empty l

val arm8_monop = HolKernel.syntax_fns1 "arm8"

(* ---------------------------- *)

local
   val state_fns = utilsLib.accessor_fns ``:arm8_state``
   val other_fns =
      [pairSyntax.fst_tm, pairSyntax.snd_tm, bitstringSyntax.v2w_tm,
       ``(h >< l) : 'a word -> 'b word``] @
      utilsLib.update_fns ``:arm8_state`` @
      utilsLib.accessor_fns ``:TCR_EL1``
   val exc = ``SND (raise'exception e s : 'a # arm8_state)``
in
   val cond_rand_thms = utilsLib.mk_cond_rand_thms (other_fns @ state_fns)
   val snd_exception_thms =
      utilsLib.map_conv
         (Drule.GEN_ALL o
          utilsLib.SRW_CONV [cond_rand_thms, arm8Theory.raise'exception_def] o
          (fn tm => Term.mk_comb (tm, exc))) state_fns
end

(* ---------------------------- *)

(* ARMv8 datatype theorems/conversions *)

fun datatype_thms thms =
   thms @ [pairTheory.FST, pairTheory.SND, wordsTheory.w2w_id,
           cond_rand_thms, snd_exception_thms, boolTheory.COND_ID,
           optionTheory.NOT_SOME_NONE] @
   utilsLib.datatype_rewrites true "arm8"
      ["arm8_state", "MemOp", "LogicalOp", "MoveWideOp", "RevOp",
       "ShiftType", "BranchType"]

val DATATYPE_CONV = REWRITE_CONV (datatype_thms [])
val DATATYPE_RULE = Conv.CONV_RULE DATATYPE_CONV
val FULL_DATATYPE_RULE = utilsLib.FULL_CONV_RULE DATATYPE_CONV
val HYP_DATATYPE_RULE = utilsLib.ALL_HYP_CONV_RULE DATATYPE_CONV

val COND_UPDATE = Q.prove(
   `!b a x y c m n f.
      (if b then (a =+ x) ((c =+ m) f) else (a =+ y) ((c =+ n) f)) =
      (a =+ if b then x else y) ((c =+ if b then m else n) f)`,
   Cases
   THEN REWRITE_TAC [combinTheory.APPLY_UPDATE_ID]
   )

val COND_UPDATE_CONV =
   REWRITE_CONV
     (COND_UPDATE ::
      utilsLib.mk_cond_update_thms [``:arm8_state``, ``:ProcState``])

val COND_UPDATE_RULE = Conv.CONV_RULE COND_UPDATE_CONV

val st = ``s: arm8_state``
val EV0 = utilsLib.STEP (datatype_thms, st)

val resetEvConv = utilsLib.resetStepConv
val setEvConv = utilsLib.setStepConv

fun SPLIT_31 d =
   let
      val p = boolSyntax.mk_eq (reg_var d, r31)
   in
      [[p], [boolSyntax.mk_neg p]]
   end

val IS_31 = hd o SPLIT_31
val NOT_31 = hd o tl o SPLIT_31

fun TF (t: term frag list) = utilsLib.augment (t, [boolSyntax.T, boolSyntax.F])
fun TF0 t = TF t [[]]

val thms =
   [CheckSPAlignment_rwt, SetTheFlags, AddWithCarry,
    wordsTheory.FST_ADD_WITH_CARRY, wordsTheory.word_len_def,
    wordsTheory.WORD_EXTRACT_ZERO2,
    X_rwt, write'X_rwt, SP_rwt, write'SP_rwt,
    mem1, mem2, mem4, mem8, write'mem1, write'mem2, write'mem4, write'mem8]

fun EV l = utilsLib.STEP (datatype_thms, st) (l @ thms)

(* ========================================================================= *)

val () = Feedback.set_trace "notify type variable guesses" 0
val () = setEvConv (Conv.DEPTH_CONV wordsLib.SIZES_CONV)

(* instruction semantics *)

val lem =
   blastLib.BBLAST_PROVE
      ``!x:word64.
         bit_field_insert 11 0 (0w: word12) x = x && 0xFFFFFFFFFFFFF000w``

val Address_rwt =
   EV [dfn'Address_def, lem] [NOT_31 "d"] []
      ``dfn'Address (page, imm, d)``

(* ---------------------------- *)

val Nop_rwt =
   EV [dfn'Hint_def] [] [] ``dfn'Hint SystemHintOp_NOP``

val AddSubCarry_rwt =
   EV [dfn'AddSubCarry_def] (SPLIT_31 "d") (TF0 `setflags`)
      ``dfn'AddSubCarry (sf, sub_op, setflags, m, n, d)``

val AddSubExtendRegister_rwt =
   EV [dfn'AddSubExtendRegister_def, ExtendReg_def]
      (SPLIT_31 "d") (TF `sub_op` (TF0 `setflags`))
      ``dfn'AddSubExtendRegister
         (sf, sub_op, setflags, m, extend_type, imm3, n, d)``

val AddSubImmediate_rwt =
   EV [dfn'AddSubImmediate_def] (SPLIT_31 "d") (TF `sub_op` (TF0 `setflags`))
      ``dfn'AddSubImmediate (sf, sub_op, setflags, imm, n, d)``

val AddSubShiftedRegister_rwt =
   EV [dfn'AddSubShiftedRegister_def, ShiftReg_def]
      (SPLIT_31 "d") (TF `sub_op` (TF0 `setflags`))
      ``dfn'AddSubShiftedRegister
         (sf, sub_op, setflags, shift_type, m, imm, n, d)``

val LogicalImmediate_rwt =
   EV [dfn'LogicalImmediate_def] (SPLIT_31 "d") (TF0 `setflags`)
      ``dfn'LogicalImmediate (sf, opc, setflags, imm, n, d)``

val LogicalShiftedRegister_rwt =
   EV [dfn'LogicalShiftedRegister_def, ShiftReg_def]
      (SPLIT_31 "d") (TF0 `setflags`)
      ``dfn'LogicalShiftedRegister
         (sf, opc, invert, setflags, shift_type, shift_amount, m, n, d)``

val Shift_rwt =
   EV [dfn'Shift_def, ShiftReg_def] (SPLIT_31 "d") []
      ``dfn'Shift (sf, shift_type, m, n, d)``

val MoveWide_rwt =
   EV [dfn'MoveWide_def] (SPLIT_31 "d") []
      ``dfn'MoveWide (sf, opcode, hw, imm, d)``

val BitfieldMove_rwt =
   EV [dfn'BitfieldMove_def, Replicate_32_64] (SPLIT_31 "d") []
      ``dfn'BitfieldMove (sf: word32, inzero, ext, wmask, tmask, r, s, n, d)`` @
   EV [dfn'BitfieldMove_def, Replicate_32_64] (SPLIT_31 "d") []
      ``dfn'BitfieldMove (sf: word64, inzero, ext, wmask, tmask, r, s, n, d)``

val ConditionalCompareImmediate_rwt =
   EV [dfn'ConditionalCompareImmediate_def, ConditionHolds_def]
      [] (TF0 `sub_op`)
      ``dfn'ConditionalCompareImmediate
          (sf, sub_op, imm, cond, (n, z, c, v), rn)``
      |> List.map COND_UPDATE_RULE

val ConditionalCompareRegister_rwt =
   EV [dfn'ConditionalCompareRegister_def, ConditionHolds_def]
      [] (TF0 `sub_op`)
      ``dfn'ConditionalCompareRegister
          (sf, sub_op, cond, (n, z, c, v), rm, rn)``
      |> List.map COND_UPDATE_RULE

val ConditionalSelect_rwt =
   EV [dfn'ConditionalSelect_def, ConditionHolds_def] (SPLIT_31 "d") []
      ``dfn'ConditionalSelect (sf, else_inv, else_inc, cond, m, n, d)``

val CountLeading_rwt =
   EV [dfn'CountLeading_def] (SPLIT_31 "d") []
      ``dfn'CountLeading (sf, count_clz, n, d)``

val ExtractRegister_rwt =
   EV [dfn'ExtractRegister_def] (SPLIT_31 "d") []
      ``dfn'ExtractRegister (sf, imms, m, n, d)``

val Division_rwt =
   EV [dfn'Division_def] (SPLIT_31 "d") []
      ``dfn'Division (sf, unsigned, m, n, d)``

val MultiplyAddSub_rwt =
   EV [dfn'MultiplyAddSub_def] (SPLIT_31 "d") []
      ``dfn'MultiplyAddSub (sf, sub_op, m, a, n, d)``

val MultiplyAddSubLong_rwt =
   EV [dfn'MultiplyAddSubLong_def] (SPLIT_31 "d") []
      ``dfn'MultiplyAddSubLong (sub_op, signed, m, a, n, d)``

val MultiplyHigh_rwt =
   EV [dfn'MultiplyHigh_def] (SPLIT_31 "d") []
      ``dfn'MultiplyHigh (signed, m, n, d)``

val Reverse32_rwt =
   EV [dfn'Reverse_def] (SPLIT_31 "d") []
      ``dfn'Reverse (sf:word32, op, n, d)``

val Reverse64_rwt =
   EV [dfn'Reverse_def] (SPLIT_31 "d") []
      ``dfn'Reverse (sf:word64, op, n, d)``

val CRC_rwt =
   EV [dfn'CRC_def] (SPLIT_31 "d") []
      ``dfn'CRC (sz, crc32c, m, n, d)``

(* ---------------------------- *)

val map_rule = List.map (DATATYPE_RULE o COND_UPDATE_RULE o HYP_DATATYPE_RULE)

val BranchImmediate_rwt =
   EV [dfn'BranchImmediate_def, BranchTo_rwt] [] []
      ``dfn'BranchImmediate (offset, branch_type)``
      |> map_rule

val BranchRegister_rwt =
   EV [dfn'BranchRegister_def, BranchTo_rwt] [] []
      ``dfn'BranchRegister (n, branch_type)``
      |> map_rule

val tm =
   ``ConditionTest (cond,^st.PSTATE.N,^st.PSTATE.Z,^st.PSTATE.C,^st.PSTATE.V)``

val BranchConditional_rwt =
   EV [dfn'BranchConditional_def, BranchTo_rwt, ConditionHolds_def]
      [[tm], [boolSyntax.mk_neg tm]] []
      ``dfn'BranchConditional (offset, cond)``
      |> map_rule

val CompareAndBranch_rwt =
   EV [dfn'CompareAndBranch_def, BranchTo_rwt]
      [[``t = 31w: word5``],
       [``t <> 31w: word5``, ``w2w (s.REG t) = 0w: 'a word``],
       [``t <> 31w: word5``, ``w2w (s.REG t) <> 0w: 'a word``]] []
      ``dfn'CompareAndBranch (sf, iszero, offset, t)``
      |> map_rule

val tm = ``word_bit (w2n (bit_pos: word6)) (w2w (^st.REG t): 'a word)``

val TestBitAndBranch_rwt =
   EV [dfn'TestBitAndBranch_def, BranchTo_rwt, wordsTheory.word_bit_0]
      [[``t = 31w: word5``],
       [``t <> 31w: word5``, tm],
       [``t <> 31w: word5``, boolSyntax.mk_neg tm]]
      (TF `bit_val` [[]])
      ``dfn'TestBitAndBranch (sf, bit_pos, bit_val, offset, t)``
      |> map_rule

(* ---------------------------- *)

val lem = Q.prove(
   `!a:'a word b c. (if b then a else a + c) = a + (if b then 0w else c)`,
   lrw []
   )

val sp_rule =
   utilsLib.ALL_HYP_CONV_RULE
     (DATATYPE_CONV
      THENC SIMP_CONV std_ss []
      THENC utilsLib.INST_REWRITE_CONV
              [mem1, mem2, mem4, mem8,
               write'mem1, write'mem2, write'mem4, write'mem8]
      THENC SIMP_CONV std_ss []
      THENC DATATYPE_CONV) o
   SIMP_RULE std_ss [wordsTheory.WORD_ADD_0] o
   COND_UPDATE_RULE

val map_sp_rule = List.map sp_rule

fun mk_sz i = Term.mk_var ("sz", wordsSyntax.mk_int_word_type i)

val LoadStoreImmediate_rwt =
   List.map
      (fn i =>
         EV [dfn'LoadStoreImmediate_def, LoadStoreSingle_def, lem]
            ((List.map (fn c => ``n <> 31w:word5`` :: c) (SPLIT_31 "t")) @
             (List.map (fn c => ``n = 31w:word5`` :: c) (SPLIT_31 "t")))
            ((TF `wback` [[`memop` |-> ``MemOp_LOAD``]]) @
             (TF `wback` [[`memop` |-> ``MemOp_STORE``]]))
            ``dfn'LoadStoreImmediate
                 (^(mk_sz i), regsize_word, memop, acctype, signed, F, F,
                  wback, postindex, unsigned_offset, offset, n, t)``
            |> map_sp_rule)
      [8, 16, 32, 64]
      |> List.concat

val LoadStoreRegister_rwt =
   List.map
      (fn i =>
         EV [dfn'LoadStoreRegister_def, LoadStoreSingle_def, ExtendReg_def, lem]
            ((List.map (fn c => ``n <> 31w:word5`` :: c) (SPLIT_31 "t")) @
             (List.map (fn c => ``n = 31w:word5`` :: c) (SPLIT_31 "t")))
            [[`memop` |-> ``MemOp_LOAD``], [`memop` |-> ``MemOp_STORE``]]
            ``dfn'LoadStoreRegister
                 (^(mk_sz i), regsize_word, memop, signed, m, extend_type,
                  shift, n, t)``
            |> List.map COND_UPDATE_RULE)
      [8, 16, 32, 64]
      |> List.concat

val LoadLiteral_rwt =
   List.map
      (fn i =>
         EV [dfn'LoadLiteral_def] (SPLIT_31 "t") [[`memop` |-> ``MemOp_LOAD``]]
            ``dfn'LoadLiteral (^(mk_sz i), memop, signed, offset, t)``)
      [32, 64]
      |> List.concat

val map_sp_rule =
   List.map
      (utilsLib.ALL_HYP_CONV_RULE
         (DATATYPE_CONV
          THENC SIMP_CONV std_ss [alignmentTheory.aligned_numeric]) o
       sp_rule)

val LoadStorePair_rwt =
   List.map
      (fn i =>
         EV [dfn'LoadStorePair_def, lem]
            [
             [``t = 31w:word5``, ``t2 = 31w:word5``, ``n = 31w:word5``],
             [``t = 31w:word5``, ``t2 = 31w:word5``, ``n <> 31w:word5``],
             [``t = 31w:word5``, ``t2 <> 31w:word5``, ``n = 31w:word5``],
             [``t = 31w:word5``, ``t2 <> 31w:word5``, ``n <> 31w:word5``],
             [``t <> 31w:word5``, ``t2 = 31w:word5``, ``n = 31w:word5``],
             [``t <> 31w:word5``, ``t2 = 31w:word5``, ``n <> 31w:word5``],
             [``t <> 31w:word5``, ``t2 <> 31w:word5``, ``n = 31w:word5``],
             [``t <> 31w:word5``, ``t2 <> 31w:word5``, ``n <> 31w:word5``]
            ]
            ((TF `wback` [[`memop` |-> ``MemOp_LOAD``]]) @
             (TF `wback` [[`memop` |-> ``MemOp_STORE``]]))
            ``dfn'LoadStorePair
                 (^(mk_sz i), memop, acctype, signed, F, F,
                  wback, postindex, offset, n, t, t2)``
            |> map_sp_rule)
      [32, 64]
      |> List.concat

local
   val f = UNDISCH o DECIDE o Parse.Term

   val lem1 = f `(~wback \/ n <> t \/ (n = 31w: word5)) ==>
                 ~(((d /\ wback) /\ (n = t)) /\ n <> 31w)`

   val lem2 = f `(~wback \/ n <> t /\ n <> t2 \/ (n = 31w: word5)) ==>
                 ~(((d /\ wback) /\ ((n = t) \/ (n = t2))) /\ n <> 31w)`

   fun w1 i = bitstringSyntax.fixedwidth_of_int (i, 1)
   fun w2 i = bitstringSyntax.padded_fixedwidth_of_int (i, 2)

   val () = setEvConv (Conv.DEPTH_CONV bitstringLib.word_bit_CONV)
in
   val LoadStoreImmediate =
      EV [LoadStoreImmediate_def, LoadStoreImmediateN_def, lem1] []
         (utilsLib.augment (`sz`, List.tabulate (4, w2)) [[]])
         ``LoadStoreImmediate
              (sz,v2w [x0; x1],acctype,wback,postindex,unsigned_offset,
               offset,n,t)``
   val LoadStorePair =
      EV [LoadStorePair_def, LoadStorePairN_def, lem2]
         [[``~((memop = MemOp_LOAD) /\ (t = t2: word5))``]]
         (utilsLib.augment (`sf`, List.tabulate (2, w1)) [[]])
         ``LoadStorePair
              (sf,memop,acctype,signed,wback,postindex,offset,n,t,t2)``
end

val () = Feedback.set_trace "notify type variable guesses" 1
val () = setEvConv (Conv.DEPTH_CONV wordsLib.SIZES_CONV)

(* ========================================================================= *)

(* Fetch *)

fun mk_opcode v =
   let
      val (l, ty) = listSyntax.dest_list v
      val () = ignore (ty = Type.bool andalso List.length l <= 32
                       orelse raise ERR "mk_opcode" "bad Bool list")
   in
      listSyntax.mk_list (utilsLib.padLeft boolSyntax.F 32 l, Type.bool)
   end

local
   val pat = bitstringSyntax.mk_bstring 32 0
in
   fun inst_opcode tm = Thm.INST (fst (Term.match_term pat (mk_opcode tm)))
   val inst_branch_hint = Thm.INST [st |-> ``^st with branch_hint := NONE``]
end

val Fetch_rwt =
   EV [Fetch_def, mem_word_def, bitstringTheory.word_concat_v2w_rwt]
      [[
       ``^st.MEM s.PC = ^(bitstringSyntax.mk_vec 8 0)``,
       ``^st.MEM (s.PC + 1w) = ^(bitstringSyntax.mk_vec 8 8)``,
       ``^st.MEM (s.PC + 2w) = ^(bitstringSyntax.mk_vec 8 16)``,
       ``^st.MEM (s.PC + 3w) = ^(bitstringSyntax.mk_vec 8 24)``
      ]]
      [] ``Fetch``
     |> hd
     |> inst_branch_hint
     |> SIMP_RULE (srw_ss()++boolSimps.LET_ss) [bitstringTheory.fixwidth_def]
     |> HYP_DATATYPE_RULE

fun arm8_fetch tm = inst_opcode tm Fetch_rwt

(* ========================================================================= *)

(* Decode *)

local
   val cmp = wordsLib.words_compset()
   val () = ( bitstringLib.add_bitstring_compset cmp
            ; integer_wordLib.add_integer_word_compset cmp
            ; intReduce.add_int_compset cmp
            ; computeLib.scrub_thms
                [wordsTheory.bit_field_insert_def,
                 wordsTheory.word_sdiv_def,
                 wordsTheory.word_div_def]
                cmp
            ; computeLib.add_thms
                (datatype_thms
                   [DecodeShift_def, HighestSetBit_def, Ones_def, Zeros_def,
                    Replicate_def, DecodeRegExtend_def, ShiftValue_def,
                    bit_field_insert_thms, ConditionTest, ExtendWord,
                    DecodeBitMasks_def, LSL_def, LSR_def, ASR_def, ROR_def,
                    wordsTheory.WORD_AND_CLAUSES, wordsTheory.WORD_OR_CLAUSES,
                    num2ShiftType_thm, num2ExtendType_thm])
                cmp
            ; computeLib.add_conv
                (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV) cmp
            )
in
   val ARM8_CONV = computeLib.CBV_CONV cmp
end

local
   val Unallocated = Term.prim_mk_const {Name = "Unallocated", Thy = "arm8"}
   val Reserved = Term.prim_mk_const {Name = "Reserved", Thy = "arm8"}

   val asms = [arm8_stepTheory.DecodeLem, arm8_stepTheory.DecodeInzeroExtend] @
     List.map (ASSUME o Parse.Term)
      [
       `DecodeBitMasks
          (v2w [F],v2w [x8; x9; x10; x11; x12; x13],
           v2w [x2; x3; x4; x5; x6; x7],T) = SOME (imm:word32, x)`,
       `DecodeBitMasks
          (v2w [x2],v2w [x9; x10; x11; x12; x13; x14],
           v2w [x3; x4; x5; x6; x7; x8],T) = SOME (imm:word64, x)`,
       `DecodeBitMasks
          (v2w [F],v2w [F; x7; x8; x9; x10; x11],
           v2w [F; x2; x3; x4; x5; x6],F) = SOME (imm:word32, x)`,
       `DecodeBitMasks
          (v2w [T],v2w [x8; x9; x10; x11; x12; x13],
           v2w [x2; x3; x4; x5; x6; x7],F)= SOME (imm:word64, x)`
      ]

   val r_rwt =
      utilsLib.map_conv
         (EVAL THENC REWRITE_CONV [arm8Theory.num2SystemHintOp_thm])
         [``v2w [F; F; F] <+ 6w: word3``,
          ``arm8$num2SystemHintOp (w2n (v2w [F; F; F]: word3))``]

   val r1 = REWRITE_RULE [r_rwt]
   val r2 = utilsLib.INST_REWRITE_RULE (LoadStoreImmediate @ LoadStorePair)
   val r3 =
      utilsLib.ALL_HYP_CONV_RULE
        (REWRITE_CONV [GSYM arm8Theory.MemOp_distinct,
                       arm8_stepTheory.LoadCheck,
                       boolTheory.DE_MORGAN_THM]) o
      SIMP_RULE (srw_ss()++boolSimps.LET_ss) asms

   val ast_thms =
      List.filter
        ((fn tm => not (tm = Unallocated orelse tm = Reserved)) o rhsc) o
      utilsLib.split_conditions o r2 o r1

   exception Decode of string * thm list

   fun ast_thm name thm =
      case ast_thms thm of
         [] => NONE
       | [thm] => SOME (r3 thm)
       | thms => raise Decode (name, thms)

   val concat_CONV =
      Conv.REWR_CONV bitstringTheory.word_concat_v2w_rwt THENC ARM8_CONV

   val case_word2_literal =
      Q.ISPEC `v2w [b1; b0] : word2` (Q.SPEC `f` boolTheory.literal_case_THM)

   val LoadStoreRegister =
      SIMP_RULE (std_ss++boolSimps.LET_ss) [] LoadStoreRegister_def

   val Decode_rwt =
      Decode_def
      |> Thm.SPEC (bitstringSyntax.mk_vec 32 0)
      |> Conv.RIGHT_CONV_RULE
            (REWRITE_CONV
                [DecodeLogicalOp, DecodeRevOp, arm8Theory.boolify32_v2w,
                 LoadStoreRegister, case_word2_literal]
             THENC Conv.DEPTH_CONV PairedLambda.let_CONV
             THENC REWRITE_CONV [bitstringTheory.ops_to_v2w, EVAL ``n2v 0``]
             THENC Conv.DEPTH_CONV concat_CONV
             THENC Conv.DEPTH_CONV bitstringLib.word_bit_CONV
             THENC Conv.DEPTH_CONV BETA_CONV
             THENC Conv.DEPTH_CONV bitstringLib.v2w_eq_CONV
             THENC REWRITE_CONV [])

   fun get_var_vars p pat =
      List.mapPartial (fn (c, tm) => if c = #"." then SOME tm else NONE)
         (ListPair.zip (String.explode p, fst (listSyntax.dest_list pat)))

   fun all_substs acc =
      fn [] => acc
       | (h: Term.term) :: t =>
          all_substs
            (List.map (fn s => (h |-> boolSyntax.T) :: s) acc @
             List.map (fn s => (h |-> boolSyntax.F) :: s) acc) t
   val all_substs = all_substs [[]]

   val get_opc = Term.rand o Term.rand o utilsLib.lhsc
in
   fun decode_thm tm = r1 (inst_opcode tm Decode_rwt)
   fun decode_rwt (name, p) =
      let
         val pat = utilsLib.pattern (String.map (fn #"." => #"_" | s => s) p)
         val thm = decode_thm pat
         val ast = ast_thm name
         val i = ref 0
         fun dec s =
            if List.null s
               then SOME ((name, pat), Option.valOf (ast thm))
            else case ast (Thm.INST s thm) of
                    NONE => NONE
                  | SOME th =>
                     ( Portable.inc i
                     ; SOME ((name ^ "-" ^ Int.toString (!i), get_opc th), th)
                     )
      in
         List.mapPartial dec (all_substs (get_var_vars p pat))
      end
end

val ps = (List.concat o List.map decode_rwt)
  [
   ("Address",                      "___TFFFF________________________"),
   ("AddSubShiftedRegister32",      "F..FTFTT__F_____F_______________"),
   ("AddSubShiftedRegister64",      "T..FTFTT__F_____________________"),
   ("AddSubExtendRegister",         "...FTFTTFFT_____________________"),
   ("AddSubImmediate",              "...TFFFTF_______________________"),
   ("AddSubCarry",                  "._.TTFTFFFF_____FFFFFF__________"),
   ("LogicalShiftedRegister32",     "F..FTFTF________F_______________"),
   ("LogicalShiftedRegister64",     "T..FTFTF________________________"),
   ("LogicalImmediate32",           "F..TFFTFFF______________________"),
   ("LogicalImmediate64",           "T..TFFTFF_______________________"),
   ("Shift",                        ".FFTTFTFTTF_____FFTF____________"),
   ("MoveWide32",                   "F__TFFTFTF______________________"),
   ("MoveWide64",                   "T__TFFTFT_______________________"),
   ("BitfieldMove32",               "F__TFFTTFFF_____F_______________"),
   ("BitfieldMove64",               "T__TFFTTFT______________________"),
   ("ConditionalCompareImmediate",  "..TTTFTFFTF_________TF_____F____"),
   ("ConditionalCompareRegister",   "..TTTFTFFTF_________FF_____F____"),
   ("ConditionalSelect",            "._FTTFTFTFF_________F___________"),
   ("CountLeading",                 ".TFTTFTFTTFFFFFFFFFTF___________"),
   ("ExtractRegister32",            "FFFTFFTTTFF_____F_______________"),
   ("ExtractRegister64",            "TFFTFFTTTTF_____________________"),
   ("Division",                     ".FFTTFTFTTF_____FFFFT___________"),
   ("MultiplyAddSub",               ".FFTTFTTFFF_____________________"),
   ("MultiplyAddSubLong",           "TFFTTFTT_FT_____________________"),
   ("MultiplyHigh",                 "TFFTTFTT_TF_____F_______________"),
   ("Reverse32",                    "FTFTTFTFTTFFFFFFFFFF____________"),
   ("Reverse64",                    "TTFTTFTFTTFFFFFFFFFF____________"),
   ("CRC8",                         "FFFTTFTFTTF_____FTF_FF__________"),
   ("CRC16",                        "FFFTTFTFTTF_____FTF_FT__________"),
   ("CRC32",                        "FFFTTFTFTTF_____FTF_TF__________"),
   ("CRC64",                        "TFFTTFTFTTF_____FTF_TT__________"),
   ("BranchConditional",            "FTFTFTFF___________________F____"),
   ("BranchImmediate",              ".FFTFT__________________________"),
   ("BranchRegisterJMP",            "TTFTFTTFFFFTTTTTFFFFFF_____FFFFF"),
   ("BranchRegisterCALL",           "TTFTFTTFFFTTTTTTFFFFFF_____FFFFF"),
   ("BranchRegisterRET",            "TTFTFTTFFTFTTTTTFFFFFF_____FFFFF"),
   ("CompareAndBranch",             ".FTTFTF_________________________"),
   ("TestBitAndBranch",             ".FTTFTT.________________________"),
   ("LoadStoreImmediate-1",         "..TTTFFF..F__________.__________"),
   ("LoadStoreImmediate-2",         "..TTTFFT..______________________"),
   ("LoadLiteral",                  "..FTTFFF________________________"),
   ("LoadStoreRegister",            "..TTTFFF..T______T__TF__________"),
   ("StorePair32",                  "FFTFTFF_.F______________________"),
   ("LoadPair32",                   "F_TFTFF_.T______________________"),
   ("LoadStorePair64",              "TFTFTFF_..______________________"),
   ("NoOperation",                  "TTFTFTFTFFFFFFTTFFTFFFFFFFFTTTTT")
  ]

local
   val ps2 = List.map fst ps
   val d = Redblackmap.fromList String.compare
             (List.map (utilsLib.lowercase ## I) ps2)
   val net = NetFromList (List.map Lib.swap ps2)
in
   val arm8_names = List.map fst ps2
   fun arm8_pattern s = Redblackmap.peek (d, utilsLib.lowercase s)
   fun arm8_instruction tm =
      case Net.match (mk_opcode tm) net of
         [tm] => SOME tm
       | _ => NONE
end

local
   val (_, mk_Decode, _, _) = arm8_monop "Decode"
   val ty32 = fcpSyntax.mk_int_numeric_type 32
   val rwts = List.map snd ps
   val decode_CONV = utilsLib.FULL_CONV_RULE (REWRITE_CONV []) o
                     utilsLib.INST_REWRITE_CONV rwts
   fun fallback tm = (WARN "arm8_decode" "fallback decode"; decode_thm tm)
in
   fun arm8_decode v =
      let
         val opc = mk_opcode v
         val tm = mk_Decode (bitstringSyntax.mk_v2w (opc, ty32))
         val thm = decode_CONV tm handle Conv.UNCHANGED => fallback opc
      in
         if utilsLib.vacuous thm then fallback opc else thm
      end
   fun arm8_decode_instruction s =
      case arm8_pattern s of
         SOME tm => arm8_decode tm
       | NONE => raise ERR "arm8_decode_instruction" "not found"
   val arm8_decode_hex = arm8_decode o bitstringSyntax.bitstring_of_hexstring
end

(* ========================================================================= *)

(* Step *)

(*

   fun printer (_: int) _ (a: 'a Net.net) = PolyML.PrettyString "<net>"
   val () = PolyML.addPrettyPrinter printer

*)

local
   val mk_net =
      NetFromList o
      List.map (fn th => (rator (utilsLib.lhsc th),
                          FULL_DATATYPE_RULE (inst_branch_hint th)))
   val net = mk_net
     (Address_rwt @ AddSubCarry_rwt @ AddSubExtendRegister_rwt @
      AddSubImmediate_rwt @ AddSubShiftedRegister_rwt @ LogicalImmediate_rwt @
      LogicalShiftedRegister_rwt @ Shift_rwt @ MoveWide_rwt @ BitfieldMove_rwt @
      ConditionalCompareImmediate_rwt @ ConditionalCompareRegister_rwt @
      ConditionalSelect_rwt @ CountLeading_rwt @ ExtractRegister_rwt @
      Division_rwt @ MultiplyAddSub_rwt @ MultiplyAddSubLong_rwt @
      MultiplyHigh_rwt @ Reverse32_rwt @ Reverse64_rwt @ CRC_rwt @
      BranchImmediate_rwt @ BranchRegister_rwt @ BranchConditional_rwt @
      CompareAndBranch_rwt @ TestBitAndBranch_rwt @ LoadStoreImmediate_rwt @
      LoadStoreRegister_rwt @ LoadLiteral_rwt @ LoadStorePair_rwt @ Nop_rwt
      )
   val get_next = Term.rator o utilsLib.lhsc
   val r = REWRITE_RULE []
   fun make_match tm thm =
      r (Drule.INST_TY_TERM (Term.match_term (get_next thm) tm) thm)
in
   fun arm8_next tm =
      List.mapPartial (Lib.total (make_match tm)) (Net.match tm net)
end

local
   val v31 = bitstringLib.v2w_n2w_CONV ``v2w [T; T; T; T; T] : word5``
   val cnv = REWRITE_CONV [DECIDE ``a <> b \/ (a = b: 'a)``, v31]
   val vs = List.filter Term.is_var o fst o listSyntax.dest_list o fst o
            bitstringSyntax.dest_v2w
   val r31 = wordsSyntax.mk_wordii (31, 5)
   val reg_31 =
      List.concat o
      List.mapPartial
        (Option.composePartial
            (fn (l, r) =>
                if r = r31
                   then SOME (List.map (fn v => v |-> boolSyntax.T) (vs l))
                else NONE,
             Lib.total boolSyntax.dest_eq))
   val rule = utilsLib.ALL_HYP_CONV_RULE cnv
in
   fun REG_31_RULE thm =
      let
         val l = reg_31 (Thm.hyp thm)
      in
         if List.null l then thm else rule (Thm.INST l thm)
      end
end

val remove_vacuous = List.filter (not o utilsLib.vacuous)

local
   val arm8_run = utilsLib.Run_CONV ("arm8", st) o rhsc
   val (_, mk_exception, _, _) = arm8_monop "arm8_state_exception"
   val arm8_exception =
      DATATYPE_CONV o mk_exception o snd o pairSyntax.dest_pair o utilsLib.rhsc
   val get_next = Term.rator o utilsLib.rhsc o Drule.SPEC_ALL
   val rule = REG_31_RULE o Conv.RIGHT_CONV_RULE DATATYPE_CONV o
              MATCH_MP arm8_stepTheory.NextStateARM8
in
   fun arm8_step v =
      let
         val thm1 = arm8_fetch v
         val thm2 = arm8_decode v
         val thm3 = arm8_run thm2
         val tm = get_next thm3
         val thm4s = arm8_next tm
         fun conj th = Drule.LIST_CONJ [thm1, thm2, thm3, th, arm8_exception th]
      in
         remove_vacuous (List.map (rule o conj) thm4s)
      end
end

local
   val (_, _, dest_DecodeBitMasks, _) = arm8_monop "DecodeBitMasks"
   val is_dbm = Lib.can (dest_DecodeBitMasks o lhs)
   val dst = pairSyntax.dest_pair o optionSyntax.dest_some
in
   val DecodeBitMasks_CONV = Conv.REWR_CONV DecodeBitMasks_def THENC ARM8_CONV
   fun DecodeBitMasks_RULE th =
      case List.filter is_dbm (Thm.hyp th) of
         [tm] => let
                    val (vimm, vx) = dst (rhs tm)
                    val thm = DecodeBitMasks_CONV (lhs tm)
                    val th' =
                       case Lib.total dst (rhsc thm) of
                          SOME (imm, x) => Thm.INST [vimm |-> imm, vx |-> x] th
                        | NONE => th
                 in
                    utilsLib.MATCH_HYP_CONV_RULE
                       (REWRITE_CONV [optionTheory.NOT_NONE_SOME, thm]) tm th'
                 end
       | _ => th
end

local
   val rule =
      DecodeBitMasks_RULE o
      utilsLib.FULL_CONV_RULE
         (ARM8_CONV THENC REWRITE_CONV [wordsTheory.WORD_SUB_INTRO]
          THENC DATATYPE_CONV)
   val step_hex = remove_vacuous o List.map rule o arm8_step o
                  bitstringSyntax.bitstring_of_hexstring
in
   fun arm8_step_hex s = Lib.with_exn step_hex s (ERR "arm8_step_hex" s)
end

val arm8_step_code = List.map arm8_step_hex o arm8AssemblerLib.arm8_code

(* Testing...

open arm8_stepLib

local
   val gen = Random.newgenseed 1.0
   fun random_bit () =
      if Random.range (0, 2) gen = 0 then boolSyntax.T else boolSyntax.F
in
   fun random_hex tm =
      let
         val l = Term.free_vars tm
         val s = List.map (fn v => v |-> random_bit ()) l
      in
         bitstringSyntax.hexstring_of_term (Term.subst s tm)
      end
end

val test =
   Count.apply (arm8_step_hex o (fn s => (print (s ^ "\n"); s)) o random_hex o
                Option.valOf o arm8_pattern)

val test = arm8_step o Option.valOf o arm8_pattern

val unsupported =
   List.mapPartial (fn n => if List.null (test n) then SOME n else NONE)
      arm8_names

(* should all be pre-fetch instructions *)

List.map arm8_decode_instruction unsupported

*)

end
