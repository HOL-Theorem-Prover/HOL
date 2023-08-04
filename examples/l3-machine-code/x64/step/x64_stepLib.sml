(* ------------------------------------------------------------------------
   x64 step evaluator
   ------------------------------------------------------------------------ *)

structure x64_stepLib :> x64_stepLib =
struct

open HolKernel Parse boolLib bossLib
open updateLib utilsLib x64Lib x64Theory x64_stepTheory

val ambient_grammars = (type_grammar(), term_grammar())
val _ = temp_set_grammars
          (x64Theory.x64_grammars |> apsnd ParseExtras.grammar_loose_equality)

val ERR = Feedback.mk_HOL_ERR "x64_stepLib"

val () = show_assums := true

(* ========================================================================= *)

(*
val print_thms =
   List.app
     (fn th => (Lib.with_flag (show_assums, false) print_thm th; print "\n\n"))
*)

val st = ``s: x64_state``
val regs = TypeBase.constructors_of ``:Zreg``
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
   val cond_rand_thms = utilsLib.mk_cond_rand_thms (other_fns @ state_fns)
   val snd_exception_thms =
      utilsLib.map_conv
         (Drule.GEN_ALL o
          utilsLib.SRW_CONV [cond_rand_thms, x64Theory.raise'exception_def] o
          (fn tm => Term.mk_comb (tm, exc))) state_fns
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
                        (Conv.REWR_CONV x64_stepTheory.prefixGroup
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
   val cmp = wordsLib.words_compset ()
   val () =
      utilsLib.add_theory
         ([immediate8_rwt, immediate16_rwt, immediate32_rwt, immediate64_rwt,
           immediate8, immediate16, immediate32, immediate64, immediate_def,
           OpSize_rwt, rbp, x64Theory.readModRM_def, readModRM_not_4_or_5,
           readModRM_byte_not_4, readModRM_dword_not_4,
           RexReg_rwt boolSyntax.F, RexReg_rwt boolSyntax.T],
          utilsLib.filter_inventory ["readPrefix"] x64Theory.inventory) cmp
   val () = utilsLib.add_base_datatypes cmp
   val () = computeLib.add_conv
               (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV) cmp
   val () = computeLib.add_conv (``boolify8``, 1, boolify8_CONV) cmp
   val () = computeLib.add_conv (``readPrefix``, 1, prefix_CONV) cmp
in
   val x64_CONV = utilsLib.CHANGE_CBV_CONV cmp
end

val highByte =
  utilsLib.map_conv x64_CONV
    (List.map (fn r => ``num2Zreg (Zreg2num ^r - 4)``)
              [``RSP``, ``RBP``, ``RSI``, ``RDI``])

local
   val state_with_pre = (st |-> ``^st with RIP := ^st.RIP + n2w len``)
   fun ADD_PRECOND_RULE thm =
      thm |> Thm.INST [state_with_pre]
          |> utilsLib.ALL_HYP_CONV_RULE DATATYPE_CONV
          |> Conv.CONV_RULE DATATYPE_CONV
   val rwts = ref ([]: thm list)
in
   fun getThms () = [highByte] @ List.map ADD_PRECOND_RULE (!rwts)
   fun resetThms () = rwts := []
   fun addThms thms = (rwts := thms @ !rwts; thms)
end

(* ------------------------------------------------------------------------ *)

val mem8_rwt =
   EV [mem8_def] [[``^st.MEM a = v``]] []
      ``mem8 a``
      |> hd

val write'mem8_rwt =
   EV [write'mem8_def] [] []
      ``write'mem8 (d, addr)``
      |> hd
      |> Drule.ADD_ASSUM ``^st.MEM addr = wv``

(* ------------------------------------------------------------------------ *)

val sizes = [``Z8 have_rex``, ``Z16``, ``Z32``, ``Z64``]

val Cflag_rwt =
   EV [Eflag_def] [[``^st.EFLAGS Z_CF = SOME cflag``]] []
      ``Eflag Z_CF``
   |> hd

val write'Eflag_rwt =
   EV [write'Eflag_def] [] []
      ``write'Eflag (b, flag)``
   |> hd

val FlagUnspecified_rwt =
   EV [FlagUnspecified_def] [] []
      ``FlagUnspecified (flag)``
   |> hd

val write_PF_rwt =
   EV [write_PF_def, write'PF_def, write'Eflag_rwt] [] []
      ``write_PF w``
   |> hd

val () = setEvConv (Conv.DEPTH_CONV (wordsLib.WORD_BIT_INDEX_CONV true))

val write_SF_rwt =
   EV [write_SF_def, write'SF_def, write'Eflag_rwt, word_size_msb_def,
       Zsize_width_def] []
      (mapl (`size`, sizes))
      ``write_SF (size, w)``

val write_ZF_rwt =
   EV [write_ZF_def, write'ZF_def, write'Eflag_rwt] [] (mapl (`size`, sizes))
      ``write_ZF (size, w)``

val erase_eflags =
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

(* ------------------------------------------------------------------------ *)

val no_imm_ea =
   [[`ea` |-> ``Zea_r (Z8 have_rex, r)``],
    [`ea` |-> ``Zea_r (Z16, r)``],
    [`ea` |-> ``Zea_r (Z32, r)``],
    [`ea` |-> ``Zea_r (Z64, r)``],
    [`ea` |-> ``Zea_m (Z8 have_rex, a)``],
    [`ea` |-> ``Zea_m (Z16, a)``],
    [`ea` |-> ``Zea_m (Z32, a)``],
    [`ea` |-> ``Zea_m (Z64, a)``]] : utilsLib.cover

val ea =
   [[`ea` |-> ``Zea_i (Z8 have_rex, i)``],
    [`ea` |-> ``Zea_i (Z16, i)``],
    [`ea` |-> ``Zea_i (Z32, i)``],
    [`ea` |-> ``Zea_i (Z64, i)``]] @ no_imm_ea

val () = resetThms()

val EA_rwt =
   EV [EA_def, restrictSize_def, id_state_cond, pred_setTheory.IN_INSERT,
       pred_setTheory.NOT_IN_EMPTY, mem8_rwt, mem16_rwt, mem32_rwt, mem64_rwt]
      [] ea
      ``EA ea``

val write'EA_rwt =
   EV [write'EA_def, bitfield_inserts,
       pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY,
       write'mem8_rwt, write'mem16_rwt, write'mem32_rwt, write'mem64_rwt] []
      no_imm_ea
      ``write'EA (d, ea)``
   |> List.map (Conv.RIGHT_CONV_RULE
                  (utilsLib.EXTRACT_CONV THENC COND_UPDATE_CONV))

val wv_to_v = List.map (Q.INST [`wv` |-> `v`])

val write'EA_rwt_r = wv_to_v write'EA_rwt

val xmm =
   [[`xmm` |-> ``xmm_reg x``],
    [`xmm` |-> ``xmm_mem (NONE, ZnoBase, d)``],
    [`xmm` |-> ``xmm_mem (NONE, ZripBase, d)``],
    [`xmm` |-> ``xmm_mem (NONE, ZregBase r, d)``],
    [`xmm` |-> ``xmm_mem (SOME (scale, inx), ZnoBase, d)``],
    [`xmm` |-> ``xmm_mem (SOME (scale, inx), ZripBase, d)``],
    [`xmm` |-> ``xmm_mem (SOME (scale, inx), ZregBase r, d)``]] : utilsLib.cover

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

val write_arith_eflags_rwt =
   EV ([write_arith_eflags_def, write'CF_def, write'OF_def, write'Eflag_rwt] @
       write_arith_eflags_except_CF_OF_rwt) [] (mapl (`size`, sizes))
      ``write_arith_eflags (size, r, carry, overflow)``

val write_logical_eflags_rwt =
   EV ([write_logical_eflags_def, write'CF_def, write'OF_def, write'Eflag_rwt] @
       write_arith_eflags_rwt) [] (mapl (`size`, sizes))
      ``write_logical_eflags (size, w)``

val () = setEvConv (Conv.DEPTH_CONV (wordsLib.WORD_BIT_INDEX_CONV true))

val ea_op =
   [[`size1` |-> ``Z8 have_rex``,  `ea` |-> ``Zea_r (Z8 have_rex, r)``],
    [`size1` |-> ``Z16``, `ea` |-> ``Zea_r (Z16, r)``],
    [`size1` |-> ``Z32``, `ea` |-> ``Zea_r (Z32, r)``],
    [`size1` |-> ``Z64``, `ea` |-> ``Zea_r (Z64, r)``],
    [`size1` |-> ``Z8 have_rex``,  `ea` |-> ``Zea_m (Z8 have_rex, a)``],
    [`size1` |-> ``Z16``, `ea` |-> ``Zea_m (Z16, a)``],
    [`size1` |-> ``Z32``, `ea` |-> ``Zea_m (Z32, a)``],
    [`size1` |-> ``Z64``, `ea` |-> ``Zea_m (Z64, a)``]] : utilsLib.cover

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
   |> addThms

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
   |> addThms

(* ------------------------------------------------------------------------ *)

val () = resetEvConv ()

val conds = TypeBase.constructors_of ``:Zcond``

val read_cond_rwts =
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
   |> addThms

val SignExtension_rwt =
   EV [SignExtension_def] []
      [[`s1` |-> ``Z8 (b)``, `s2` |-> ``Z16``],
       [`s1` |-> ``Z8 (b)``, `s2` |-> ``Z32``],
       [`s1` |-> ``Z8 (b)``, `s2` |-> ``Z64``],
       [`s1` |-> ``Z16``, `s2` |-> ``Z32``],
       [`s1` |-> ``Z16``, `s2` |-> ``Z64``],
       [`s1` |-> ``Z32``, `s2` |-> ``Z64``]]
      ``SignExtension (w, s1, s2)``

val SignExtension64_rwt =
   EV (SignExtension64_def :: SignExtension_rwt) []
      [[`sz` |-> ``Z8 (b)``], [`sz` |-> ``Z16``],
       [`sz` |-> ``Z32``], [`sz` |-> ``Z64``]]
      ``SignExtension64 (w, sz)``

(* ------------------------------------------------------------------------ *)

val rm =
   [[`rm` |-> ``Zr r``],
    [`rm` |-> ``Zm (NONE, ZnoBase, d)``],
    [`rm` |-> ``Zm (NONE, ZripBase, d)``],
    [`rm` |-> ``Zm (NONE, ZregBase r, d)``],
    [`rm` |-> ``Zm (SOME (scale, ix), ZnoBase, d)``],
    [`rm` |-> ``Zm (SOME (scale, ix), ZripBase, d)``],
    [`rm` |-> ``Zm (SOME (scale, ix), ZregBase r, d)``]]: utilsLib.cover

val r_rm =
   [[`ds` |-> ``Zr_rm (r1, Zr r2)``],
    [`ds` |-> ``Zr_rm (r, Zm (NONE, ZnoBase, d))``],
    [`ds` |-> ``Zr_rm (r, Zm (NONE, ZripBase, d))``],
    [`ds` |-> ``Zr_rm (r1, Zm (NONE, ZregBase r2, d))``],
    [`ds` |-> ``Zr_rm (r, Zm (SOME (scale, ix), ZnoBase, d))``],
    [`ds` |-> ``Zr_rm (r, Zm (SOME (scale, ix), ZripBase, d))``],
    [`ds` |-> ``Zr_rm (r1, Zm (SOME (scale, ix), ZregBase r2, d))``]]
    : utilsLib.cover

val rm_i =
   [[`ds` |-> ``Zrm_i (Zr r, i)``],
    [`ds` |-> ``Zrm_i (Zm (NONE, ZnoBase, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (NONE, ZripBase, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (NONE, ZregBase r, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (SOME (scale, ix), ZnoBase, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (SOME (scale, ix), ZripBase, d), i)``],
    [`ds` |-> ``Zrm_i (Zm (SOME (scale, ix), ZregBase r, d), i)``]]
    : utilsLib.cover

val rm_r =
   [[`ds` |-> ``Zrm_r (Zr r1, r2)``],
    [`ds` |-> ``Zrm_r (Zm (NONE, ZnoBase, d), r)``],
    [`ds` |-> ``Zrm_r (Zm (NONE, ZripBase, d), r)``],
    [`ds` |-> ``Zrm_r (Zm (NONE, ZregBase r1, d), r2)``],
    [`ds` |-> ``Zrm_r (Zm (SOME (scale, ix), ZnoBase, d), r)``],
    [`ds` |-> ``Zrm_r (Zm (SOME (scale, ix), ZripBase, d), r)``],
    [`ds` |-> ``Zrm_r (Zm (SOME (scale, ix), ZregBase r1, d), r2)``]]
    : utilsLib.cover

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
         (updateLib.OVERRIDE_UPDATES_CONV ``:Zeflags -> bool option``
           (SIMP_CONV (srw_ss()) []))))

val cond_update_rule = List.map (Conv.CONV_RULE COND_UPDATE_CONV)

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
   |> addThms

(* val Znop_rwt = EV [dfn'Znop_def] [] [] ``dfn'Znop n`` |> addThms *)

val Zcmc_rwt =
   EV [dfn'Zcmc_def, CF_def, write'CF_def, Cflag_rwt, write'Eflag_rwt] [] []
      ``dfn'Zcmc``
   |> addThms

val Zclc_rwt =
   EV [dfn'Zclc_def, CF_def, write'CF_def, write'Eflag_rwt] [] []
      ``dfn'Zclc``
   |> addThms

val Zstc_rwt =
   EV [dfn'Zstc_def, CF_def, write'CF_def, write'Eflag_rwt] [] []
      ``dfn'Zstc``
   |> addThms

val Zbinop_rwts =
   EV ([dfn'Zbinop_def, read_dest_src_ea_def] @
       ea_Zsrc_rwt @ ea_Zdest_rwt @ EA_rwt) [] src_dst
      ``dfn'Zbinop (bop, size, ds)``
   |> addThms

val Zcall_imm_rwts =
   EV ([dfn'Zcall_def, x64_push_rip_def, x64_push_aux_def, jump_to_ea_def,
        call_dest_from_ea_def, write'mem64_rwt] @ ea_Zimm_rm_rwt) [] []
      ``dfn'Zcall (Zimm imm)``
   |> data_hyp_rule
   |> addThms

val Zcall_rm_rwts =
   EV ([dfn'Zcall_def, x64_push_rip_def, x64_push_aux_def, jump_to_ea_def,
        call_dest_from_ea_def, write'mem64_rwt, mem64_rwt] @
       ea_Zimm_rm_rwt) [] rm
      ``dfn'Zcall (Zrm rm)``
   |> data_hyp_rule
   |> addThms

val Zjcc_rwts =
   EV ([dfn'Zjcc_def] @ read_cond_rwts) [] (mapl (`c`, conds))
      ``dfn'Zjcc (c, imm)``
   |> cond_update_rule
   |> addThms

val Zjmp_rwts =
   EV ([dfn'Zjmp_def] @ ea_Zrm_rwt @ EA_rwt) [] rm
      ``dfn'Zjmp rm``
   |> addThms

val Zlea_rwts =
   EV ([dfn'Zlea_def, get_ea_address_def] @
       ea_Zsrc_rwt @ ea_Zdest_rwt @ EA_rwt @ write'EA_rwt) [] lea
      ``dfn'Zlea (size, ds)``
   |> addThms

val Zleave_rwts =
   EV ([dfn'Zleave_def, x64_pop_def, x64_pop_aux_def, mem64_rwt,
        combinTheory.UPDATE_EQ] @ ea_Zrm_rwt @ write'EA_rwt)
      [] []
      ``dfn'Zleave``
   |> addThms

val Zloop_rwts =
   EV ([dfn'Zloop_def] @ read_cond_rwts) []
      (mapl (`c`, [``Z_NE``, ``Z_E``, ``Z_ALWAYS``]))
      ``dfn'Zloop (c, imm)``
   |> data_hyp_rule
   |> cond_update_rule
   |> addThms

val Zmonop_rwts =
   EV ([dfn'Zmonop_def] @ ea_Zrm_rwt @ EA_rwt) [] rm_cases
      ``dfn'Zmonop (mop, size, rm)``
   |> addThms

val Zmov_rwts =
   EV ([dfn'Zmov_def] @
       ea_Zsrc_rwt @ ea_Zdest_rwt @ read_cond_rwts @ EA_rwt @ write'EA_rwt)
       [] (utilsLib.augment (`c`, Lib.butlast conds) src_dst_not8 @
           utilsLib.augment (`c`, [``Z_ALWAYS``]) src_dst)
      ``dfn'Zmov (c, size, ds)``
   (* |> is_some_hyp_rule *)
   |> cond_update_rule
   |> addThms

val Zmovzx_rwts =
   EV ([dfn'Zmovzx_def, cond_rand_thms, word_thms] @
      ea_Zsrc_rwt @ ea_Zdest_rwt @ EA_rwt @ write'EA_rwt)
       [] extends
      ``dfn'Zmovzx (size, ds, size2)``
   |> addThms

val Zmovsx_rwts =
   EV ([dfn'Zmovsx_def, cond_rand_thms, extension_thms, word_thms] @
       SignExtension_rwt @ ea_Zsrc_rwt @ ea_Zdest_rwt @ EA_rwt @ write'EA_rwt)
      [] extends
      ``dfn'Zmovsx (size, ds, size2)``
   |> addThms

val Zmul_rwts =
   EV ([dfn'Zmul_def, erase_eflags, value_width_def, Zsize_width_def,
        word_mul_thms, word_mul_top] @
       ea_Zrm_rwt @ EA_rwt @ write'EA_rwt) [] rm_cases
      ``dfn'Zmul (size, rm)``
   |> addThms

val Zimul_rwts =
   EV ([dfn'Zimul_def, erase_eflags, value_width_def, Zsize_width_def,
        write'CF_def, write'OF_def, write'Eflag_rwt, word_thms,
        integer_wordTheory.word_mul_i2w] @
       SignExtension64_rwt @ ea_Zrm_rwt @ EA_rwt @ write'EA_rwt) [] rm_cases
      ``dfn'Zimul (size, rm)``
   |> flags_override_rule
   |> addThms

val Zimul2_rwts =
   EV ([dfn'Zimul2_def, erase_eflags, value_width_def, Zsize_width_def,
        write'CF_def, write'OF_def, write'Eflag_rwt, word_thms,
        integer_wordTheory.word_mul_i2w] @ SignExtension64_rwt @ ea_Zrm_rwt @
       EA_rwt @ write'EA_rwt) [] rm_cases_not8
      ``dfn'Zimul2 (size, d, rm)``
   |> flags_override_rule
   |> addThms

val Zimul3_rwts =
   EV ([dfn'Zimul3_def, erase_eflags, value_width_def, Zsize_width_def,
        write'CF_def, write'OF_def, write'Eflag_rwt, word_thms,
        integer_wordTheory.word_mul_i2w] @ SignExtension64_rwt @ ea_Zrm_rwt @
       EA_rwt @ write'EA_rwt) [] rm_cases_not8
      ``dfn'Zimul3 (size, d, rm, imm)``
   |> flags_override_rule
   |> addThms

val Zpop_rwts =
   EV ([dfn'Zpop_def, x64_pop_def, x64_pop_aux_def, mem64_rwt] @
        ea_Zrm_rwt @ write'EA_rwt)
      [] rm
      ``dfn'Zpop rm``
   |> data_hyp_rule
   |> addThms

val Zpush_imm_rwts =
   EV ([dfn'Zpush_def, x64_push_def, x64_push_aux_def, write'mem64_rwt] @
       ea_Zimm_rm_rwt @ EA_rwt) [] []
      ``dfn'Zpush (Zimm imm)``
   |> data_hyp_rule
   |> addThms

val Zpush_rm_rwts =
   EV ([dfn'Zpush_def, x64_push_def, x64_push_aux_def, write'mem64_rwt] @
       ea_Zimm_rm_rwt @ EA_rwt) [] rm
      ``dfn'Zpush (Zrm rm)``
   |> data_hyp_rule
   |> addThms

val Zret_rwts =
   EV [dfn'Zret_def, x64_pop_rip_def, x64_pop_aux_def, x64_drop_def, mem64_rwt,
       combinTheory.UPDATE_EQ]
      [[``(7 >< 0) (imm: word64) = 0w: word8``]] []
      ``dfn'Zret imm``
   |> addThms

val Zset_rwts =
   EV ([dfn'Zset_def, word_thms] @
       read_cond_rwts @ ea_Zrm_rwt @ write'EA_rwt) []
      (utilsLib.augment (`c`, Lib.butlast conds) rm)
      ``dfn'Zset (c, have_rex, rm)``
   |> addThms

val Zxchg_rwts =
   EV ([dfn'Zxchg_def] @ ea_Zrm_rwt @ EA_rwt @ write'EA_rwt_r)
      [] rm_cases
      ``dfn'Zxchg (size, rm, r2)``
   |> data_hyp_rule
   (* |> is_some_hyp_rule *)
   |> addThms

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

val Zdiv_rwts =
  div_ev [] (tl rm_cases)
      ``dfn'Zdiv (size, rm)``
   |> List.map avoid_error_rule
   |> addThms

val Zidiv_rwts =
  div_ev [] (tl rm_cases)
      ``dfn'Zidiv (size, rm)``
   |> List.map avoid_error_rule
   |> addThms

val Zdiv_byte_reg_rwts_1 =
  div_ev [] [] ``dfn'Zdiv (Z8 T, Zr r)``
   |> List.map avoid_error_rule
   |> addThms

val Zidiv_byte_reg_rwts_1 =
  div_ev [] [] ``dfn'Zidiv (Z8 T, Zr r)``
   |> List.map avoid_error_rule
   |> addThms

val Zdiv_byte_reg_rwts_2 =
  div_ev []
   [[`r` |-> ``RAX``], [`r` |-> ``RCX``], [`r` |-> ``RDX``], [`r` |-> ``RBX``],
    [`r` |-> ``RSP``], [`r` |-> ``RBP``], [`r` |-> ``RSI``], [`r` |-> ``RDI``]]
      ``dfn'Zdiv (Z8 F, Zr r)``
   |> List.map avoid_error_rule
   |> addThms

val Zidiv_byte_reg_rwts_2 =
  div_ev []
   [[`r` |-> ``RAX``], [`r` |-> ``RCX``], [`r` |-> ``RDX``], [`r` |-> ``RBX``],
    [`r` |-> ``RSP``], [`r` |-> ``RBP``], [`r` |-> ``RSI``], [`r` |-> ``RDI``]]
      ``dfn'Zidiv (Z8 F, Zr r)``
   |> List.map avoid_error_rule
   |> addThms

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

val lem1 = prove(
  “(!x y.
    (if IS_SOME x then i2w (THE x) else y) =
     case x of SOME a => i2w a | _ => y) /\
   (!x y.
    (if IS_SOME x then w2w (i2w (THE x) : 'c word) else y) =
     case x of SOME a => w2w (i2w a : 'c word) | _ => y)”,
  strip_tac \\ Cases \\ rw [])

val lem2 = prove(
  “(case x of
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
              ((Z_ZF =+ SOME (x IN {EQ; UN})) s.EFLAGS)))))”,
  Cases_on `x` \\ simp [])

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

val pshift =
  EV ([dfn'PSRLW_imm_def, dfn'PSRAW_imm_def, dfn'PSLLW_imm_def,
       dfn'PSRLD_imm_def, dfn'PSRAD_imm_def, dfn'PSLLD_imm_def,
       dfn'PSRLQ_imm_def, dfn'PSLLQ_imm_def, dfn'PSRLDQ_def, dfn'PSLLDQ_def] @
      XMM_rwt @ write'XMM_rwt) [] []

val sse_bin =
  fpEV (SOME [``sse_add``, ``sse_sub``, ``sse_mul``, ``sse_div``,
              ``sse_min``, ``sse_max``])

val sse_logic =
  fpEV (SOME [``sse_and``, ``sse_andn``, ``sse_or``, ``sse_xor``])

val sse_compare =
  fpEV (SOME [``sse_eq_oq``, ``sse_lt_os``, ``sse_le_os``, ``sse_unord_q``,
              ``sse_neq_uq``, ``sse_nlt_us``, ``sse_nle_us``, ``sse_ord_q``])

val sse = rule o fpEV NONE
val sse_rm = fpEV (SOME [])

val bin_PD = sse_bin ``dfn'bin_PD (f, dst, xmm)``
val bin_SD = sse_bin ``dfn'bin_SD (f, dst, xmm)``
val bin_PS = sse_bin ``dfn'bin_PS (f, dst, xmm)``
val bin_SS = sse_bin ``dfn'bin_SS (f, dst, xmm)``

val logic_PD = sse_logic ``dfn'logic_PD (f, dst, xmm)``
val logic_PS = sse_logic ``dfn'logic_PS (f, dst, xmm)``

val CMPPD = sse_compare ``dfn'CMPPD (f, dst, xmm)``
val CMPSD = sse_compare ``dfn'CMPSD (f, dst, xmm)``
val CMPPS = sse_compare ``dfn'CMPPS (f, dst, xmm)``
val CMPSS = sse_compare ``dfn'CMPSS (f, dst, xmm)``

val COMISD = sse ``dfn'COMISD (src1, xmm)``
val COMISS = sse ``dfn'COMISS (src1, xmm)``

val SQRTPD = sse ``dfn'SQRTPD (dst, xmm)``
val SQRTSD = sse ``dfn'SQRTSD (dst, xmm)``
val SQRTPS = sse ``dfn'SQRTPS (dst, xmm)``
val SQRTSS = sse ``dfn'SQRTSS (dst, xmm)``

val CVTDQ2PD = sse ``dfn'CVTDQ2PD (dst, xmm)``
val CVTDQ2PS = sse ``dfn'CVTDQ2PS (dst, xmm)``
val CVTPD2DQ = sse ``dfn'CVTPD2DQ (F, dst, xmm)``
val CVTTPD2DQ = sse ``dfn'CVTPD2DQ (T, dst, xmm)``
val CVTPD2PS = sse ``dfn'CVTPD2PS (dst, xmm)``
val CVTPS2DQ = sse ``dfn'CVTPS2DQ (F, dst, xmm)``
val CVTTPS2DQ = sse ``dfn'CVTPS2DQ (T, dst, xmm)``
val CVTPS2PD = sse ``dfn'CVTPS2PD (dst, xmm)``
val CVTSD2SS = sse ``dfn'CVTSD2SS (dst, xmm)``
val CVTSS2SD = sse ``dfn'CVTSS2SD (dst, xmm)``
val CVTSD2SI_0 = sse ``dfn'CVTSD2SI (F, T, r, xmm)``
val CVTSD2SI_1 = sse ``dfn'CVTSD2SI (F, F, r, xmm)``
val CVTTSD2SI_0 = sse ``dfn'CVTSD2SI (T, T, r, xmm)``
val CVTTSD2SI_1 = sse ``dfn'CVTSD2SI (T, F, r, xmm)``
val CVTSI2SD_0 = sse_rm ``dfn'CVTSI2SD (T, x, rm)``
val CVTSI2SD_1 = sse_rm ``dfn'CVTSI2SD (F, x, rm)``
val CVTSI2SS_0 = sse_rm ``dfn'CVTSI2SS (T, x, rm)``
val CVTSI2SS_1 = sse_rm ``dfn'CVTSI2SS (F, x, rm)``
val CVTSS2SI_0 = sse ``dfn'CVTSS2SI (F, T, r, xmm)``
val CVTSS2SI_1 = sse ``dfn'CVTSS2SI (F, F, r, xmm)``
val CVTTSS2SI_0 = sse ``dfn'CVTSS2SI (T, T, r, xmm)``
val CVTTSS2SI_1 = sse ``dfn'CVTSS2SI (T, F, r, xmm)``

(* TODO: MOVAP_D_S *)

val MOVUP_D_S_0 = sse ``dfn'MOVUP_D_S (double, xmm_reg (dst), xmm)``
val MOVUP_D_S_1 = sse ``dfn'MOVUP_D_S (double, xmm, xmm_reg (src))`` |> List.tl

val MOVSD_0 = sse ``dfn'MOVSD (xmm_reg (dst), xmm)``
val MOVSD_1 = sse ``dfn'MOVSD (xmm, xmm_reg (src))`` |> List.tl |> wv_to_v
val MOVSS_0 = sse ``dfn'MOVSS (xmm_reg (dst), xmm)``
val MOVSS_1 = sse ``dfn'MOVSS (xmm, xmm_reg (src))`` |> List.tl |> wv_to_v

val MOV_D_Q_0 = sse_rm ``dfn'MOV_D_Q (T, T, dst, rm)``
val MOV_D_Q_1 = sse_rm ``dfn'MOV_D_Q (T, F, dst, rm)``
val MOV_D_Q_2 = sse_rm ``dfn'MOV_D_Q (F, T, dst, rm)``
val MOV_D_Q_3 = sse_rm ``dfn'MOV_D_Q (F, F, dst, rm)``

val MOVQ_0 = sse ``dfn'MOVQ (xmm_reg (dst), xmm)``
val MOVQ_1 = sse ``dfn'MOVQ (xmm, xmm_reg (src))`` |> List.tl

val PCMPEQQ = sse ``dfn'PCMPEQQ (dst, xmm)``

val PSRLW_imm = pshift ``dfn'PSRLW_imm (r, i)``
val PSRAW_imm = pshift ``dfn'PSRAW_imm (r, i)``
val PSLLW_imm = pshift ``dfn'PSLLW_imm (r, i)``
val PSRLD_imm = pshift ``dfn'PSRLD_imm (r, i)``
val PSRAD_imm = pshift ``dfn'PSRAD_imm (r, i)``
val PSLLD_imm = pshift ``dfn'PSLLD_imm (r, i)``
val PSRLQ_imm = pshift ``dfn'PSRLQ_imm (r, i)``
val PSLLQ_imm = pshift ``dfn'PSLLQ_imm (r, i)``
val PSRLDQ = pshift ``dfn'PSRLDQ (r, i)``
val PSLLDQ = pshift ``dfn'PSLLDQ (r, i)``

val _ = List.map addThms
  [bin_PD, bin_SD, bin_PS, bin_SS, logic_PD, logic_PS, CMPPD, CMPSD, CMPPS,
   CMPSS, COMISD, COMISS, SQRTPD, SQRTSD, SQRTPS, SQRTSS, CVTDQ2PD, CVTDQ2PS,
   CVTPD2DQ, CVTTPD2DQ, CVTPD2PS, CVTPS2DQ, CVTTPS2DQ, CVTPS2PD, CVTSD2SS,
   CVTSS2SD, CVTSD2SI_0, CVTSD2SI_1, CVTTSD2SI_0, CVTTSD2SI_1, CVTSI2SD_0,
   CVTSI2SD_1, CVTSI2SS_0, CVTSI2SS_1, CVTSS2SI_0, CVTSS2SI_1, CVTTSS2SI_0,
   CVTTSS2SI_1, MOVUP_D_S_0, MOVUP_D_S_1, MOV_D_Q_0, MOV_D_Q_1, MOV_D_Q_2,
   MOV_D_Q_3, MOVQ_0, MOVQ_1, MOVSD_0, MOVSD_1, MOVSS_0, MOVSS_1, PCMPEQQ,
   PSRLW_imm, PSRAW_imm, PSLLW_imm, PSRLD_imm, PSRAD_imm, PSLLD_imm,
   PSRLQ_imm, PSLLQ_imm, PSRLDQ, PSLLDQ]

(* ------------------------------------------------------------------------ *)

local
   fun decode_err s = ERR "x64_decode" s
   val i8 = fcpSyntax.mk_int_numeric_type 8
   val w8 = wordsSyntax.mk_int_word_type 8
   val imm8_tm = combinSyntax.mk_I (Term.mk_var ("imm", w8))
   fun mk_extract imm n =
      let
         val h = numSyntax.term_of_int (n - 1)
         val l = numSyntax.term_of_int (n - 8)
      in
         wordsSyntax.mk_word_extract(h, l, imm, i8)
      end
   fun mk_extracts n =
      let
         val mk =
            mk_extract (Term.mk_var ("imm", wordsSyntax.mk_int_word_type n))
         fun iter a n = if n < 8 then a else iter (mk n :: a) (n - 8)
      in
         iter [] n
      end
   fun mk_byte w = wordsSyntax.mk_wordi (w, 8)
   fun toByte (x, y) = mk_byte (Arbnum.fromHexString (String.implode [x, y]))
   val x64_fetch =
      (x64_CONV THENC REWRITE_CONV [wordsTheory.WORD_ADD_0])``x64_fetch s``
   fun fetch l =
      List.foldl
         (fn (b, (i, thm)) =>
            let
               val rwt = if i = 0
                            then ``^st.MEM (^st.RIP) = ^b``
                         else let
                                 val j = numSyntax.term_of_int i
                              in
                                 ``^st.MEM (^st.RIP + n2w ^j) = ^b``
                              end
            in
               (i + 1, PURE_REWRITE_RULE [ASSUME rwt, optionTheory.THE_DEF] thm)
            end) (0, x64_fetch) l |> snd
   val decode_tm = ``x64_decode (x64_fetch ^st)``
   fun decode_thm fetch_rwt =
      (Conv.RAND_CONV (Conv.REWR_CONV fetch_rwt) THENC x64_CONV) decode_tm
   val get_list =
     fst o listSyntax.dest_list o optionSyntax.dest_some o #3 o
     Lib.triple_of_list o pairSyntax.strip_pair
in
   fun get_bytes s =
      let
         fun iter a [] = List.rev a
           | iter a (l as (x::y::t)) =
                if List.all (Lib.equal #"_") l
                   then let
                           val n = List.length l * 4
                        in
                           List.rev a @
                             (if n = 8
                                 then [imm8_tm]
                              else if Lib.mem n [16, 32, 64]
                                 then mk_extracts n
                              else raise ERR "x64_decode"
                                    ("bad immediate length: " ^ Int.toString n))
                        end
                else iter (toByte (x, y) :: a) t
           | iter a [_] = raise decode_err "not even"
      in
         iter [] (String.explode s)
      end
   fun x64_decode l =
      let
         val thm = decode_thm (fetch l)
      in
         case boolSyntax.dest_strip_comb (utilsLib.rhsc thm) of
            ("x64$Zfull_inst", [a]) =>
               (case Lib.total get_list a of
                   SOME l =>
                     ( List.null l orelse not (wordsSyntax.is_n2w (hd l))
                       orelse raise decode_err "trailing bytes"
                     ; thm
                     )
                 | NONE => raise decode_err "decode failed")
          | _ => (Parse.print_thm thm; raise decode_err "too few bytes")
      end
   val x64_decode_hex = x64_decode o get_bytes
end

(* ------------------------------------------------------------------------ *)

local
   fun is_some_wv tm =
      ((tm |> boolSyntax.dest_eq |> snd
           |> Term.dest_var |> fst) = "wv")
      handle HOL_ERR _ => false
in
   fun FIX_SAME_ADDRESS_RULE thm =
      case List.partition is_some_wv (Thm.hyp thm) of
         ([], _) => thm
       | ([t], rst) =>
           let
              val (l, wv) = boolSyntax.dest_eq t
              val v = Term.mk_var ("v", Term.type_of wv)
              val tv = boolSyntax.mk_eq (l, v)
           in
              if List.exists (aconv tv) rst
                 then Thm.INST [wv |-> v] thm
              else thm
           end
       | _ => raise ERR "FIX_SAME_ADDRESS_RULE" "more than one"
end

local
   val rwts = [pairTheory.FST, pairTheory.SND, combinTheory.I_THM, word_thms]
   val TIDY_UP_CONV =
      REWRITE_CONV
         (List.take (utilsLib.datatype_rewrites false "x64" ["Zreg"], 2) @ rwts)
      THENC utilsLib.WGROUND_CONV
   val get_strm1 = Term.rand o Term.rand o Term.rand o Term.rand o utilsLib.rhsc
   val get_ast = Term.rand o Term.rator o Term.rand o Term.rand o utilsLib.rhsc
   fun sel ty f = TypeBasePure.mk_recordtype_fieldsel{tyname=ty,fieldname=f}
   val state_exception_tm =
      Term.prim_mk_const {Thy = "x64", Name = sel "x64_state" "exception"}
   fun mk_proj_exception r = Term.mk_comb (state_exception_tm, r)
   val twenty = numSyntax.term_of_int 20
   fun mk_len_thm thm1 =
      (Conv.RAND_CONV listLib.LENGTH_CONV THENC numLib.REDUCE_CONV)
         (numSyntax.mk_minus (twenty, listSyntax.mk_length (get_strm1 thm1)))
   fun bump_rip len = Term.subst [st |-> ``^st with RIP := ^st.RIP + n2w ^len``]
   val run_CONV = utilsLib.Run_CONV ("x64", st) o get_ast
   val run = utilsLib.ALL_HYP_CONV_RULE utilsLib.WGROUND_CONV o
             FIX_SAME_ADDRESS_RULE o
             utilsLib.ALL_HYP_CONV_RULE TIDY_UP_CONV o
             (INST_REWRITE_CONV (getThms ()) THENC TIDY_UP_CONV)
   val MP_Next  = Drule.MATCH_MP x64_stepTheory.NextStateX64
   val MP_Next0 = Drule.MATCH_MP x64_stepTheory.NextStateX64_0
   val STATE_CONV =
      REWRITE_CONV (utilsLib.datatype_rewrites true "x64" ["x64_state"] @
                    [boolTheory.COND_ID, cond_rand_thms])
   fun unchanged l =
      raise ERR "x64_step"
         ("Failed to evaluate: " ^
            Hol_pp.term_to_string (listSyntax.mk_list (l, ``:word8``)))
   val cache =
      ref (Redblackmap.mkDict String.compare: (string, thm) Redblackmap.dict)
   fun addToCache (s, thm) = (cache := Redblackmap.insert (!cache, s, thm); thm)
   fun checkCache s = Redblackmap.peek (!cache, s)
   val I_intro =
     Drule.GEN_ALL o
     Conv.RIGHT_CONV_RULE (ONCE_REWRITE_CONV [GSYM combinTheory.I_THM]) o
     Drule.SPEC_ALL
in
   fun x64_step l =
      let
         val thm1 = x64_decode l
         val thm2 = mk_len_thm thm1
         val thm4 = run_CONV thm1
         val s = utilsLib.rhsc (Drule.SPEC_ALL thm4)
         val thm4 = if Term.is_var s then I_intro thm4 else thm4
         val thm5 = (thm4 |> Drule.SPEC_ALL
                          |> utilsLib.rhsc
                          |> bump_rip (utilsLib.rhsc thm2)
                          |> run)
                    handle Conv.UNCHANGED => unchanged l
         val r = utilsLib.rhsc thm5
         val thm6 = Conv.QCONV STATE_CONV (mk_proj_exception r)
         val thm = Drule.LIST_CONJ [thm1, thm2, thm4, thm5, thm6]
      in
         MP_Next thm
         handle HOL_ERR {message = "different constructors", ...} =>
            MP_Next0 thm
      end
   fun x64_step_hex s =
      let
         val s = utilsLib.uppercase s
      in
         case checkCache s of
            SOME thm => thm
          | NONE => addToCache (s, x64_step (get_bytes s))
      end
end

val x64_decode_code =
   List.map x64_decode_hex o x64AssemblerLib.x64_code_no_spaces

val x64_step_code = List.map x64_step_hex o x64AssemblerLib.x64_code_no_spaces

val _ = temp_set_grammars ambient_grammars

(*

List.length (getThms ())

open x64_stepLib

val thms = Count.apply x64_step_code
  `nop                       ; 90
   mov [r11], al             ; 41 88 03
   jb 0x7                    ; 72 07
   add dword [rbp-0x8], 0x1  ; 83 45 f8 01
   movsxd rdx, eax           ; 48 63 d0
   movsx eax, al             ; 0f be c0
   movzx eax, al             ; 0f b6 c0`

Count.apply x64_step_hex "90";
Count.apply x64_step_hex "418803";
Count.apply x64_step_hex "487207";
Count.apply x64_step_hex "8345F801";
Count.apply x64_step_hex "4863D0";
Count.apply x64_step_hex "0FBEC0";
Count.apply x64_step_hex "0FB6C0";

Count.apply x64_step_hex "48BA________________";
Count.apply x64_decode_hex "48BA________________"

Count.apply x64_step_hex "41B8________";
Count.apply x64_decode_hex "41B8________"

Count.apply x64_decode_hex "8345F8__";
Count.apply x64_step_hex "8345F8__"

*)

(* ========================================================================= *)

end
