(* ------------------------------------------------------------------------
   x64 step evaluator
   ------------------------------------------------------------------------ *)

structure x64_stepLib :> x64_stepLib =
struct

open HolKernel Parse boolLib bossLib
open updateLib utilsLib x64Lib x64Theory x64_stepTheory

val ambient_grammars = (type_grammar(), term_grammar())
val _ = temp_set_grammars
          (valOf (grammarDB{thyname="x64"}) |> apsnd ParseExtras.grammar_loose_equality)

val ERR = Feedback.mk_HOL_ERR "x64_stepLib"

val () = show_assums := true

(* ========================================================================= *)

val st = ``s: x64_state``

local
   val cnv = Conv.REWR_CONV x64Theory.readPrefix_def
             THENC REWRITE_CONV [prefixGroup_def]
             THENC EVAL
             THENC REWRITE_CONV [rec'REX_def]
             THENC EVAL
   fun mk_ibyte w = wordsSyntax.mk_wordii (w, 8)
   val prefix_rwt1 =
      map_conv cnv
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
      map_conv (REWRITE_CONV [RexReg_def]
                         THENC EVAL
                         THENC REWRITE_CONV [num2Zreg_thm])
         (List.tabulate (8, fn i => ``RexReg (^b, ^(mk_3 i))``))
in
  val x64_CONV = computeLib.copy wordsLib.words_compset
    |> add_theory
      ([immediate8_rwt, immediate16_rwt, immediate32_rwt, immediate64_rwt,
        immediate8, immediate16, immediate32, immediate64, immediate_def,
        OpSize_rwt, rbp, x64Theory.readModRM_def, readModRM_not_4_or_5,
        readModRM_byte_not_4, readModRM_dword_not_4,
        RexReg_rwt boolSyntax.F, RexReg_rwt boolSyntax.T],
      filter_inventory ["readPrefix"] (Import.gen_inventory{thyname="x64"}))
    |> add_base_datatypes
    |> computeLib.add_conv
        (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)
    |> computeLib.add_conv (``boolify8``, 1, boolify8_CONV)
    |> computeLib.add_conv (``readPrefix``, 1, prefix_CONV)
    |> CHANGE_CBV_CONV
end

val thms = [highByte] @ (map UNDISCH_ALL o List.concat o map CONJUNCTS) [
  write_binop_rwts, write_monop_rwts, read_cond_rwts,
  Zbit_test_rwts, (*Znop_rwts,*) Zcmc_rwts, Zclc_rwts, Zstc_rwts, Zbinop_rwts,
  Zcall_imm_rwts, Zcall_rm_rwts, Zjcc_rwts, Zjmp_rwts, Zlea_rwts,
  Zleave_rwts, Zloop_rwts, Zmonop_rwts, Zmov_rwts, Zmovzx_rwts, Zmovsx_rwts,
  Zmul_rwts, Zimul_rwts, Zimul2_rwts, Zimul3_rwts, Zpop_rwts, Zpush_imm_rwts,
  Zpush_rm_rwts, Zret_rwts, Zset_rwts, Zxchg_rwts, Zdiv_rwts, Zidiv_rwts,
  Zdiv_byte_reg_rwts_2, Zidiv_byte_reg_rwts_2,
  bin_PD, bin_SD, bin_PS, bin_SS, logic_PD, logic_PS, CMPPD, CMPSD, CMPPS,
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
           | iter _ [_] = raise decode_err "not even"
      in
         iter [] (String.explode s)
      end
   fun x64_decode l =
      let
         val thm = decode_thm (fetch l)
      in
         case boolSyntax.dest_strip_comb (rhsc thm) of
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
         (List.take (datatype_rewrites false "x64" ["Zreg"], 2) @ rwts)
      THENC WGROUND_CONV
   val get_strm1 = Term.rand o Term.rand o Term.rand o Term.rand o rhsc
   val get_ast = Term.rand o Term.rator o Term.rand o Term.rand o rhsc
   fun sel ty f = TypeBasePure.mk_recordtype_fieldsel{tyname=ty,fieldname=f}
   val state_exception_tm =
      Term.prim_mk_const {Thy = "x64", Name = sel "x64_state" "exception"}
   fun mk_proj_exception r = Term.mk_comb (state_exception_tm, r)
   val twenty = numSyntax.term_of_int 20
   fun mk_len_thm thm1 =
      (Conv.RAND_CONV listLib.LENGTH_CONV THENC numLib.REDUCE_CONV)
         (numSyntax.mk_minus (twenty, listSyntax.mk_length (get_strm1 thm1)))
   fun bump_rip len = Term.subst [st |-> ``^st with RIP := ^st.RIP + n2w ^len``]
   val run_CONV = Run_CONV ("x64", st) o get_ast
   val run = ALL_HYP_CONV_RULE WGROUND_CONV o
             FIX_SAME_ADDRESS_RULE o
             ALL_HYP_CONV_RULE TIDY_UP_CONV o
             (INST_REWRITE_CONV thms THENC TIDY_UP_CONV)
   val MP_Next  = Drule.MATCH_MP x64_stepTheory.NextStateX64
   val MP_Next0 = Drule.MATCH_MP x64_stepTheory.NextStateX64_0
   val STATE_CONV =
      REWRITE_CONV (datatype_rewrites true "x64" ["x64_state"] @
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
         val s = rhsc (Drule.SPEC_ALL thm4)
         val thm4 = if Term.is_var s then I_intro thm4 else thm4
         val thm5 = (thm4 |> Drule.SPEC_ALL
                          |> rhsc
                          |> bump_rip (rhsc thm2)
                          |> run)
                    handle Conv.UNCHANGED => unchanged l
         val r = rhsc thm5
         val thm6 = Conv.QCONV STATE_CONV (mk_proj_exception r)
         val thm = Drule.LIST_CONJ [thm1, thm2, thm4, thm5, thm6]
      in
         MP_Next thm
         handle (e as HOL_ERR herr) =>
            if message_of herr = "different constructors" then
               MP_Next0 thm
            else raise e
      end
   fun x64_step_hex s =
      let
         val s = uppercase s
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
