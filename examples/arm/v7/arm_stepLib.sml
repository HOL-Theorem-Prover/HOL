structure arm_stepLib :> arm_stepLib =
struct

(* interactive use:
  app load ["arm_stepTheory", "armSyntax", "intLib", "wordsLib",
            "SatisfySimps"];
*)

open HolKernel boolLib bossLib;
open wordsTheory combinTheory updateLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory armTheory;
open arm_stepTheory;

structure Parse = struct
  open Parse
  val (Type,Term) = arm_stepTheory.arm_step_grammars
                      |> apsnd ParseExtras.grammar_loose_equality
                      |> parse_from_grammars

end

open Parse

(* ------------------------------------------------------------------------- *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();
val srw_ss = srw_ss() -* ["UPDATE_EQ", "UPDATE_APPLY_ID_RWT", "lift_disj_eq",
                          "lift_imp_disj"]
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]

fun SRW_TAC ssdl thl g = let
  val base = srw_ss
  open BasicProvers
  val ss = foldl (fn (ssd, ss) => ss ++ ssd) base ssdl
in
  markerLib.ABBRS_THEN
    (markerLib.mk_require_tac (fn thl => PRIM_STP_TAC (ss && thl) NO_TAC)) thl
end g;

infix \\

val op \\ = op Tactical.THEN;

val ERR = Feedback.mk_HOL_ERR "arm_stepLib";

val arm_step_trace = ref 0;
val arm_step_check = ref false;

val _ = Feedback.register_trace ("arm step", arm_step_trace, 3);
val _ = Feedback.register_btrace ("arm step check", arm_step_check);

(* ------------------------------------------------------------------------- *)
(* Facilitate evaluation                                                     *)
(* ------------------------------------------------------------------------- *)

fun mkfupdt thy ty fld =
    prim_mk_const{Thy = thy,
                  Name = TypeBasePure.mk_recordtype_fieldfupd
                           {tyname = ty, fieldname = fld}
                 }
fun mkselt thy ty fld =
    prim_mk_const{Thy = thy,
                  Name = TypeBasePure.mk_recordtype_fieldsel
                           {tyname = ty, fieldname = fld}
                 }


val mk_constants =
  List.concat o List.map (fn (thy, l) =>
    List.map (fn name => Term.prim_mk_const {Thy = thy, Name = name}) l);

(* Things to avoid evaluating *)

val restr_terms = mk_constants
  [("words",         ["word_div", "word_quot", "add_with_carry",
                      "bit_field_insert", "word_sign_extend"]),
   ("integer_word",  ["w2i", "i2w"]),
   ("arm_coretypes", ["signed_sat_q", "unsigned_sat_q",
                      "signed_sat", "unsigned_sat",
                      "encode_psr", "decode_psr", "count_leading_zeroes"])];

val _ = computeLib.del_consts (mk_constants
  [("arm_opsem",
    ["branch_write_pc", "bx_write_pc", "load_write_pc", "alu_write_pc",
     "branch_target_instr",
     "branch_exchange_instr",
     "branch_link_exchange_imm_instr",
     "branch_link_exchange_reg_instr",
     "null_check_if_thumbEE",
     "compare_branch_instr",
     "table_branch_byte_instr",
     "check_array_instr",
     "handler_branch_link_instr",
     "handler_branch_link_parameter_instr",
     "handler_branch_parameter_instr",
     "add_sub_instr",
     "data_processing_instr",
     "load_instr",
     "load_multiple_instr",
     "return_from_exception_instr",
     "saturating_add_subtract_instr",
     "signed_16_multiply_32_accumulate_instr",
     "signed_16x32_multiply_32_accumulate_instr",
     "signed_multiply_dual_instr",
     "saturate_instr", "saturate_16_instr",
     "branch_instruction", "data_processing_instruction",
     "load_store_instruction",
     "arm_instr"]),
    ("arm", ["arm_next"])]);

val _ = computeLib.add_funs
  (List.map (REWRITE_RULE [condT_set_q])
    [saturating_add_subtract_instr, signed_16_multiply_32_accumulate_instr,
     signed_16x32_multiply_32_accumulate_instr, signed_multiply_dual_instr,
     saturate_instr, saturate_16_instr] @
   [branch_write_pc, bx_write_pc, load_write_pc_def, alu_write_pc_def,
    null_check_if_thumbEE_def, branch_target_instr, branch_exchange_instr,
    branch_link_exchange_imm_instr, branch_link_exchange_reg_instr,
    arm_stepTheory.compare_branch_instr, table_branch_byte_instr,
    check_array_instr, handler_branch_link_instr,
    handler_branch_link_parameter_instr, handler_branch_parameter_instr,
    add_sub_instr, data_processing_instr, load_instr, load_multiple_instr,
    return_from_exception_instr, branch_instruction_def,
    data_processing_instruction_def, load_store_instruction_def, arm_instr_def,
    armTheory.arm_next_def]);

val WORD_EQ_ADD_LCANCEL_0 =
  simpLib.SIMP_PROVE (srw_ss ++wordsLib.WORD_ARITH_EQ_ss) []
     ``(v = v + w) <=> (w = 0w:'a word)``;

val word_add_sub2 = wordsLib.WORD_DECIDE ``(a + b) + -a = b : 'a word``
val word_add_sub3 = wordsLib.WORD_DECIDE ``a + b + -b = a : 'a word``
val word_add_sub4 = wordsLib.WORD_DECIDE ``a + -b + b = a : 'a word``
val word_add_sub5 = wordsLib.WORD_DECIDE ``a + -(a + -b) = b : 'a word``

local
  val rule = GSYM o ONCE_REWRITE_RULE [aligned_def]
in
  val aligned_con_thms2            = rule aligned_con_thms
  val aligned_con_plus4_thm2       = rule aligned_con_plus4_thm
  val aligned_con_shift_thms2      = rule aligned_con_shift_thms
  val aligned_con_rrx_thms2        = rule aligned_con_rrx_thms
  val aligned_and_aligned_bx_thms2 = rule aligned_and_aligned_bx_thms
  val aligned_and_aligned_bx_thms2 = rule aligned_and_aligned_bx_thms
  val aligned_and_aligned_bx_rrx2  = rule aligned_and_aligned_bx_rrx
  val aligned_rm_thms2             = rule aligned_rm_thms
  val aligned_shift_rm_thms2       = rule aligned_shift_rm_thms
  val aligned_rrx_rm_thms2         = rule aligned_rrx_rm_thms
  val aligned_aligned2             = aligned_aligned
                                       |> CONJUNCTS
                                       |> Lib.C (curry List.take) 2
                                       |> LIST_CONJ
                                       |> rule
end;

val inst_type2  = Thm.INST_TYPE [Type.alpha |-> ``:2``];
val inst_type32 = Thm.INST_TYPE [Type.alpha |-> ``:32``];

fun bitwise_clauses f thm =
  List.drop (thm |> f |> Drule.SPEC_ALL |> Drule.CONJUNCTS,2)
    |> Drule.LIST_CONJ;

val _ = computeLib.add_funs
  [align_1, align_2_align_4, align_bits, (* align_neq, *) align_aligned,
   aligned_align_thms, aligned_align_thms2, align2_add_times2,
   aligned_rm_thms, aligned_rm_thms2, aligned_align_rm_thms,
   aligned_shift_rm_thms, aligned_shift_rm_thms2, aligned_align_shift_rm_thms,
   aligned_rrx_rm_thms, aligned_rrx_rm_thms2, aligned_align_rrx_rm_thms,
   aligned_align, aligned_sum, align_bits_sum, aligned_0_thms,
   aligned_pair_thms, aligned_shift_pair_thms, aligned_rrx_pair_thms,
   aligned_aligned, aligned_aligned2,
   aligned_over_bitwise, aligned_aligned_add_with_carry,
   aligned_pc_pc, aligned_aligned_rsb, add_with_carry, add_with_carry0,
   aligned_aligned_shift_thms, aligned_aligned_shift_pc_thms,
   aligned_aligned_rrx, aligned_aligned_rrx_pc,
   aligned_con_thms, aligned_con_thms2,
   aligned_con_plus4_thm, aligned_con_plus4_thm2,
   aligned_con_shift_thms, aligned_con_shift_thms2,
   aligned_con_rrx_thms, aligned_con_rrx_thms2,
   align_bx_bit, aligned_bx_branch, align_ldr_lsl,
   aligned_bx_1comp, aligned_bx_2comp,
   aligned_bx_and, aligned_bx_eor, aligned_bx_orr,
   aligned_bx_add_with_carry, aligned_bx_add_sub,
   aligned_bx_add_with_carry_pair, aligned_bx_add_pair,
   aligned_bx_pair_shift_thms,
   aligned_bx_1comp_pc, aligned_bx_and_pc, aligned_bx_eor_pc,
   aligned_bx_orr_pc, aligned_bx_bic_pc, aligned_bx_add_with_carry_pc,
   aligned_bx_add_with_carry_pair_pc, aligned_bx_add_sub_pc,
   aligned_bx_add_with_carry_literal_pc,
   aligned_bx_rrx_pair, aligned_bx_add_with_carry_rrx_pair,
   aligned_bx_add_sub_rrx_pc, aligned_and_aligned_bx_rrx,
   aligned_and_aligned_bx_rrx2,  aligned_bx_and_aligned_add_with_carry_rrx,
   aligned_bx_and_aligned_rrx, aligned_and_aligned_bx_rrx,
   aligned_bx_and_pc |> CONJUNCT2 |> ONCE_REWRITE_RULE [WORD_AND_COMM],
   aligned_bx_eor_pc |> CONJUNCT2 |> ONCE_REWRITE_RULE [WORD_XOR_COMM],
   aligned_bx_orr_pc |> CONJUNCT2 |> ONCE_REWRITE_RULE [WORD_OR_COMM],
   aligned_and_aligned_bx_thms, aligned_and_aligned_bx_thms2,
   aligned_bx_and_aligned_thms, IT_concat, good_mode, good_it, divisor_neq_zero,
   neq_pc_plus4, neq_pc_plus4_t2, neq_pc_plus4_plus, aligned_over_memread,
   aligned_bx_aligned_bx, aligned_concat, aligned_bx_concat,
   it_mode_concat, it_con_thm,
   word_add_sub2, word_add_sub3, word_add_sub4, word_add_sub5,
   WORD_ADD_RINV, WORD_NEG_NEG, WORD_ADD_0, UPDATE_ID_o,
   wordsLib.WORD_ARITH_CONV ``~(n2w n + -a) : word32``,
   wordsLib.WORD_ARITH_CONV ``~-a : word32``,
   wordsLib.WORD_ARITH_CONV ``a + ~a + 1w : word32``,
   extract_of_double_word, encode_psr_bit, encode_psr_bits,
   Q.ISPEC `IS_SOME:'a option -> bool` COND_RAND,
   Q.ISPEC `FST:'a # 'b -> 'a` COND_RAND,
   Q.ISPEC `SND:'a # 'b -> 'b` COND_RAND,
   Q.ISPEC `ARMpsr_N` COND_RAND,
   Q.ISPEC `ARMpsr_Z` COND_RAND,
   Q.ISPEC `ARMpsr_C` COND_RAND,
   Q.ISPEC `ARMpsr_V` COND_RAND,
   Q.ISPEC `ARMpsr_Q` COND_RAND,
   Q.ISPEC `ARMpsr_IT` COND_RAND,
   Q.ISPEC `ARMpsr_J` COND_RAND,
   Q.ISPEC `ARMpsr_GE` COND_RAND,
   Q.ISPEC `ARMpsr_E` COND_RAND,
   Q.ISPEC `ARMpsr_A` COND_RAND,
   Q.ISPEC `ARMpsr_I` COND_RAND,
   Q.ISPEC `ARMpsr_F` COND_RAND,
   Q.ISPEC `ARMpsr_T` COND_RAND,
   Q.ISPEC `ARMpsr_IT_fupd f` COND_RAND,
   error_option_case_COND_RAND, COND_RATOR,
   FST_ADD_WITH_CARRY,
   DECIDE ``if b then b else T``,
   DECIDE ``~((n <=> if z then v else ~n) /\ ~z)``,
   DECIDE ``n <=/=> ~n``,
   DECIDE ``~((z /\ c) /\ ~z)``,
   WORD_ADD_ASSOC |> Q.SPECL [`v`,`n2w n`,`n2w m`] |> GSYM |> inst_type32,
   pairTheory.FST_PAIR_MAP, pairTheory.SND_PAIR_MAP,
   bitwise_clauses inst_type32 WORD_AND_CLAUSES,
   bitwise_clauses inst_type32 WORD_XOR_CLAUSES,
   bitwise_clauses inst_type32 WORD_OR_CLAUSES,
   inst_type32 WORD_AND_COMP,
   inst_type32 WORD_EQ_ADD_LCANCEL,
   inst_type32 WORD_EQ_ADD_RCANCEL,
   inst_type32 WORD_EQ_ADD_LCANCEL_0,
   inst_type32 WORD_ADD_INV_0_EQ,
   inst_type32 WORD_ADD_LINV];

(* ------------------------------------------------------------------------- *)

val lowercase = String.map Char.toLower
val rhsc = boolSyntax.rhs o Thm.concl;
val eval = rhsc o bossLib.EVAL;
fun apply_conv conv = rhsc o (Conv.QCONV conv);
val restr_eval = apply_conv (computeLib.RESTR_EVAL_CONV restr_terms);
val dest_strip = armSyntax.dest_strip;

fun dest_arm_state_updates tm =
 (case dest_strip tm
  of (s, [a,b]) => (s, a) :: dest_arm_state_updates b
   | _ => []) handle HOL_ERR _ => [];

fun mk_test (c,l,v) = boolSyntax.mk_eq (Term.list_mk_comb (c,l),v)
fun mk_arm_const s = Term.prim_mk_const {Name = s, Thy = "arm_step"}

local
  val I_flags_fupd = Term.inst [Type.alpha |-> “:ARMpsr”] combinSyntax.I_tm
  val read_status_tm = mk_arm_const "ARM_READ_STATUS"
  fun mk_read_status (t,s) =
        Term.list_mk_comb (read_status_tm,[t,s])
        handle HOL_ERR _ => raise ERR "mk_read_status" ""
in
  fun set_flags state cond pass =
    let fun test_flag t = mk_read_status (t,state)
        val flag_n = test_flag “arm_step$psrN”
        val flag_z = test_flag “arm_step$psrZ”
        val flag_c = test_flag “arm_step$psrC”
        val flag_v = test_flag “arm_step$psrV”
        val not_flag_n = mk_neg flag_n
        val not_flag_z = mk_neg flag_z
        val not_flag_c = mk_neg flag_c
        val not_flag_v = mk_neg flag_v
        val mkfupd = mkfupdt "arm_coretypes" "ARMpsr"
    in
      case (Arbnum.toInt (wordsLib.dest_word_literal cond),pass)
      of (0,true)   => (“^(mkfupd "Z") (K T)”,flag_z)
       | (0,false)  => (“^(mkfupd "Z") (K F)”,not_flag_z)
       | (1,true)   => (“^(mkfupd "Z") (K F)”,not_flag_z)
       | (1,false)  => (“^(mkfupd "Z") (K T)”,flag_z)
       | (2,true)   => (“^(mkfupd "C") (K T)”,flag_c)
       | (2,false)  => (“^(mkfupd "C") (K F)”,not_flag_c)
       | (3,true)   => (“^(mkfupd "C") (K F)”,not_flag_c)
       | (3,false)  => (“^(mkfupd "C") (K T)”,flag_c)
       | (4,true)   => (“^(mkfupd "N") (K T)”,flag_n)
       | (4,false)  => (“^(mkfupd "N") (K F)”,not_flag_n)
       | (5,true)   => (“^(mkfupd "N") (K F)”,not_flag_n)
       | (5,false)  => (“^(mkfupd "N") (K T)”,flag_n)
       | (6,true)   => (“^(mkfupd "V") (K T)”,flag_v)
       | (6,false)  => (“^(mkfupd "V") (K F)”,not_flag_v)
       | (7,true)   => (“^(mkfupd "V") (K F)”,not_flag_v)
       | (7,false)  => (“^(mkfupd "V") (K T)”,flag_v)
       | (8,true)   => (“^(mkfupd "C") (K T) o ^(mkfupd "Z") (K F)”,
                          mk_conj (flag_c,not_flag_z))
       | (8,false)  => (“^(mkfupd "C") (K(^flag_z /\ ^flag_c))”,
                          mk_neg (mk_conj (flag_c,not_flag_z)))
       | (9,true)   => (“^(mkfupd "C") (K(^flag_z /\ ^flag_c))”,
                          mk_neg (mk_conj (flag_c,not_flag_z)))
       | (9,false)  => (“^(mkfupd "C") (K T) o ^(mkfupd "Z") (K F)”,
                          mk_conj (flag_c,not_flag_z))
       | (10,true)  => (“^(mkfupd "V") (K ^flag_n)”, mk_eq (flag_n,flag_v))
       | (10,false) => (“^(mkfupd "V") (K (~^flag_n))”,
                          mk_neg (mk_eq (flag_n,flag_v)))
       | (11,true)  => (“^(mkfupd "V") (K (~^flag_n))”,
                          mk_neg (mk_eq (flag_n,flag_v)))
       | (11,false) => (“^(mkfupd "V") (K ^flag_n)”, mk_eq (flag_n,flag_v))
       | (12,true)  => (“^(mkfupd "V") (K ^flag_n) o ^(mkfupd "Z") (K F)”,
                          mk_conj (mk_eq (flag_n,flag_v),not_flag_z))
       | (12,false) => (“^(mkfupd "V")
                            (K (if ^flag_z then ^flag_v else ~^flag_n))”,
                          mk_neg (mk_conj (mk_eq (flag_n,flag_v),not_flag_z)))
       | (13,true)  => (“^(mkfupd "V")
                            (K (if ^flag_z then ^flag_v else ~^flag_n))”,
                          mk_neg (mk_conj (mk_eq (flag_n,flag_v),not_flag_z)))
       | (13,false) => (“^(mkfupd "V") (K ^flag_n) o ^(mkfupd "Z") (K F)”,
                          mk_conj (mk_eq (flag_n,flag_v),not_flag_z))
       | (14,true)  => (I_flags_fupd,T)
       | (15,true)  => (I_flags_fupd,T)
       | _ => raise ERR "set_flags" "Invalid pass status."
    end
end;

datatype endian = BigEndian | LittleEndian;

datatype mode = Usr | Fiq | Irq | Svc | Mon | Abt | Und | Sys;

datatype arch = ARMv4 | ARMv4T
              | ARMv5T | ARMv5TE
              | ARMv6 | ARMv6K | ARMv6T2
              | ARMv7_A | ARMv7_R;

type options =
  { arch : arch, mode : mode, endian : endian,
    pass : bool, thumb : bool, thumbee : bool, itblock : int };

fun endian_to_term BigEndian = boolSyntax.T
  | endian_to_term LittleEndian = boolSyntax.F;

fun mode_to_term m = Parse.Term
  (case m
   of Usr => `0b10000w:word5`
    | Fiq => `0b10001w:word5`
    | Irq => `0b10010w:word5`
    | Svc => `0b10011w:word5`
    | Mon => `0b10110w:word5`
    | Abt => `0b10111w:word5`
    | Und => `0b10111w:word5`
    | Sys => `0b11111w:word5`);

fun arch_to_term s = Parse.Term
 (case s
  of ARMv4   => `ARMv4`
   | ARMv4T  => `ARMv4T`
   | ARMv5T  => `ARMv5T`
   | ARMv5TE => `ARMv5TE`
   | ARMv6   => `ARMv6`
   | ARMv6K  => `ARMv6K`
   | ARMv6T2 => `ARMv6T2`
   | ARMv7_A => `ARMv7_A`
   | ARMv7_R => `ARMv7_R`);

fun arch_version s =
  case s
  of ARMv4   => 4
   | ARMv4T  => 4
   | ARMv5T  => 5
   | ARMv5TE => 5
   | ARMv6   => 6
   | ARMv6K  => 6
   | ARMv6T2 => 6
   | ARMv7_A => 7
   | ARMv7_R => 7;

fun thumb2_support a = Lib.mem a [ARMv6T2, ARMv7_A, ARMv7_R]

local
  val arch_tm                = mk_arm_const "ARM_ARCH"
  val extensions_tm          = mk_arm_const "ARM_EXTENSIONS"
  val unaligned_support_tm   = mk_arm_const "ARM_UNALIGNED_SUPPORT"
  val read_event_register_tm = mk_arm_const "ARM_READ_EVENT_REGISTER"
  val read_interrupt_wait_tm = mk_arm_const "ARM_READ_INTERRUPT_WAIT"
  val read_sctlr_tm          = mk_arm_const "ARM_READ_SCTLR"
  val read_status_tm         = mk_arm_const "ARM_READ_STATUS"
  val read_it_tm             = mk_arm_const "ARM_READ_IT"
  val ALIGN_CONV = SIMP_CONV srw_ss [aligned_n2w, align_n2w]
  val ALIGN_ss = simpLib.std_conv_ss
        {conv = ALIGN_CONV, name = "ALIGN_CONV",
         pats = [``arm_coretypes$aligned (n2w a:'a word,n)``]}
  fun cond_mk_test c f l =
        [case c
         of SOME b => mk_test (f,l,b)
          | NONE => boolSyntax.T]
in
  fun mk_precondition
        the_state arch itstate ext thumbee thumb endian flags regs memory =
        apply_conv
         (SIMP_CONV (pure_ss++ALIGN_ss++boolSimps.CONJ_ss)
            [GSYM CONJ_ASSOC, aligned_thm,
             NOT_CLAUSES, AND_CLAUSES, REFL_CLAUSE, COND_CLAUSES,
             ARM_READ_CPSR_def, ARM_MODE_def, ARM_READ_STATUS_def,
             ARM_READ_IT_def])
         (list_mk_conj
          ([mk_test (arch_tm,[the_state],arch),
            mk_test (extensions_tm,[the_state], ext),
            mk_test (unaligned_support_tm,[the_state],T),
            mk_test (read_event_register_tm,[the_state],T),
            mk_test (read_interrupt_wait_tm,[the_state],F),
            mk_test (read_sctlr_tm,[``arm_step$sctlrV``,the_state],F),
            mk_test (read_sctlr_tm,[``arm_step$sctlrA``,the_state],T),
            mk_test (read_sctlr_tm,[``arm_step$sctlrU``,the_state],F)] @
            cond_mk_test itstate read_it_tm [the_state] @
            cond_mk_test endian  read_status_tm [``arm_step$psrE``,the_state] @
           [mk_test (read_status_tm,[``arm_step$psrJ``,the_state],thumbee),
            mk_test (read_status_tm,[``arm_step$psrT``,the_state],thumb),
            flags, regs, memory]))
end;

fun list_dest_o t =
let
  fun F t a = let val (f,g) = combinSyntax.dest_o t in
                F g (f :: a)
              end handle HOL_ERR _ => (t :: a)
in
  List.rev (F t [])
end;

fun butlastn (l,n) = List.take (l, List.length l - n);

fun list_mk_o l = List.foldr combinSyntax.mk_o (List.last l) (butlastn (l,1));

val dropn_o = total (fn (t,n) => list_mk_o (butlastn (list_dest_o t, n)));

fun find_arm_state_updates upd tm =
    let val cnm = TypeBasePure.mk_recordtype_fieldfupd
                    {tyname = "arm_state",fieldname = upd}
    in
      case List.find (fn (s,_) => s = cnm) (dest_arm_state_updates tm) of
          SOME (_,t) => t
        | _ => raise ERR "find_arm_state_updates" "no matching updates"
    end

fun arm_state_standard_updates tm =
let
  val upd = dest_arm_state_updates tm
  fun mkfupdnm s = TypeBasePure.mk_recordtype_fieldfupd
                     {tyname = "arm_state", fieldname = s}
  fun pl s0 = let val s1 = mkfupdnm s0 in Lib.pluck (fn (s2,_) => s2 = s1) end
  fun trypl s0 =
      let val s1 = mkfupdnm s0
      in Lib.trypluck' (fn (s2,u) => if s1 = s2 then SOME u else NONE)
      end
  val (reg,upd) = pl "registers" upd
  val (psr,upd) = pl "psrs" upd
  val (mem,upd) = trypl "memory" upd
  val (evt,upd) = pl "event_register" upd
  val (wfi,upd) = pl "interrupt_wait" upd
  val (acc,upd) = trypl "accesses" upd
  val (mon,upd) = trypl "monitors" upd
in
  (snd reg, snd psr, mem, snd evt, snd wfi, acc, mon, upd)
end;

local
  val mode_tm = mk_arm_const "ARM_MODE"
  val registers_tm  = mkselt "arm_seq_monad" "arm_state" "registers"

  val ALIGN_EQ_ss = simpLib.merge_ss
    [simpLib.rewrites [WORD_NEG_NEG, align_relative_thm,
                       GSYM aligned_def, GSYM aligned_248],
     simpLib.std_conv_ss
      {conv = Conv.CHANGED_CONV wordsLib.WORD_EVAL_CONV,
       name = "WORD_EVAL_CONV", pats = [``a = b : word32``]}]

  val arm_reg_updates =
        List.map combinSyntax.dest_update o list_dest_o o
        find_arm_state_updates "registers"

  fun mk_reg_mode_updates (the_state,state') =
        let val updates = arm_reg_updates state' handle HOL_ERR _ => []
            fun mk_reg_test (r,v) =
                 let val c = total (find_term is_cond) v
                     val t = mk_test (registers_tm, [the_state,r], v)
                 in
                   case c
                     of SOME tm =>
                          let val (b,_,_) = dest_cond tm
                              val c2 = total (find_term is_cond) b
                          in
                            case c2
                              of SOME tm2 =>
                                   let val (b2,_,_) = dest_cond tm2 in
                                     list_mk_conj [b2,b,t]
                                   end
                               | NONE => mk_conj (b,t)
                          end
                      | NONE => t
                 end
            val tms = List.map mk_reg_test updates
        in
          List.map (apply_conv
            (SIMP_CONV (std_ss++boolSimps.CONJ_ss++ALIGN_EQ_ss) [])) tms
        end

  val arm_psrs_updates =
        List.map combinSyntax.dest_update o list_dest_o o
        find_arm_state_updates "psrs"

  fun mk_psrs_updates (the_state,state') =
        let val updates = arm_psrs_updates state' in
          case List.find
                 (fn tm => not (term_eq ``(0n,arm_coretypes$CPSR)`` (fst tm)))
                 updates
            of SOME (t,v) =>
                 (case total (find_term is_cond) v
                     of SOME tm => let val (b,_,_) = dest_cond tm in [b] end
                      | NONE => [])
             | NONE => []
        end
in
  fun mk_reg_pre (the_state,M,state') =
        let val tmode = mk_test (mode_tm, [the_state], M)
            val regs = mk_reg_mode_updates (the_state,state')
            val psrs = mk_psrs_updates (the_state,state')
            val mregs = list_mk_conj (tmode :: regs @ psrs)
        in
          (List.length regs, apply_conv (SIMP_CONV (std_ss++boolSimps.CONJ_ss)
             [GSYM word_sub_def]) mregs)
        end
end;

val aligned_bx_tm = Term.prim_mk_const {Name = "aligned_bx", Thy = "arm_step"}

fun mk_aligned_bx (w,n:term) =
  Term.mk_comb
    (Term.inst [Type.alpha |-> wordsSyntax.dest_word_type (Term.type_of w)]
       aligned_bx_tm, w)
  handle HOL_ERR _ => raise ERR "mk_aligned_bx" "";

fun concat_bytes l =
let val _ = List.length l = 4 orelse raise ERR "concat_bytes" "" in
  List.foldl wordsSyntax.mk_word_concat (hd l) (tl l)
end;

fun bits32 (n,h,l) =
  let val s = StringCvt.padLeft #"0" 32 (Arbnum.toBinString n)
      val ss = Substring.slice (Substring.full s, 31 - h, SOME (h + 1 - l))
  in
    Arbnum.fromBinString (Substring.string ss)
  end;

local
  val read_mem_tm = mkselt "arm_seq_monad" "arm_state" "memory"
  val read_reg_tm = mkselt "arm_seq_monad" "arm_state" "registers"
  val pc_tm = ``(0n,arm_coretypes$RName_PC)``
  fun mk_word32 x = wordsSyntax.mk_wordii (x,32)

  fun make_bytes t =
    if optionSyntax.is_some t then
      let val a = optionSyntax.dest_some t in
        List.tabulate (4, fn x => wordsSyntax.mk_word_add (a,mk_word32 x))
      end
    else if optionSyntax.is_none t then
      []
    else raise ERR "make_bytes" ""

  val I_mem = ``I : (FullAddress -> word8) -> (FullAddress -> word8)``

  (* a =+ if f d then d else 0w *)
  fun mk_conform_mem (f,a,d) =
        combinSyntax.mk_update (a, mk_cond (f d, d, ``0w:word8``))

  (* a =+ if GOOD_MODE ((4 >< 0) d) then d else d || 31w *)
  fun mk_good_mode_mem (a,d) =
        let val good = ``GOOD_MODE ((4 >< 0) ^d)`` in
          combinSyntax.mk_update
            (a, mk_cond (good, d,
                         wordsSyntax.mk_word_or (d,``31w:word8``)))
        end

  fun mk_aligned_the_mem (f:term -> term,s,l) =
        let val bytes = List.map (fn a => restr_eval
                               (list_mk_comb (read_mem_tm, [s,a]))) l
            val aliged_word = concat_bytes bytes
        in
          (1, mk_conform_mem (f,hd l,hd bytes), f aliged_word)
        end

  fun mk_good_it_mode_the_mem (s,l) =
        let val bytes = List.map (fn a => restr_eval
                               (list_mk_comb (read_mem_tm, [s,a]))) l
            val aliged_word = concat_bytes bytes
        in
          (3, list_mk_o
             [mk_good_mode_mem (hd l,hd bytes),
              mk_conform_mem
                 (fn d => ``(7 >< 2) ^d = 0w:word6``,
                  List.nth(l,1), List.nth(bytes,1)),
              mk_conform_mem
                 (fn d => ``(2 >< 1) ^d = 0w:word2``,
                  List.nth(l,3), List.nth(bytes,3))],
           ``GOOD_MODE ((4 >< 0) ^aliged_word) /\
             ((((15 >< 10) ^aliged_word):word6) @@
              (((26 >< 25) ^aliged_word):word2) = 0w:word8)``)
        end

  fun fold_mem f init l =
        List.foldl (fn (a,(n,tm1,tm2)) =>
                 let val (u,t) = f a in
                   if n = 0 then
                     (1,u,t)
                   else
                     (n + 1, combinSyntax.mk_o (u,tm1), mk_conj (t,tm2))
                 end) init l

  fun mk_memory_good (endian,arch,bx,s,aligns) =
        if optionSyntax.is_none bx then
          (0,I_mem,T)
        else
          let val bytes = make_bytes aligns
              val bytes = if endian = BigEndian then rev bytes else bytes
              val align_fn = if arch_version arch >= 5 then
                               Lib.C (Lib.curry mk_aligned_bx) ``4n``
                             else
                               Lib.C (Lib.curry armSyntax.mk_aligned) ``4n``
          in
            if term_eq (optionSyntax.dest_some bx) T then
              mk_aligned_the_mem (align_fn,s,bytes)
            else
              mk_good_it_mode_the_mem (s,bytes)
          end

  fun mk_memory_opc data_mem (s,endian,enc,opc) =
        let open wordsSyntax
            val (n,bytes) =
                   case fst (Term.dest_const enc)
                     of "Encoding_Thumb" =>
                           let val l = eval (armSyntax.mk_bytes (opc,``2n``))
                               val bytes = fst (listSyntax.dest_list l)
                           in
                             (1,if endian = BigEndian then rev bytes else bytes)
                           end
                      | "Encoding_Thumb2" =>
                           let val l = eval (armSyntax.mk_bytes (opc,``4n``)) in
                             (3,case fst (listSyntax.dest_list l)
                                of [a,b,c,d] => if endian = BigEndian then
                                                  [d,c,b,a]
                                                else
                                                  [c,d,a,b]
                                 | _ => raise ERR "mk_memory_opc" "")
                           end
                      | "Encoding_ARM" =>
                           let val l = eval (armSyntax.mk_bytes (opc,``4n``))
                               val bytes = fst (listSyntax.dest_list l)
                           in
                             (3,if endian = BigEndian then rev bytes else bytes)
                           end
                      | s =>
                         if s = "Encoding_Thumb" orelse
                            s = "Encoding_ThumbEE"
                         then
                           let val l = eval (armSyntax.mk_bytes (opc,``2n``))
                               val bytes = fst (listSyntax.dest_list l)
                           in
                             (1,if endian = BigEndian then rev bytes else bytes)
                           end
                         else
                           raise ERR "mk_memory_opc" "Invalid encoding."
            val registers = mk_comb (read_reg_tm,s)
            val pc = restr_eval (mk_comb (registers,pc_tm))
            val addrs = pc :: List.tabulate (n,
                                fn x => mk_word_add (pc,mk_word32 (x+1)))
        in
          fold_mem (fn (a,b) =>
                     (restr_eval (combinSyntax.mk_update (a,b)),
                      restr_eval (mk_test (read_mem_tm, [s,a], b))))
                   data_mem (Lib.zip addrs bytes)
        end
in
  fun mk_arm_memory state' endian arch enc opc bx aligns =
       let val data_mem = mk_memory_good (endian,arch,bx,state',aligns)
           val (nmem,tm1,tm2) = mk_memory_opc data_mem (state',endian,enc,opc)
       in
         (nmem, tm1,
          apply_conv
            (SIMP_CONV (std_ss++boolSimps.CONJ_ss)
               [GSYM word_sub_def, WORD_ADD_0]) tm2)
       end
end;

fun get_valuestate s tm =
    armSyntax.dest_valuestate tm handle HOL_ERR _ =>
      (let val e = armSyntax.dest_error tm handle HOL_ERR _ =>
        (if (!arm_step_trace div 2) mod 2 = 1 then Parse.print_term tm else ();
         raise ERR "eval_inst" ("Failed to fully evaluate " ^ s))
       in
         raise ERR "eval_inst" ("Error: " ^ stringSyntax.fromHOLstring e)
       end);

fun mk_inp instr =
  case lowercase instr
  of "rst"       => armSyntax.HW_Reset_tm
   | "reset"     => armSyntax.HW_Reset_tm
   | "fiq"       => armSyntax.HW_Fiq_tm
   | "fast"      => armSyntax.HW_Fiq_tm
   | "irq"       => armSyntax.HW_Irq_tm
   | "interrupt" => armSyntax.HW_Irq_tm
   | _           => armSyntax.NoInterrupt_tm

local
  val read_status_tm = mk_arm_const "ARM_READ_STATUS"
  val memfupd_tm = mkfupdt "arm_seq_monad" "arm_state" "memory"

  fun init s cpsr arch thumbee = let
        val ext = if thumbee then
                    ``{Extension_ThumbEE}``
                  else
                    ``{}:ARMextensions set``
      in
        (ext,
        ``^s with
         <| psrs updated_by ((0,CPSR) =+ ^cpsr);
            event_register updated_by (0 =+ T);
            interrupt_wait updated_by (0 =+ F);
            information :=
              <| arch := ^arch; unaligned_support := T; extensions := ^ext |>;
            coprocessors updated_by
              (Coprocessors_state_fupd (cp15_fupd (CP15reg_SCTLR_fupd
              (\sctlr. sctlr with <| V := F; A := T; U := F |>)))) |>``)
      end

  fun mk_bool b = if b then T else F

  fun mk_cpsr the_state flags_fupd itstate T ThumbEE E M = let
      val cpsr = case itstate
                 of SOME IT =>
                   ``^the_state.psrs (0,CPSR) with
                     <| IT := ^IT; J := ^ThumbEE; T := ^T; E := ^E; M := ^M |>``
                 | _ => ``^the_state.psrs (0,CPSR) with
                            <| J := F; T := ^T; E := ^E; M := ^M |>``
    in
      eval (mk_comb (flags_fupd, cpsr))
    end

  fun mk_irpt_cpsr the_state T ThumbEE M =
        ``^the_state.psrs (0,CPSR) with <| J := ^ThumbEE; T := ^T; M := ^M |>``

  fun decode_opcode IT arch thumb thumbee opc =
        if thumb then
          let val n = wordsSyntax.mk_wordi (bits32 (opc,15,0),16)
          in
            if bits32 (opc,31,29) = Arbnum.fromBinString "111" andalso
               bits32 (opc,28,27) <> Arbnum.zero
            then
              (armSyntax.Encoding_Thumb2_tm,
               eval (armSyntax.mk_thumb2_decode (arch_to_term arch,IT,
                     wordsSyntax.mk_wordi (bits32 (opc,31,16),16),n)))
            else if bits32 (opc,31,16) = Arbnum.zero then
              if thumbee then
                pairSyntax.dest_pair (eval
                  (armSyntax.mk_thumbee_decode (arch_to_term arch,IT,n)))
              else
                (armSyntax.Encoding_Thumb_tm,
                 eval (armSyntax.mk_thumb_decode (arch_to_term arch,IT,n)))
            else
              raise ERR "decode_opcode" "not a valid thumb op-code"
          end
        else
          let val n = wordsSyntax.mk_wordi (opc,32)
              val v4 = arch = ARMv4 orelse arch = ARMv4T
          in
            (armSyntax.Encoding_ARM_tm,
             eval (armSyntax.mk_arm_decode (mk_bool v4,n)))
          end

  val remove_white_space =
        String.translate
          (fn c => if Char.isSpace c then "" else Char.toString c)
in
  fun make_arm_state_and_pre the_state (opt:options) instr =
  let
    val arch = #arch opt
    val thumb = #thumb opt
    val thumbee = #thumbee opt
    val endian = #endian opt
    val _ = not (arch = ARMv4 andalso thumb) orelse
              raise ERR "make_arm_state_and_pre" "ARMv4 does not support Thumb."
    val Thumb = mk_bool thumb
    val ThumbEE = if thumbee then
                    if arch = ARMv7_A orelse arch = ARMv7_R then
                      boolSyntax.T
                    else
                      raise ERR "make_arm_state_and_pre"
                                "ThumbEE not supported by architecture."
                  else
                    boolSyntax.F
    val ii = ``<| proc := 0 |> : arm_coretypes$iiid``
    val T2 = thumb2_support arch
    val IT = wordsSyntax.mk_wordii (if T2 then #itblock opt else 0,8)
    val itstate = if T2 then SOME IT else NONE
    val M = mode_to_term (#mode opt)
    val E = endian_to_term endian
    val A = arch_to_term arch
    val inp = mk_inp instr
  in
    if mk_inp instr !~ armSyntax.NoInterrupt_tm then
      let
        val CPSR = mk_irpt_cpsr the_state Thumb ThumbEE M
        val (ext,state') = init the_state CPSR A thumbee
        val reg_pre = snd (mk_reg_pre (the_state,M,state'))
      in
        (0,0,state',
         mk_precondition the_state A NONE ext ThumbEE Thumb NONE
           boolSyntax.T reg_pre boolSyntax.T)
      end
    else
      let
        val opc = Arbnum.fromHexString (remove_white_space instr)
                    handle Option => raise ERR "make_arm_state_and_pre"
                                               "not a valid hex opcode"
        val (enc,dec) = decode_opcode IT arch thumb thumbee opc
        val (cond,instruction) = pairSyntax.dest_pair dec
        val (flags_fupd,flags_pre) = set_flags the_state cond (#pass opt)
        val CPSR = mk_cpsr the_state flags_fupd itstate Thumb ThumbEE E M
        val (ext,state') = init the_state CPSR A thumbee
        val opc = wordsSyntax.mk_wordi (opc,32)
        val opc' = if not thumb orelse arch_version arch >= 5
                   then opc else ``0w:word32``
        val npass = if #pass opt then F else T
        val tm = list_mk_comb (``arm_step$ARM_ALIGN_BX``,
                               [ii,npass,opc',enc,instruction,state'])
        val (bx,state') = get_valuestate "ARM_ALIGN_BX" (restr_eval tm)
        val tm = list_mk_comb (``arm_step$ARM_MEMORY_FOOTPRINT``,
                               [ii,npass,instruction,state'])
        val (aligns,state') =
               get_valuestate "ARM_MEMORY_FOOTPRINT" (restr_eval tm)
        val (nmem,memory_fupd,memory_pre) =
               mk_arm_memory state' endian arch enc opc bx aligns
        val state' = list_mk_comb (memfupd_tm, [memory_fupd,state'])
        val state' = restr_eval state'
        val state' = apply_conv (PURE_REWRITE_CONV [UPDATE_ID_o2]) state'
        val (nreg,reg_pre) = mk_reg_pre (the_state,M,state')
      in
        (nreg,nmem,state',
         mk_precondition the_state A itstate ext ThumbEE Thumb
           (SOME E) flags_pre reg_pre memory_pre)
      end
  end
end;

local
  val lem1 = DECIDE ``(a <=/=> b) ==> (a <=> ~b)``
  val lem2 = DECIDE ``(a <=/=> b) ==> (b <=> ~a)``
  val lem3 = ``(-1w * a:'a word) << 1 = -1w * (a << 1)``
                |> wordsLib.WORD_ARITH_CONV |> Drule.EQT_ELIM |> Drule.GEN_ALL
in
  fun prove_character P G = Q.prove(
    `!s. ^P s ==> (^G s = s)`,
    STRIP_TAC
      \\ PURE_REWRITE_TAC [ARM_ARCH_def, ARM_EXTENSIONS_def,
           ARM_UNALIGNED_SUPPORT_def, ARM_READ_EVENT_REGISTER_def,
           ARM_READ_INTERRUPT_WAIT_def, ARM_READ_SCTLR_def, ARM_READ_SCR_def,
           ARM_READ_TEEHBR_def]
      \\ Cases_on `s`
      \\ SIMP_TAC srw_ss
           [WORD_NOT, WORD_LEFT_ADD_DISTRIB, IT_concat0,
            aligned_concat, aligned_bx_concat, it_mode_concat]
      \\ STRIP_TAC
      \\ ASM_SIMP_TAC srw_ss [arm_state_component_equality,
           ARMinfo_component_equality, Coprocessors_component_equality,
           coproc_state_component_equality, CP15reg_component_equality,
           CP15sctlr_component_equality, ARMpsr_component_equality,
           optionTheory.option_CLAUSES, APPLY_UPDATE_ID, aligned_thm,
           aligned_n2w, align_n2w]
      \\ ASM_SIMP_TAC srw_ss
           [align_relative_add_with_carry, lem3, APPLY_UPDATE_THM,
            WORD_NOT, WORD_LEFT_ADD_DISTRIB, UPDATE_APPLY_IMP_ID]
      \\ MATCH_MP_TAC UPDATE_APPLY_IMP_ID
      \\ SRW_TAC [] [ARMpsr_component_equality, lem1, lem2]
  )
end;

fun prove_comp_thm the_state P H G X = Q.prove(
  `^P ^the_state ==> (^H (^G ^the_state) = ^X)`,
  BETA_TAC \\ STRIP_TAC
    \\ PURE_REWRITE_TAC [arm_state_accfupds]
    \\ computeLib.RESTR_EVAL_TAC restr_terms
    \\ ASM_SIMP_TAC (srw_ss++boolSimps.CONJ_ss)
         [UPD11_SAME_KEY_AND_BASE, UPDATE_EQ, UPDATE_ID_o2, APPLY_UPDATE_THM,
          WORD_EQ_ADD_LCANCEL_0, align_aligned, align_aligned3]);

local
  val lem1 = trace ("metis",0) (METIS_PROVE [WORD_EQ_ADD_RCANCEL])
    ``(((state:arm_seq_monad$arm_state).memory p = x) ==>
         ((if p = a then x else state.memory a) = state.memory a)) /\
      ((state.memory (p + n) = x) ==>
         ((if p = a then x else state.memory (a + n)) = state.memory (a + n)))``

  val lem2 = (CONJ signed_sat_def unsigned_sat_def)
                |> SIMP_RULE std_ss [FUN_EQ_THM] |> GSYM

  val lem4 = intLib.COOPER_PROVE ``&a + &b >= &c:int = a + b >= c:num``
  val lem5 = intLib.COOPER_PROVE ``a - b >= 0i = a >= b``
  val lem6 = intLib.COOPER_PROVE ``&a >= &b:int = a >= b:num``

  val lem7 = ``(~a + n2w b : word32) = (n2w b - 1w) - a``
                 |> wordsLib.WORD_ARITH_CONV
                 |> Drule.EQT_ELIM |> bossLib.EVAL_RULE
                 |> REWRITE_RULE [GSYM word_sub_def] |> Drule.GEN_ALL
  val lem8 = intLib.ARITH_PROVE ``(a + b * 65536i) / 65536 = a / 65536 + b``
  val lem9 = ``arm_step$word4 (a,b,c,d)`` |> EVAL |> SYM |> GEN_ALL
  val lem10 = DECIDE ``~((a <=> b) /\ ~c) ==> ((if c then b else ~a) = b)``
  val lem11 = simpLib.SIMP_PROVE std_ss [COND_RAND]
                 ``(if b then align (x:word32,m) else align (x,n)) =
                   align (x,if b then m else n)``
  val lem12 = Q.prove(`word_modify (\i. COND (i = 0) T) (w:word32) =
                       (((31 >< 1) w):31 word) @@ (1w:bool[unit])`,
                    SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [])

  val align_rws = [lem1, lem7, aligned_thm, aligned_n2w, align_n2w,
     aligned_bitwise_thm, aligned_pc_thm, optionTheory.option_CLAUSES,
     WORD_SUB_LZERO, GSYM word_sub_def, UPDATE_ID_o2, it_mode_imp_thm,
     aligned_bx_concat |> Drule.SPEC_ALL |> Thm.EQ_IMP_RULE |> fst |> GEN_ALL,
     aligned_concat    |> Drule.SPEC_ALL |> Thm.EQ_IMP_RULE |> fst |> GEN_ALL]

  val record_rws =
    [GSYM ARM_READ_MEM_def, GSYM ARM_WRITE_MEM_def, GSYM ARM_WRITE_MEM_o,
     GSYM ARM_WRITE_MEM_READ_def, GSYM ARM_WRITE_MEM_WRITE_def,
     ARM_READ_REG_FROM_MODE, ARM_WRITE_REG_FROM_MODE,
     GSYM ARM_READ_REG_MODE, GSYM ARM_WRITE_REG_MODE,
     GSYM ARM_WRITE_REG_o, GSYM ARM_MODE_def,
     GSYM ARM_READ_IT_def, GSYM ARM_READ_GE_def,
     GSYM ARM_READ_CPSR_def, GSYM ARM_WRITE_CPSR_def,
     ARM_READ_SCTLR_def  |> SIMP_RULE srw_ss [] |> GSYM,
     ARM_READ_SCR_def    |> SIMP_RULE srw_ss [] |> GSYM,
     ARM_READ_TEEHBR_def |> SIMP_RULE srw_ss [] |> GSYM,
     GSYM ARM_READ_STATUS_def, GSYM ARM_READ_SCTLR_def, GSYM ARM_READ_SCR_def,
     GSYM ARM_READ_TEEHBR_def,
     GSYM ARM_READ_STATUS_SPSR_def, GSYM ARM_READ_MODE_SPSR_def,
     GSYM ARM_READ_IT_SPSR_def, GSYM ARM_READ_GE_SPSR_def,
     GSYM ARM_WAIT_FOR_EVENT_def, GSYM ARM_SEND_EVENT_def,
     GSYM ARM_WAIT_FOR_INTERRUPT_def,
     GSYM ARM_READ_SPSR_MODE, ARM_READ_SPSR_FROM_MODE,
     GSYM ARM_WRITE_SPSR_MODE, ARM_WRITE_SPSR_FROM_MODE,
     GSYM ARM_WRITE_PSR_o, ARM_WRITE_CPSR_o, ARM_WRITE_SPSR_o,
     CPSR_COMPONENTS_OF_UPDATES, MARK_AND_CLEAR_EXCLUSIVE, MONITORS_OF_UPDATES,
     FST_SHIFT_C, EXTRACT_ROR, SInt_0,
     integerTheory.INT_ADD_RID, integerTheory.INT_ADD_LID,
     integer_wordTheory.word_add_i2w_w2n,
     integer_wordTheory.word_sub_i2w_w2n,
     integer_wordTheory.word_add_i2w,
     integer_wordTheory.word_sub_i2w,
     GSYM integer_wordTheory.WORD_GEi, GSYM WORD_HS, WORD_EQ_SUB_ZERO,
     lem2, lem4, lem5, lem6, lem8, lem9, lem10]

  val updates_rws =
    [ARM_WRITE_CPSR, ARM_WRITE_SPSR,
     PSR_OF_UPDATES, REG_OF_UPDATES, MEM_OF_UPDATES,
     CPSR_COMPONENTS_OF_UPDATES, SPSR_COMPONENTS_OF_UPDATES,
     ARM_READ_STATUS_UPDATES, ARM_WRITE_SPSR_FROM_MODE,
     ARM_READ_UNCHANGED, ARM_WRITE_STATUS_Q,
     ARM_READ_CPSR_COMPONENT_UNCHANGED,
     COND_RATOR,
     Q.ISPEC `ARM_WRITE_CPSR` COND_RAND,
     Q.ISPEC `ARM_WRITE_IT n` COND_RAND,
     arm_bit_distinct, lem11, lem12]

  fun OFFSET_CONV tm =
    let
      val (l,r) = wordsSyntax.dest_word_add tm
      val (ll,lr) = wordsSyntax.dest_word_add l
    in
      if wordsSyntax.is_word_literal lr andalso
         wordsSyntax.is_word_literal r
      then
        (REWR_CONV (GSYM wordsTheory.WORD_ADD_ASSOC) THENC
         RAND_CONV wordsLib.WORD_EVAL_CONV) tm
      else
        raise ERR "OFFSET_CONV" ""
    end
in
  val OFFSET_ss = simpLib.merge_ss [simpLib.rewrites [wordsTheory.WORD_ADD_0],
                   simpLib.std_conv_ss
                     {conv = OFFSET_CONV, name = "OFFSET_CONV",
                      pats = [``a + n2w b + n2w c : word32``]}]

  val WORD_EQ_ss = simpLib.std_conv_ss
             {conv = wordsLib.word_EQ_CONV, name = "word_EQ_CONV",
              pats = [``n2w w = n2w y :'a word``]}

  val BFC_ss = simpLib.std_conv_ss
             {conv = wordsLib.WORD_EVAL_CONV, name = "WORD_EVAL_CONV",
              pats = [``words$word_modify f 0xFFFFFFFFw : word32``]}

  val ARM_ALIGN_ss = simpLib.merge_ss
                        [simpLib.rewrites align_rws, wordsLib.SIZES_ss,
                         numSimps.REDUCE_ss, SatisfySimps.SATISFY_ss]

  val ARM_RECORD_ss = simpLib.merge_ss
                        [simpLib.rewrites record_rws, WORD_EQ_ss,
                         boolSimps.CONJ_ss, numSimps.REDUCE_ss]

  val ARM_UPDATES_ss = simpLib.merge_ss
                        [simpLib.rewrites updates_rws,
                         OFFSET_ss, WORD_EQ_ss, BFC_ss]
end;

val SORT_PSR_UPDATES_CONV =
  updateLib.OVERRIDE_UPDATES_CONV ``:(num # PSRName) -> ARMpsr``
    (PURE_REWRITE_CONV
       [GSYM arm_coretypesTheory.PSRName2num_11,
        arm_coretypesTheory.PSRName2num_thm,
        pairTheory.PAIR_EQ, pairTheory.FST, pairTheory.SND]
     THENC numLib.REDUCE_CONV);

val SORT_REG_UPDATES_CONV =
  updateLib.OVERRIDE_UPDATES_CONV ``:(num # RName) -> word32``
    (PURE_REWRITE_CONV
       [GSYM arm_coretypesTheory.RName2num_11,
        arm_coretypesTheory.RName2num_thm,
        pairTheory.PAIR_EQ, pairTheory.FST, pairTheory.SND]
     THENC numLib.REDUCE_CONV);

val SORT_REG_UPDATES_RULE =
  Conv.CONV_RULE (Conv.RAND_CONV (Conv.RHS_CONV
    (Conv.ONCE_DEPTH_CONV SORT_PSR_UPDATES_CONV THENC
     Conv.ONCE_DEPTH_CONV SORT_REG_UPDATES_CONV)));

local
  val endian_options = List.map (List.map lowercase)
        [["le", "little-endian", "LittleEndian"],
         ["be", "big-endian", "BigEndian"]]

  val arch_options = List.map (List.map lowercase)
        [["v4", "ARMv4"],
         ["v4T", "ARMv4T"],
         ["v5", "v5T", "ARMv5", "ARMv5T"],
         ["v5TE", "ARMv5TE"],
         ["v6", "ARMv6"],
         ["v6K", "ARMv6K"],
         ["v6T2", "ARMv6T2"],
         ["v7", "v7_A", "v7-A", "ARMv7", "ARMv7_A", "ARMv7-A"],
         ["v7_R", "v7-R", "ARMv7_R", "ARMv7-R"]]

  val mode_options = List.map (List.map lowercase)
        [["Usr", "User"],
         ["Fiq"],
         ["Irq"],
         ["Svc", "Supervisor"],
         ["Mon", "Monitor"],
         ["Abt", "Abort"],
         ["Und", "Undefined"],
         ["Sys", "System"]]

  val pass_options =
        [["pass", "passed"],
         ["fail", "not-passed", "skip"]]

  val thumb_options =
        [["thumb","thumb2","16-bit","16"],
         ["arm","32-bit","32"]]

  val thumbee_options =
        [["thumbee","thumbx"]]

  fun find_pos P l =
        let fun tail [] n = n
              | tail (h::t) n = if P h then n else tail t (n + 1)
         in
           tail l 0
         end

  fun isDelim c = Char.isPunct c andalso (c <> #"-") andalso (c <> #":") orelse
                  Char.isSpace c

  val fromDec = Option.valOf o Int.fromString

  val empty_string_set = Redblackset.empty Int.compare

  fun process_option P g s d l f =
        let val (l,r) = List.partition P l
            val positions = Lib.mk_set (List.map g l)
            val result =
                  if null positions then d else
                  if List.length positions = 1 then
                    f (hd positions)
                  else
                    raise ERR "process_option"
                      ("More than one " ^ s ^ " option.")
        in
          (result,r)
        end

  fun process_opt opt = process_option (Lib.C Lib.mem (List.concat opt))
                          (fn option => find_pos (Lib.mem option) opt)

  val default_options =
    {arch = ARMv7_A, mode = Usr, endian = LittleEndian,
     pass = true, thumb = false, thumbee = false, itblock = 0}
in
  fun process_options s =
    let val l = Substring.tokens isDelim (Substring.full s)
        val l = List.map (lowercase o Substring.string) l
        val (endian,l) = process_opt endian_options "Endian"
                            (#endian default_options) l
                            (fn i => if i = 0 then LittleEndian else BigEndian)
        val (arch,l) = process_opt arch_options "Arch"
                            (#arch default_options) l
                            (fn i =>
                              case i
                                of 0 => ARMv4   | 1 => ARMv4T
                                 | 2 => ARMv5T  | 3 => ARMv5TE
                                 | 4 => ARMv6   | 5 => ARMv6K  | 6 => ARMv6T2
                                 | 7 => ARMv7_A | 8 => ARMv7_R
                                 | _ => raise ERR "process_options"
                                                  "Invalid Arch option.")
        val (mode,l) = process_opt mode_options "Mode"
                            (#mode default_options) l
                            (fn i =>
                              case i
                                of 0 => Usr | 1 => Fiq | 2 => Irq | 3 => Svc
                                 | 4 => Mon | 5 => Abt | 6 => Und | 7 => Sys
                                 | _ => raise ERR "process_options"
                                                  "Invalid Mode option.")
        val (pass,l) = process_opt pass_options "Pass"
                            (#pass default_options) l (fn i => i = 0)
        val (thumbee,l) = process_opt thumbee_options "ThumbEE"
                            (#thumbee default_options) l (fn i => i = 0)
        val (thumb,l) = process_opt thumb_options "Thumb"
                            thumbee l (fn i => i = 0)
        val (itblock,l) = process_option (String.isPrefix "it:")
                            (fn s => fromDec (String.extract (s,3,NONE)))
                            "IT block" (#itblock default_options) l I
    in
      if null l then
        {arch = arch, mode = mode, endian = endian, pass = pass,
         thumb = thumb, thumbee = thumb andalso thumbee, itblock = itblock}
      else
        raise ERR "process_options"
          ("Unrecognized option: " ^ String.concat (commafy l))
    end
end;

local
    val fupd_set =
        (DB.definitions "arm_coretypes" @
         DB.definitions "arm_seq_monad")
        |> List.map fst
        |> List.filter (String.isSuffix "_fupd")
        |> Redblackset.fromList String.compare
  fun is_fupd tm =
         case Lib.total Term.dest_const tm
         of SOME (s,_) => Redblackset.member (fupd_set,s)
          | NONE => false
in
  fun check_step thm =
      if !arm_step_check andalso
         Lib.can (HolKernel.find_term is_fupd) (concl thm)
      then
        (Parse.print_thm thm;
         print "\n";
         raise ERR "check_step" "Found record update!")
      else
        thm
end

local
  fun get_valuestate2 s tm = let
    val f = snd o get_valuestate s
  in
    case Lib.total boolSyntax.dest_cond tm
    of SOME (c,tm1,tm2) => [f tm1, f tm2]
     | NONE => [f tm]
  end
  val the_state = mk_var ("state",``:arm_seq_monad$arm_state``)
  fun mk_arm_next inp t = ``arm$arm_next <| proc := 0 |> ^inp ^t``
  fun some_update fupd v s =
        case v of SOME u => list_mk_comb (fupd, [u,s])
                | NONE => s
  fun maybe_dropn_o tm =
        if combinSyntax.is_update tm orelse combinSyntax.is_o tm then
          dropn_o (tm, 1)
        else
          SOME tm
  fun print_progress s = if !arm_step_trace mod 2 = 1 then
                           TextIO.print s
                         else
                           ()
  val mkfupdt = mkfupdt "arm_seq_monad" "arm_state"
  fun prove_comp_thms nreg nmem P G X =
    let
      val (reg,psr,mem,evt,wfi,acc,mon,_) = arm_state_standard_updates X
      val reg' = dropn_o (reg, nreg)
      val mem' = case mem of SOME m => dropn_o (m, nmem)
                           | NONE => mem
      val psr' = dropn_o (psr, 1)
      val evt' = maybe_dropn_o evt
      val wfi' = maybe_dropn_o wfi
      val h = some_update (mkfupdt "registers") reg' the_state
      val h = some_update (mkfupdt "memory") mem' h
      val h = some_update (mkfupdt "psrs") psr' h
      val h = some_update (mkfupdt "event_register") evt' h
      val h = some_update (mkfupdt "interrupt_wait") wfi' h
      val h = some_update (mkfupdt "accesses") acc h
      val h = some_update (mkfupdt "monitors") mon h
      val H = Term.mk_abs (the_state,h)
    in
      prove_comp_thm the_state P H G X handle HOL_ERR _ =>
        raise ERR "eval_inst" "Failed to prove composition theorem"
    end
in
  fun arm_step options instr =
  let
    val opt = process_options options
    val (nreg, nmem, s, pre) = make_arm_state_and_pre the_state opt instr
    val P = mk_abs (the_state,pre)
    val G = mk_abs (the_state,s)
    val character_thm = prove_character P G handle HOL_ERR _ =>
                          raise ERR "eval_inst"
                            "Failed to prove characteristic theorem"
    val init_state = mk_comb (mk_abs (the_state,s),the_state)
    val tm = mk_arm_next (mk_inp instr) init_state
    val _ = print_progress "Starting evaluation ...\n"
    val eval_thm = computeLib.RESTR_EVAL_CONV restr_terms tm
    val _ = print_progress "... finished evaluation.\n"
    val Xs = get_valuestate2 "next_arm" (rhsc eval_thm)
    val _ = print_progress "Starting composition proof(s) ...\n"
    val comp_thms = List.map (prove_comp_thms nreg nmem P G) Xs
    val _ = print_progress "... finished composition proof(s).\n"
    val next_thm = case comp_thms
                   of [comp_thm] =>
                       Conv.BETA_RULE (Drule.MATCH_MP arm_next_thm
                         (Drule.LIST_CONJ [character_thm,comp_thm,eval_thm]))
                    | [comp_thm1, comp_thm2] =>
                       Conv.BETA_RULE (Drule.MATCH_MP arm_next_thm2
                         (Drule.LIST_CONJ
                           [character_thm,comp_thm1,comp_thm2,eval_thm]))
                    | _ => raise ERR "arm_step"
                             "Unexpected number of composition theorems"
    val thm = next_thm |> SORT_REG_UPDATES_RULE
                       |> Drule.UNDISCH
                       |> SIMP_RULE (bool_ss++ARM_ALIGN_ss) [Thm.ASSUME pre]
                       |> Thm.DISCH pre
                       |> with_flag (Cond_rewr.stack_limit,50)
                            (SIMP_RULE (bool_ss++ARM_RECORD_ss) [])
                       |> Drule.UNDISCH
    val pre' = hd (fst (Thm.dest_thm thm))
  in
    thm |> with_flag (Cond_rewr.stack_limit,50)
             (SIMP_RULE (bool_ss++ARM_UPDATES_ss) [Thm.ASSUME pre'])
        |> Thm.DISCH pre'
        |> Thm.GEN the_state
        |> check_step
  end
end;

end

(*
open arm_encoderLib;
fun test opt s = arm_step opt (arm_encode_from_string s);
test "" "svc #4";
test "" "adds r1, r2";
test "" "ldrex r1,[r2]";

val test = arm_step "fiq";
val _ = test "0xE591F000"; (* ldr pc,[r1] *)
val _ = test "0xF8110A00"; (* rfeda r1 *)

Unsupported:
  all coprocessor instructions.

Unsupported:
  strex <rd>,<rt>,[<rn>{,#<imm>}]
  strexb <rd>,<rt>,[<rn>]
  strexh <rd>,<rt>,[<rn>]
  strexd <rd>,<rt>,<rt2>,[<rn>]

Unsupported:
  tbh [<rn>,<rn>,lsl #1]

Unsupported for version < 6 (may give unpredictable results):
  adc pc,pc,#<const>
  sbc pc,pc,#<const>
  rsc pc,pc,#<const>
  mvn pc,<rn>,<shift>
  adc pc,<rn>,<rn>{,<shift>}
  sbc pc,<rn>,<rn>{,<shift>}
  rsc pc,<rn>,<rn>{,<shift>}

Unsupported:
  ldr pc,[<rm>,+/-<rm>{,{shift}]{!}
  ldr pc,[pc,+/-<rm>{,{shift}]

when UInt rm in {1,2,3,5,6,7,9,10,11,13,14} for version = 4
 and UInt rm in {2,6,10,13} for version >= 5
*)
