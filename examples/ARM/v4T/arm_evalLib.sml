(* ========================================================================= *)
(* FILE          : arm_evalLib.sml                                           *)
(* DESCRIPTION   : Code for evaluating the I/O free ARM specification        *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006 - 2007                                               *)
(* ========================================================================= *)

structure arm_evalLib :> arm_evalLib =
struct

(* interactive use:
  app load ["wordsLib", "computeLib", "pred_setSimps", "arm_evalTheory",
            "systemTheory", "assemblerML", "thumbTheory", "instructionSyntax"];
*)

open HolKernel boolLib bossLib;
open Q Parse computeLib combinTheory pairTheory wordsTheory wordsSyntax
     optionTheory rich_listTheory armTheory arm_evalTheory
     updateTheory systemTheory instructionTheory instructionSyntax assemblerML;

(* ------------------------------------------------------------------------- *)
(* Some conversions *)

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

fun NUM_ONLY_RULE n x =
  let val y = SPEC_ALL x
  in CONJ
      ((GEN_ALL o INST [n |-> `0`]) y)
      ((GEN_ALL o INST [n |-> `NUMERAL n`]) y)
  end;

fun WORD_ONLY_RULE n x =
  let val y = SPEC_ALL x
  in CONJ
      ((GEN_ALL o CONV_RULE (RHS_CONV EVAL_CONV) o INST [n |-> `0w`]) y)
      ((GEN_ALL o INST [n |-> `n2w (NUMERAL n)`]) y)
  end;

fun add_rws f rws =
let val cmp_set = f()
    val _ = add_thms rws cmp_set
in cmp_set end;

val ARM_ASSEMBLE_CONV = let open instructionTheory
  val compset = add_rws wordsLib.words_compset
       [transfer_options_accessors, transfer_options_updates_eq_literal, 
        transfer_options_accfupds, transfer_options_fupdfupds, 
        transfer_options_literal_11, transfer_options_fupdfupds_comp, 
        transfer_options_fupdcanon, transfer_options_fupdcanon_comp, 
        arm_instruction_case_def, thumb_instruction_case_def, 
        instruction_encode_def, thumb_encode_def,
        condition2num_thm, addr_mode1_case_def, 
        addr_mode2_case_def, addr_mode3_case_def, 
        msr_mode_case_def, condition_encode_def, 
        shift_encode_def, addr_mode1_encode_def, 
        addr_mode2_encode_def, addr_mode3_encode_def, 
        msr_mode_encode_def, msr_psr_encode_def, 
        options_encode_def, options_encode2_def, 
        data_proc_encode_def, K_THM, concat_thumb_def,
        SET_NZCV_def, SET_IFTM_def, mode_num_def, mode_case_def]
in
  computeLib.CBV_CONV compset
end;

val SET_BYTE_WORD_CONV =
let val compset = add_rws wordsLib.words_compset [SET_BYTE_def, SET_HALF_def]
    val _ = add_conv(``enc``, 1, ARM_ASSEMBLE_CONV) compset
    val _ = add_conv(``$#``, 2, ARM_ASSEMBLE_CONV) compset
in
  computeLib.CBV_CONV compset
end;

val arm_compset = wordsLib.words_compset();

val _ = add_conv(``SET_BYTE``, 3, SET_BYTE_WORD_CONV) arm_compset;
val _ = add_conv(``SET_HALF``, 3, SET_BYTE_WORD_CONV) arm_compset;

val _ = Lib.C add_thms arm_compset
  [FST,SND,listTheory.EL_compute,HD,TL,MAP,FILTER,LENGTH,ZIP,FOLDL,
   APPEND,APPEND_NIL,ELL_compute,LAST_CONS,listTheory.FRONT_CONS,
   GENLIST_compute,SNOC,FIRSTN_compute,K_THM,listTheory.NULL_DEF,
   register_EQ_register,num2register_thm,register2num_thm,
   mode_EQ_mode,mode2num_thm,mode_case_def,pairTheory.pair_case_thm,
   formats_case_def, psr_EQ_psr,psr2num_thm,
   iclass_EQ_iclass,iclass2num_thm,
   exceptions_EQ_exceptions,exceptions2num_thm,exceptions_case_def,
   num2exceptions_thm,exception2mode_def,
   num2condition_thm,condition2num_thm,condition_case_def,
   literal_case_THM, iclass_case_def, data_case_def, APPLY_UPDATE_THM,

   SET_NZC_def,NZCV_def,USER_def,mode_num_def,
   DECODE_IFTM_SET_NZCV,DECODE_NZCV_SET_NZCV,
   DECODE_IFTM_SET_IFTM,DECODE_NZCV_SET_IFTM,
   SET_NZCV_IDEM,SET_IFTM_IDEM,SET_THUMB_IFTM,SET_THUMB_NZCV,SET_IFTM_NZCV_SWP,
   DECODE_PSR_def,DECODE_MODE_def,DECODE_PSR_THM,
   CPSR_READ_def,CPSR_WRITE_def,SPSR_READ_def,SPSR_WRITE_def,
   CPSR_WRITE_n2w,SPSR_WRITE_n2w,mode_reg2num_def,mode2psr_def,
   REG_READ_def,REG_WRITE_def,INC_PC_def,FETCH_PC_def,
   word_modify_PSR,word_modify_PSR2,
   ALU_arith_def,ALU_logic_def,SUB_def,ADD_def,
   AND_def,EOR_def,ORR_def,ALU_def,
   LSL_def,LSR_def,ASR_def,ROR_def,
   WORD_ONLY_RULE `ireg` CONDITION_PASSED_def,CONDITION_PASSED2_def,
   DECODE_ARM_THM, SPEC `n2w i` THUMB_TO_ARM_def,

   ZIP,FOLDL,
   regs_accessors, regs_updates_eq_literal,
   regs_accfupds, regs_fupdfupds, regs_literal_11,
   regs_fupdfupds_comp, regs_fupdcanon,
   regs_fupdcanon_comp,
   interrupts_accessors, interrupts_updates_eq_literal,
   interrupts_accfupds, interrupts_fupdfupds, interrupts_literal_11,
   interrupts_fupdfupds_comp, interrupts_fupdcanon,
   interrupts_fupdcanon_comp,
   arm_state_accessors, arm_state_updates_eq_literal,
   arm_state_accfupds, arm_state_fupdfupds, arm_state_literal_11,
   arm_state_fupdfupds_comp, arm_state_fupdcanon,
   arm_state_fupdcanon_comp,
   transfer_options_accessors, transfer_options_updates_eq_literal,
   transfer_options_accfupds, transfer_options_fupdfupds,
   transfer_options_literal_11, transfer_options_fupdfupds_comp,
   transfer_options_fupdcanon, transfer_options_fupdcanon_comp,
   arm_input_accessors, arm_input_updates_eq_literal,
   arm_input_accfupds, arm_input_fupdfupds, arm_input_literal_11,
   arm_input_fupdfupds_comp, arm_input_fupdcanon,
   arm_input_fupdcanon_comp,
   arm_output_accessors, arm_output_updates_eq_literal,
   arm_output_accfupds, arm_output_fupdfupds, arm_output_literal_11,
   arm_output_fupdfupds_comp, arm_output_fupdcanon,
   arm_output_fupdcanon_comp,
   pipe_output_accessors, pipe_output_updates_eq_literal,
   pipe_output_accfupds, pipe_output_fupdfupds, pipe_output_literal_11,
   pipe_output_fupdfupds_comp, pipe_output_fupdcanon,
   pipe_output_fupdcanon_comp,
   coproc_accessors, coproc_updates_eq_literal,
   coproc_accfupds, coproc_fupdfupds,
   coproc_literal_11, coproc_fupdfupds_comp,
   coproc_fupdcanon, coproc_fupdcanon_comp,
   cp_input_accessors, cp_input_updates_eq_literal,
   cp_input_accfupds, cp_input_fupdfupds, cp_input_literal_11,
   cp_input_fupdfupds_comp, cp_input_fupdcanon,
   cp_input_fupdcanon_comp,
   cp_output_accessors, cp_output_updates_eq_literal,
   cp_output_accfupds, cp_output_fupdfupds, cp_output_literal_11,
   cp_output_fupdfupds_comp, cp_output_fupdcanon,
   cp_output_fupdcanon_comp,
   mem_output_accessors, mem_output_updates_eq_literal,
   mem_output_accfupds, mem_output_fupdfupds, mem_output_literal_11,
   mem_output_fupdfupds_comp, mem_output_fupdcanon,
   mem_output_fupdcanon_comp,

   regs_case_def,shift_case_def,transfers_case_def,

   DECODE_BRANCH_THM,DECODE_DATAP_THM,DECODE_MRS_THM,
   DECODE_MSR_THM,DECODE_LDR_STR_THM,DECODE_SWP_THM,
   DECODE_LDM_STM_THM,DECODE_MLA_MUL_THM,DECODE_LDC_STC_THM,
   DECODE_CDP_THM,DECODE_MRC_MCR_THM,
   DECODE_PSRD_def,
   IS_DP_IMMEDIATE_def, IS_DT_SHIFT_IMMEDIATE_def, IS_MSR_IMMEDIATE_def,
   IS_DTH_IMMEDIATE_def,

   cond_pass_enc_br, cond_pass_enc_coproc, cond_pass_enc_swp,
   cond_pass_enc_data_proc, cond_pass_enc_data_proc2, cond_pass_enc_data_proc3,
   cond_pass_enc_ldm_stm, cond_pass_enc_ldr_str, cond_pass_enc_ldrh_strh,
   cond_pass_enc_mla_mul, cond_pass_enc_mrs, cond_pass_enc_msr,
   cond_pass_enc_swi,

   decode_enc_br, decode_enc_coproc, decode_enc_swp,
   decode_enc_data_proc, decode_enc_data_proc2, decode_enc_data_proc3,
   decode_enc_ldm_stm, decode_enc_ldr_str, decode_enc_ldrh_strh,
   decode_enc_mla_mul, decode_enc_mrs, decode_enc_msr, decode_enc_swi,

   decode_br_enc, decode_ldc_stc_enc, decode_mrc_mcr_rd_enc,
   decode_data_proc_enc, decode_data_proc_enc2, decode_data_proc_enc3,
   decode_ldm_stm_enc, decode_ldr_str_enc, decode_ldrh_strh_enc,
   decode_mla_mul_enc, decode_mrs_enc, decode_msr_enc, decode_swp_enc,
   thumbTheory.thumb_to_arm_enc,

   immediate_enc, immediate_enc2, immediate_enc3, register_enc3,
   shift_immediate_enc, shift_immediate_enc2, shift_immediate_shift_register,
   shift_register_enc, shift_register_enc2,

   CARRY_def,GET_BYTE_def,GET_HALF_def,FORMAT_def,
   SHIFT_IMMEDIATE2_def,SHIFT_REGISTER2_def,
   NUM_ONLY_RULE `opnd2` SHIFT_IMMEDIATE_THM,
   NUM_ONLY_RULE `opnd2` SHIFT_REGISTER_THM,
   WORD_ONLY_RULE `opnd2` IMMEDIATE_def,
   ALU_multiply_def,ARITHMETIC_def,TEST_OR_COMP_def,UP_DOWN_def,
   ADDR_MODE1_def,ADDR_MODE2_def,ADDR_MODE3_def,ADDR_MODE4_def,ADDR_MODE5_def,
   REGISTER_LIST_THM,ADDRESS_LIST_def,FIRST_ADDRESS_def,WB_ADDRESS_def,
   LDM_LIST_def,STM_LIST_def,STM_DATA_def,

   EXCEPTION_def,BRANCH_def,BRANCH_EXCHANGE_def,DATA_PROCESSING_def,MRS_def,
   LDR_STR_def,MLA_MUL_def,SWP_def,MRC_def,MCR_OUT_def,MSR_def,LDM_STM_def,
   LDC_STC_def,LDRH_STRH_def,

   empty_memory_def,empty_registers_def,empty_psrs_def,
   SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) [] interrupt2exception_def,
   THE_DEF,IS_SOME_DEF,IS_NONE_EQ_NONE,NOT_IS_SOME_EQ_NONE,
   option_case_ID,option_case_SOME_ID,
   option_case_def,SOME_11,NOT_SOME_NONE,
   sumTheory.OUTL, sumTheory.OUTR, thumb_to_arm, NoTransfers_def,

   RUN_ARM, WRITE_MEM_def, READ_MEM_def,
   NEXT_ARM_def, OUT_ARM, INP_ARM1_def, INP_ARM2_def,
   NEXT_CP_def, OUT_CP_def, INP_CP1_def, INP_CP2_def,
   NEXT_MEM_def, OUT_MEM_def, INP_MEM_def,
   NEXT_NO_PIPE_def, OUT_NO_PIPE_def,
   (GEN_ALL o REWRITE_RULE [I_THM, NEXT_SYSTEM_def] o
    SPEC `((a,c,m,()),r,f,i)` o GEN `x` o SPEC_ALL o
    REWRITE_RULE [FUN_EQ_THM]) NEXT_1STAGE_def,

   memop_case_def, fcpTheory.index_comp, decode_cp_enc_coproc,
   decode_27_enc_coproc, thumbTheory.decode_27_enc_coproc_,
   decode_cdp_enc, decode_mrc_mcr_enc,

   APPLY_LUPDATE_THM, fcpTheory.FCP_APPLY_UPDATE_THM, ADDR30_def,
   MEM_WRITE_BYTE_def, MEM_WRITE_HALF_def, MEM_WRITE_WORD_def,
   MEM_WRITE_def, MEM_READ_def, BASIC_READ_def, BASIC_WRITE_def,
   NO_CP_def, NO_IRPTS_def];

val ARM_CONV = CBV_CONV arm_compset;
val ARM_RULE = CONV_RULE ARM_CONV;

val EVAL_UPDATE_CONV =
let val compset = add_rws reduceLib.num_compset
          [register_EQ_register,register2num_thm,
           psr_EQ_psr,psr2num_thm,APPLY_UPDATE_THM]
in
  computeLib.CBV_CONV compset
end;

val SORT_UPDATE_CONV =
let open arm_evalTheory fcpTheory
    val compset = add_rws wordsLib.words_compset
        [o_THM,register_EQ_register,register2num_thm,psr_EQ_psr,psr2num_thm,
         SYM Ua_def,UPDATE_EQ_RULE,Ua_RULE4,Ub_RULE4,Ua_RULE_PSR,Ub_RULE_PSR,
         SYM FUa_def,FCP_UPDATE_EQ_RULE,FUa_RULE,FUb_RULE,
         LENGTH,SUC_RULE JOIN,BUTFIRSTN_compute,APPEND,
         PURE_REWRITE_RULE [SYM Ua_def] UPDATE_LUPDATE,
         LUa_RULE,LUb_RULE,GSYM LUa_def]
in
  computeLib.CBV_CONV compset
    THENC PURE_REWRITE_CONV [Ua_def,Ub_def,FUa_def,FUb_def,LUa_def,LUb_def]
    THENC SIMP_CONV (srw_ss()) [UPDATE_APPLY_IMP_ID,APPLY_UPDATE_THM,
            FCP_UPDATE_IMP_ID,FCP_APPLY_UPDATE_THM,FCP_BETA]
end;

val FOLD_UPDATE_CONV =
let val compset = add_rws wordsLib.words_compset
      [SET_IFTM_def,SET_NZCV_def,FOLDL,APPLY_UPDATE_THM,
       psr_EQ_psr,psr2num_thm,mode_num_def,mode_case_def,
       register_EQ_register,register2num_thm,
       empty_registers_def,empty_memory_def,empty_psrs_def]
in
  computeLib.CBV_CONV compset THENC SORT_UPDATE_CONV
end;

val rhsc = rhs o concl;
val lhsc = lhs o concl;
val fdest_comb = fst o dest_comb;
val sdest_comb = snd o dest_comb;

fun printn s = print (s ^ "\n");

fun findi p l =
  let fun findin _ [] _ = NONE
        | findin p (h::t) n =
            if p h then SOME n else findin p t (n + 1)
  in
    findin p l 0
  end;

fun mapi f l =
  let fun m f [] i = []
        | m f (h::t) i = (f(i, h))::m f t (i + 1)
  in
    m f l 0
  end;

local
  fun take_dropn(l,n) a =
        if n = 0 then (rev a,l)
        else
          case l of
            [] => raise Subscript
          | (h::t) => take_dropn(t,n - 1) (h::a)
in
  fun take_drop(l,n) = take_dropn(l,n) []
end;

(* ------------------------------------------------------------------------- *)
(* Syntax *)

fun mk_word30 n = mk_n2w(numSyntax.mk_numeral n,``:30``);
fun mk_word32 n = mk_n2w(numSyntax.mk_numeral n,``:32``);

fun eval_word t = (numSyntax.dest_numeral o rhsc o FOLD_UPDATE_CONV o mk_w2n) t;

val subst_tm  = prim_mk_const{Name = "UPDATE", Thy = "combin"};
val lupdate_tm = prim_mk_const{Name = "|:", Thy = "update"};

fun mk_subst (a,b,m) =
   list_mk_comb(inst[alpha |-> type_of a,beta |-> type_of b] subst_tm,[a,b,m])
   handle HOL_ERR _ => raise ERR "mk_subst" "";

fun mk_lupdate (a,b,m) =
   list_mk_comb(inst[alpha |-> dim_of a,beta |-> listSyntax.eltype b]
     lupdate_tm,[a,b,m])
   handle HOL_ERR _ => raise ERR "mk_lupdate" "";

val dest_subst  = dest_triop subst_tm  (ERR "dest_word_slice" "");
val dest_lupdate = dest_triop lupdate_tm (ERR "dest_word_slice" "");

fun dest_psr t =
  case (strip_pair o rhsc o ARM_CONV) (mk_comb(``DECODE_PSR``, t)) of
    [n,z,c,v,i,f,t,m] =>
      {N = n, Z = z, C = c, V = v, I = i, F = f, T = t, M = m}
  | _ => raise ERR "dest_psr" "Failed to decode PSR";

datatype mode = USR | FIQ | IRQ | SVC | ABT | UND;

local
  val split_enum = (snd o strip_comb o sdest_comb o concl);
  val und_regs = split_enum armTheory.datatype_register;
  val (usr_regs,und_regs) = take_drop(und_regs,16)
  val (fiq_regs,und_regs) = take_drop(und_regs,7)
  val (irq_regs,und_regs) = take_drop(und_regs,2)
  val (svc_regs,und_regs) = take_drop(und_regs,2)
  val (abt_regs,und_regs) = take_drop(und_regs,2)

  fun mode2int m =
    case m of
      USR => 0
    | FIQ => 1
    | IRQ => 2
    | SVC => 3
    | ABT => 4
    | UND => 5;

  fun mode_compare(a,b) = Int.compare(mode2int a, mode2int b);

  fun rm_duplicates (h1::h2::l) =
        if h1 = h2 then rm_duplicates (h2::l)
        else h1::(rm_duplicates (h2::l))
    | rm_duplicates l = l;

  fun do_dest_subst_reg t a =
        let val (i,d,m) = dest_subst t in
          do_dest_subst_reg m
              (if isSome (List.find (fn a => term_eq (fst a) i) a) then a
               else ((i,d)::a))
        end handle HOL_ERR _ => (``ARB:unit``,t)::a;

  fun dest_subst_reg t = do_dest_subst_reg t []

  fun get_a_reg l rest r =
    case List.find (fn a => term_eq (fst a) r) l of
      SOME (x,y) => y
    | _ => (rhsc o EVAL_UPDATE_CONV o mk_comb) (rest,r);

  fun print_reg l rest r =
        (print_term r; print "="; print_term (get_a_reg l rest r); print "; ");

  fun print_usr_reg l rest n =
        if n <= 15 then
          print_reg l rest (List.nth(usr_regs,n))
        else ();

  fun print_fiq_reg l rest n =
        if 8 <= n andalso n <= 14 then
          (print_reg l rest (List.nth(fiq_regs,n - 8)))
        else ();

  fun print_irq_reg l rest n =
        if 12 < n andalso n < 15 then
          (print_reg l rest (List.nth(irq_regs,n - 13)))
        else ();

  fun print_svc_reg l rest n =
        if 12 < n andalso n < 15 then
          (print_reg l rest (List.nth(svc_regs,n - 13)))
        else ();

  fun print_abt_reg l rest n =
        if 12 < n andalso n < 15 then
          (print_reg l rest (List.nth(abt_regs,n - 13)))
        else ();

  fun print_und_reg l rest n =
        if 12 < n andalso n < 15 then
          (print_reg l rest (List.nth(und_regs,n - 13)))
        else ();

  fun mode2printer m =
    case m of
      USR => print_usr_reg
    | FIQ => print_fiq_reg
    | IRQ => print_irq_reg
    | SVC => print_svc_reg
    | ABT => print_abt_reg
    | UND => print_und_reg;

  val all_modes = [USR,FIQ,IRQ,SVC,ABT,UND];

  fun pprint_regs p t =
        let val regs = dest_subst_reg t
            val l = tl regs
            val rest = snd (hd regs)
        in
          for_se 0 15 (fn i =>
            let val newline =
               foldl (fn (m,e) => if p (i,m) then
                                    ((mode2printer m) l rest i; true)
                                  else e) false all_modes
            in
              if newline then print "\n" else ()
            end)
        end

  fun pprint_psrs p t =
        let val regs = dest_subst_reg t
            val l = tl regs
            val rest = snd (hd regs)
        in
          app (fn e => if p e then (print_reg l rest e; print "\n") else ())
            (split_enum armTheory.datatype_psr)
        end
in
  val print_all_regs = pprint_regs (K true);
  val print_usr_regs = pprint_regs (fn (i,m) => m = USR);
  val print_std_regs = pprint_regs (fn (i,m) => (m = USR) orelse (m = UND));
  fun print_regs l = pprint_regs (fn x => mem x l);

  val print_all_psrs = pprint_psrs (K true);
  val print_cpsr = pprint_psrs (term_eq ``CPSR``);
  val print_sprs = pprint_psrs (not o (term_eq ``CPSR``));

  fun get_reg r t =
  let val regs = dest_subst_reg t
      val l = tl regs
      val rest = snd (hd regs)
  in
    get_a_reg l rest r
  end

  val get_pc   = get_reg ``r15``;
  val get_cpsr = get_reg ``CPSR``;
end;

local
  fun do_dest_subst_mem t a =
       let val (i,d,m) = dest_lupdate t in
          do_dest_subst_mem m ((i,fst (listSyntax.dest_list d))::a)
       end handle HOL_ERR _ =>
         let val (i,d,m) = dest_subst t in
            do_dest_subst_mem m ((i,[d])::a)
         end handle HOL_ERR _ => (``ARB:unit``,[t])::(rev a);

  fun dest_subst_mem t = do_dest_subst_mem t []

  fun compute_bound (t, tl) =
  let open Arbnum
      val n4 = fromInt 4
      val l = eval_word t
  in
    (l, l + fromInt (Int.-(length tl, 1)))
  end;

  fun get_blocki bounds n =
    findi (fn (x,y) => Arbnum.<=(x, n) andalso Arbnum.<=(n, y)) bounds;

  fun get_mem_val blocks rest bounds n =
         case get_blocki bounds n of
           SOME i => List.nth(List.nth(blocks, i),
                       Arbnum.toInt (Arbnum.-(n, fst (List.nth(bounds, i)))))
         | NONE   => (rhsc o EVAL_UPDATE_CONV o mk_comb) (rest,mk_word30 n)
in
  fun read_mem_range m start n =
  let val dm = dest_subst_mem m
      val rest = hd (snd (hd (dm)))
      val bounds = map compute_bound (tl dm)
      val blocks = map snd (tl dm)
      val sa = Arbnum.div(start,Arbnum.fromInt 4)
      val f = get_mem_val blocks rest bounds
      val n4 = Arbnum.fromInt 4
  in
    List.tabulate(n, fn i => let val x = Arbnum.+(sa, Arbnum.fromInt i) in
                                 (Arbnum.*(x, n4), f x) end)
  end

  fun read_mem_block m n =
  let open Arbnum
      val dm = List.nth(dest_subst_mem m, n)
      val sa = eval_word (fst dm)
      val bl = snd dm
      val n4 = fromInt 4
      val addrs = List.tabulate(length bl, fn i => (sa + fromInt i) * n4)
  in
     zip addrs bl
  end
end;

local
  fun thumb_to_halves (n, t) =
  case total (match_term ``x # y``) t of
    SOME (l, []) =>
      let val x = case List.find (fn e => term_eq ``x:word16`` (#redex e)) l of
                    SOME r => #residue r
                  | NONE => ``x:word16``
          val y = case List.find (fn e => term_eq ``y:word16`` (#redex e)) l of
                    SOME r => #residue r
                  | NONE => ``x:word16``
      in
        [(n, x), (Arbnum.+(n, Arbnum.two), y)]
      end
  | _ => [(n, t)];
in
  fun to_halves l = List.concat (map thumb_to_halves l);
end;

fun mem_val_to_string(n, t) =
  "0x" ^ Arbnum.toHexString n ^ ": " ^
  (let val (l, r) = dest_comb t in
    if term_eq l ``enc`` orelse term_eq l ``enc_`` then
      dest_instruction (SOME n) r
    else
      term_to_string t
   end handle HOL_ERR _ => term_to_string t);

fun print_mem_range m (start, n) =
  app printn (map mem_val_to_string (to_halves (read_mem_range m start n)));

fun print_mem_block m n =
  app printn (map mem_val_to_string (to_halves (read_mem_block m n)))
  handle HOL_ERR _ => ();

(* ------------------------------------------------------------------------- *)

local
  fun add1 a = Data.add32 a Arbnum.one;
  fun add2 a = Data.add32 a Arbnum.two;
  val mul2 = Data.mul2;
  val div2 = Data.div2;
  val start = Arbnum.zero;

  fun label_table() =
    Polyhash.mkPolyTable
      (100,HOL_ERR {message = "Cannot find ARM label\n",
                    origin_function = "", origin_structure = "arm_evalLib"});

  fun advance_pc i n =
        case i of
          Data.Mark m                    => div2 m
        | Data.Code (Data.Instruction i) => add2 n
        | Data.Code (Data.Data n)        => add2 n
        | Data.Code (Data.Thumb i)       => add1 n
        | Data.Code (Data.ThumbData n)   => add1 n
        | Data.BranchS b                 => add2 n
        | Data.BranchN b                 => add2 n
        | Data.ThumbBranchS (c,l,s)      => if l then add2 n else add1 n
        | Data.ThumbBranchN (c,l,x)      => if l then add2 n else add1 n
        | Data.Label s                   => n;

  fun mk_links [] ht n = ()
    | mk_links (h::r) ht n =
       ((case h of
           Data.Label s =>
             Polyhash.insert ht (s, "0x" ^ Arbnum.toHexString (mul2 n))
         | _ => ());
        mk_links r ht (advance_pc h n));

  fun mk_link_table code =
        let val ht = label_table() in
          mk_links code ht start; ht
        end;

  fun x_label (Data.BranchS (c, l, s)) = (Data.BranchS (c, l, ""), s)
    | x_label (Data.ThumbBranchS (c, l, s)) = (Data.ThumbBranchS (c, l, ""), s)
    | x_label x = (x,"");

  fun br_to_term i ht n =
        let val (xi, label) = x_label i
            val s = assembler_to_string NONE xi NONE
            val address = Polyhash.find ht label
        in
          mk_instruction ("0x" ^ Arbnum.toHexString n ^ ": " ^ s ^ address)
        end;

  fun lcons h [] = [[h]]
    | lcons h (x::l) = (h::x)::l;

  fun assembler_to_term i ht n =
        case i of
          Data.Code c         => arm_to_term (validate_instruction c)
        | Data.BranchS b      => br_to_term i ht n
        | Data.ThumbBranchS b => br_to_term i ht n
        | Data.BranchN b      => arm_to_term (branch_to_arm b n)
        | Data.ThumbBranchN b => arm_to_term (branch_to_thumb b n)
        | _ => ``ARB:unit``;

  fun do_link m l n [] ht = zip m l
    | do_link m l n (h::r) ht =
        let val (nm, nl, nn) =
          case h of
            Data.Mark mk =>
               let val k = div2 mk in
                 if k = n then
                   (m, l, n)
                 else if null (hd l) then
                   (k::(tl m), l, k)
                 else
                   (k::m, []::l, k)
               end
          | Data.Label s => (m, l, n)
          | _ => (m, lcons (assembler_to_term h ht (mul2 n)) l, advance_pc h n)
        in
          do_link nm nl nn r ht
        end;

  fun do_links code =
        let val l = do_link [start] [[]] start code (mk_link_table code) in
          rev (map (fn (a,b) => (a,rev b)) l)
        end;

  fun check_aligned n = if Data.even n then () else
        raise ERR "check_aligned" "ARM instruction not word aligned";

  fun join_half_words a b =
      let val typA = type_of a and typB = type_of b in
        if typA = ``:word16`` then
          if typB = ``:word16`` then
            (rhsc o EVAL o inst [``:'c`` |-> ``:word32``])
               (mk_word_concat(b, a))
          else if typB = ``:thumb_instruction`` then
            subst [``a:word16`` |-> a,
                   ``b:thumb_instruction`` |-> b] ``a # enc_ b``
          else
            raise ERR "join_half_words" "not word aligned"
        else if typA = ``:thumb_instruction`` then
          if typB = ``:word16`` then
            subst [``a:thumb_instruction`` |-> a,
                   ``b:word16`` |-> b] ``enc_ a # b``
          else if typB = ``:thumb_instruction`` then
            subst [``a:thumb_instruction`` |-> a,
                   ``b:thumb_instruction`` |-> b] ``enc_ a # enc_ b``
          else
            raise ERR "join_half_words" "not word aligned"
        else
          raise ERR "join_half_words" "unknown type"
      end;

  fun do_form_words [] r n = rev r
    | do_form_words [a] r n =
        let val typA = type_of a in
          if typA = ``:word32`` then
            (check_aligned n; rev (a::r))
          else if typA = ``:arm_instruction`` then
            (check_aligned n; rev (mk_comb(``enc``, a)::r))
          else if typA = ``:thumb_instruction # thumb_instruction`` then
            let val (c, d) = dest_pair a in
              do_form_words [c, d] r n
            end
          else
            if Data.even n then
              rev ((join_half_words a ``UND_``)::r)
            else
              rev ((join_half_words ``UND_`` a)::r)
        end
    | do_form_words (a::b::t) r n =
        let val typA = type_of a in
          if typA = ``:word32`` then
            (check_aligned n;
             do_form_words (b::t) (a::r) (add2 n))
          else if typA = ``:arm_instruction`` then
            (check_aligned n;
             do_form_words (b::t) (mk_comb(``enc``, a)::r) (add2 n))
          else if typA = ``:thumb_instruction # thumb_instruction`` then
            let val (c, d) = dest_pair a in
              do_form_words (c::d::b::t) r n
            end
          else if type_of b = ``:thumb_instruction # thumb_instruction`` then
            let val (c, d) = dest_pair b in
              do_form_words (a::c::d::t) r n
            end
          else
            if Data.even n then
              do_form_words t ((join_half_words a b)::r) (add2 n)
            else
              do_form_words (b::t) ((join_half_words ``UND_`` a)::r) (add1 n)
        end;

  fun form_words(n, c) = (div2 n, do_form_words c [] n);

  fun assemble_assembler m a = let
    val l = map form_words (do_links a)
    val b = map (fn (m,c) => (mk_word30 m,listSyntax.mk_list(c,``:word32``))) l
    val t = foldl (fn ((a,c),t) => mk_lupdate(a,c,t)) m b
  in
    rhsc (SORT_UPDATE_CONV t)
  end
in
  fun assemble m file = assemble_assembler m (parse_arm file);
  fun list_assemble m l =
    let val nll = String.concat (map (fn s => s ^ "\n") l)
        val c = substring(nll,0,size nll - 1)
    in
      assemble_assembler m (string_to_code c)
    end;
  fun assemble1 m t = list_assemble m [t];
end;

val empty_memory = rhsc empty_memory_def
val empty_registers = rhsc empty_registers_def
val empty_psrs = rhsc empty_psrs_def

(* ------------------------------------------------------------------------- *)
(* Funtions for memory loading and saving *)

local
  fun bytes2num (b0,b1,b2,b3) =
    let open Arbnum
        val byte2num = fromInt o Char.ord o Byte.byteToChar
    in
      (byte2num b0) * (fromInt 16777216) + (byte2num b1) * (fromInt 65536) +
      (byte2num b2) * (fromInt 256) + byte2num b3
    end

  fun read_word (v,i) =
    let val l = Word8Vector.length v
        fun f i = if i < l then Word8Vector.sub(v,i) else 0wx0
    in
      mk_word32 (bytes2num (f i, f (i + 1), f (i + 2), f (i + 3)))
      (* could change order to do little-endian *)
    end
in
  fun load_mem fname skip top_addr m =
    let open BinIO
        val istr = openIn fname
        val data = inputAll istr
        val _ = closeIn istr
        val lines = (Word8Vector.length data - skip) div 4
        val l = List.tabulate(lines, fn i => read_word (data,4 * i + skip))
        val lterm = listSyntax.mk_list(l,``:word32``)
    in
      rhsc (SORT_UPDATE_CONV (mk_lupdate(mk_word30 top_addr,lterm,m)))
    end
end;

fun mem_read m a = (eval_word o rhsc o ARM_CONV) (mk_comb(m,mk_word30 a));

fun save_mem fname start finish le m = let open BinIO Arbnum
    fun bits  h l n = (n mod pow(two,plus1 h)) div (pow(two,l))
    val ostr = openOut fname
    val num2byte = Word8.fromInt o Arbnum.toInt;
    fun num2bytes w =
          map (fn (i,j) => num2byte (bits (fromInt i) (fromInt j) w))
              ((if le then rev else I) [(31,24),(23,16),(15,8),(7,0)])
    fun save_word i = map (fn b => output1(ostr,b)) (num2bytes (mem_read m i))
    fun recurse i =
          if Arbnum.<=(i,finish) then recurse (save_word i; Arbnum.plus1 i)
          else closeOut ostr
in
  recurse start
end;

(* ------------------------------------------------------------------------- *)
(* Set the general purpose, program status and coprocessor registers *)

val foldl_tm = ``FOLDL (\m (r:'a,v:word32). (r =+ v) m) x y``;

fun assign_type_reg_list (t:term frag list) =
  let val s = case hd t of QUOTE s => s | ANTIQUOTE x => "" in
    Term [QUOTE (s ^ ": (register # word32) list")]
  end;

fun assign_type_psr_list (t:term frag list) =
  let val s = case hd t of QUOTE s => s | ANTIQUOTE x => "" in
    Term [QUOTE (s ^ ": (psr # word32) list")]
  end;

fun set_registers reg rvs  =
 (rhsc o FOLD_UPDATE_CONV o
  subst [``x:registers`` |-> reg,
         ``y:(register # word32) list`` |-> assign_type_reg_list rvs] o
  inst [alpha |-> ``:register``]) foldl_tm;

fun set_status_registers psr rvs  = (rhsc o
  (FOLD_UPDATE_CONV
   THENC PURE_ONCE_REWRITE_CONV [SPEC `n2w n` arm_evalTheory.PSR_CONS]
   THENC ARM_CONV) o
  subst [``x:psrs`` |-> psr,
         ``y:(psr # word32) list`` |-> assign_type_psr_list rvs] o
  inst [alpha |-> ``:psr``]) foldl_tm;

(* ------------------------------------------------------------------------- *)
(* State & Input *)

type sys_state =
  {reg : term, psr : term, exc: term, cp_state : term, mem : term, pipe : term};

fun dest_state t =
  case strip_pair t of
    [arm, cp, memory, pipe] =>
     (case snd (TypeBase.dest_record arm) of
        [("regs", regs), ("exception", exc)] =>
         (case snd (TypeBase.dest_record regs) of
            [("reg", reg), ("psr", psr)] =>
              {reg = reg, psr = psr, exc = exc, cp_state = cp,
               mem = memory, pipe = pipe}
          | _ => raise ERR "dest_state" "regs")
      | _ => raise ERR "dest_state" "arm")
  | _ => raise ERR "dest_state" "tuple";

fun mk_state (x:sys_state) =
let
  val cp_typ = type_of (#cp_state x)
  val mem_typ = type_of (#mem x)
  val pipe_typ = type_of (#pipe x)
in
  subst [``reg:registers`` |-> #reg x, ``psr:psrs`` |-> #psr x,
         ``exc:exceptions`` |-> #exc x,
         ``cp:^(ty_antiq cp_typ)`` |-> #cp_state x,
         ``mem:^(ty_antiq mem_typ)`` |-> #mem x,
         ``pipe:^(ty_antiq pipe_typ)`` |-> #pipe x]
    ``(<| regs := <| reg := reg; psr := psr |>; exception := exc |>,
       cp:^(ty_antiq cp_typ), mem:^(ty_antiq mem_typ),
       pipe:^(ty_antiq pipe_typ))``
end;

(* ------------------------------------------------------------------------- *)
(* Running the model *)

fun init (cp,write,read,i) s =
let
  val cp_typ    = type_of cp
  val write_typ = type_of write
  val read_typ  = type_of read
  val state     = mk_state s
  val state_typ = type_of state
in
  (PURE_ONCE_REWRITE_CONV [CONJUNCT1 STATE_1STAGE_def] o
   subst [``cp:^(ty_antiq cp_typ)`` |-> cp,
          ``write:^(ty_antiq write_typ)`` |-> write,
          ``read:^(ty_antiq read_typ)`` |-> read,
          ``s:^(ty_antiq state_typ)`` |-> state,
          ``i:num -> regs option # bool # bool`` |-> i])
  ``STATE_1STAGE (cp:^(ty_antiq cp_typ))
       (write:^(ty_antiq write_typ)) (read:^(ty_antiq read_typ))
       (s:^(ty_antiq state_typ),i) 0``
end;

(*
 val x = ``(<|regs := <|reg := I a; psr := I b|>; exception := I c|>,
            I d : 'a, I e, I f : mem, I g : unit)``;

 reg  - rator rand rator rand rand rator
 psr  - rator rand rator rand rand rand
 exc  - rator rand rand

 arm  - rator
 cp   - rand rator
 mem  - rand rand rator
 pipe - rand rand rand
*)

fun REG_CONV c =
  RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV (RATOR_CONV c)))));

fun PSR_CONV c =
  RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV c)))));

fun COP_CONV c = RATOR_CONV (RATOR_CONV c);
fun EXC_CONV c = RATOR_CONV (RAND_CONV (RAND_CONV c));
fun MEM_CONV c = RAND_CONV (RAND_CONV (RATOR_CONV c));

val NEXT_ARM_CONV =
  ARM_CONV THENC
  SORT_UPDATE_CONV THENC
  REG_CONV ARM_ASSEMBLE_CONV THENC
  COP_CONV ARM_ASSEMBLE_CONV;

fun next (cp,write,read,i) t =
 let
   val time      = snd (dest_comb (lhsc t))
   val state     = rhsc t
   val cp_typ    = type_of cp
   val write_typ = type_of write
   val read_typ  = type_of read
   val state_typ = type_of state
   val t1 =
        (NEXT_ARM_CONV o
         subst [``cp:^(ty_antiq cp_typ)``              |-> cp,
                ``write:^(ty_antiq write_typ)``        |-> write,
                ``read:^(ty_antiq read_typ)``          |-> read,
                ``s:^(ty_antiq state_typ)``            |-> state,
                ``i:num -> regs option # bool # bool`` |-> i,
                ``t:num``                              |-> time])
      ``NEXT_1STAGE (cp:^(ty_antiq cp_typ)) (write:^(ty_antiq write_typ))
          (read:^(ty_antiq read_typ)) (s:^(ty_antiq state_typ), i (t:num))``
 in
   numLib.REDUCE_RULE (MATCH_MP STATE_1STAGE (CONJ t t1))
 end;

fun done t = term_eq ``undefined`` (#exc (dest_state (rhsc t)));

fun lstate _ _ [] _ = []
  | lstate (tmr,prtr) x (l as (t::ts)) n =
      if n = 0 then l
      else
        if can prtr (rhsc t) then
          let val nl = (tmr (uncurry next) (x, t)) :: l in
            if done t then nl else lstate (tmr,prtr) x nl (n - 1)
          end
      else
       (print "Aborted: probably in the wrong Thumb/ARM mode.\n"; l);

fun state (tmr,prtr) x t n =
  if n = 0 then t else
    if can prtr (rhsc t) then
      let val nxt = tmr (uncurry next) (x, t) in
        if done t then nxt else state (tmr,prtr) x nxt (n - 1)
      end
    else
      (print "Aborted: probably in the wrong Thumb/ARM mode.\n"; t);

fun pc_ptr s =
let
  val x = dest_state s
  val pc = eval_word (get_pc (#reg x))
in
  if not (term_eq ``software`` (#exc x)) then
    print ("0x" ^ Arbnum.toHexString pc ^ ": " ^
           term_to_string (#exc x) ^ " exception\n")
  else let val thumb = term_eq T (#T (dest_psr (get_cpsr (#psr x)))) in
    case to_halves (read_mem_range (#mem x) pc 1) of
      [ireg] =>
        (printn (mem_val_to_string ireg) before
         (thumb andalso term_eq ``enc`` (fst (dest_comb (snd (ireg))))
          andalso raise ERR "pc_ptr" "ARM in thumb mode"))
    | [ireg1, ireg2] =>
        (printn (mem_val_to_string
                       (if Data.even (Data.div2 pc) then ireg1 else ireg2))
         before (thumb orelse raise ERR "pc_ptr" "thumb in ARM mode"))
    | _ => raise ERR "pc_ptr" "Cannot print instruction register"
  end
end;

val mem_write = ``BASIC_WRITE``;
val mem_read  = ``BASIC_READ``;
val no_irpts  = ``NO_IRPTS``;
val no_cp     = ``NO_CP:'a coproc``;

fun evaluate_cp(n, x, y) = state (A,pc_ptr) x (init x y) n;

fun eval_cp (n, x, y) = lstate (time,pc_ptr) x [init x y] n;

fun evaluate (n, m, r, s) =
  evaluate_cp(n, (no_cp,mem_write,mem_read,no_irpts),
   {cp_state = ``cp_state:'a``, pipe = ``()``, exc = ``software``,
    mem = m, reg = r, psr = s});

fun eval (n, m, r, s) =
  eval_cp(n, (no_cp,mem_write,mem_read,no_irpts),
   {cp_state = ``cp_state:'a``, pipe = ``()``, exc = ``software``,
    mem = m, reg = r, psr = s});

(*
val x = evaluate(valOf Int.maxInt, empty_memory, empty_registers, empty_psrs);
*)

(* ------------------------------------------------------------------------- *)

fun myprint sys (pg,lg,rg) d pps t = let
      open Portable term_pp_types
      val (l,typ) = listSyntax.dest_list t
      val _ = typ = ``:word32`` andalso not (null l) orelse raise UserPP_Failed
      fun delim act = case pg of
                        Prec(_, "CONS") => ()
                      | _ => act()
    in
      delim (fn () => (begin_block pps CONSISTENT 0;
                       add_string pps "[";
                       add_break pps (1,2);
                       begin_block pps CONSISTENT 0));
      app (fn x => (sys (Prec(0, "CONS"), Top, Top) (d - 1) x;
                    add_string pps ";"; add_newline pps))
          (List.take (l,length l - 1));
      sys (Prec(0, "CONS"), Top, Top) (d - 1) (last l);
      delim (fn () => (end_block pps;
                       add_break pps (1,0);
                       add_string pps "]";
                       end_block pps))
    end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _ = temp_add_user_printer ({Tyop = "list", Thy = "list"}, myprint);

(* ------------------------------------------------------------------------- *)

end
