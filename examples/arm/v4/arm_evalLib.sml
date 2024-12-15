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
            "systemTheory", "assemblerML", "instructionTheory",
            "instructionSyntax"];
*)

open HolKernel boolLib bossLib;
open Q Parse computeLib combinTheory pairTheory wordsTheory wordsSyntax
     optionTheory rich_listTheory armTheory arm_evalTheory
     updateTheory systemTheory instructionTheory instructionSyntax assemblerML;

val ERR = mk_HOL_ERR "arm_evalLib"

(* ------------------------------------------------------------------------- *)
(* Some conversions *)

val SUC_RULE = numLib.SUC_RULE;

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

val arm_compset = wordsLib.words_compset();

val _ = Lib.C add_thms arm_compset
  [FST,SND,listTheory.EL_compute,HD,TL,MAP,FILTER,LENGTH,ZIP,FOLDL,
   APPEND,APPEND_NIL,ELL_compute,LAST_CONS,listTheory.FRONT_CONS,
   SUC_RULE listTheory.GENLIST,SNOC,listTheory.TAKE_def,K_THM,
   listTheory.NULL_DEF,
   register_EQ_register,num2register_thm,register2num_thm,
   mode_EQ_mode,mode2num_thm,mode_case_def,pairTheory.pair_case_thm,
   formats_case_def, psr_EQ_psr,psr2num_thm,
   iclass_EQ_iclass,iclass2num_thm,
   exceptions_EQ_exceptions,exceptions2num_thm,exceptions_case_def,
   num2exceptions_thm,exception2mode_def,
   num2condition_thm,condition2num_thm,condition_case_def,
   interrupt_case_def, literal_case_THM, iclass_case_def, data_case_def,
   APPLY_UPDATE_THM,

   SET_NZC_def,NZCV_def,USER_def,mode_num_def,
   DECODE_IFMODE_SET_NZCV,DECODE_NZCV_SET_NZCV,
   DECODE_IFMODE_SET_IFMODE,DECODE_NZCV_SET_IFMODE,
   SET_NZCV_IDEM,SET_IFMODE_IDEM,SET_IFMODE_NZCV_SWP,
   DECODE_PSR_def,DECODE_MODE_def,DECODE_PSR_THM,
   CPSR_READ_def,CPSR_WRITE_def,SPSR_READ_def,SPSR_WRITE_def,
   CPSR_WRITE_n2w,SPSR_WRITE_n2w,mode_reg2num_def,mode2psr_def,
   REG_READ_def,REG_WRITE_def,INC_PC_def,FETCH_PC_def,REG_READ6_def,
   word_modify_PSR,word_modify_PSR2,
   ALU_arith_def,ALU_logic_def,SUB_def,ADD_def,
   AND_def,EOR_def,ORR_def,ALU_def,
   LSL_def,LSR_def,ASR_def,ROR_def,
   WORD_ONLY_RULE `ireg` CONDITION_PASSED_def,CONDITION_PASSED2_def,
   DECODE_ARM_THM,

   ZIP,FOLDL,
   regs_accessors, regs_updates_eq_literal,
   regs_accfupds, regs_fupdfupds, regs_literal_11,
   regs_fupdfupds_comp, regs_fupdcanon,
   regs_fupdcanon_comp,
   arm_state_accessors, arm_state_updates_eq_literal,
   arm_state_accfupds, arm_state_fupdfupds, arm_state_literal_11,
   arm_state_fupdfupds_comp, arm_state_fupdcanon,
   arm_state_fupdcanon_comp,
   state_inp_accessors, state_inp_updates_eq_literal,
   state_inp_accfupds, state_inp_fupdfupds, state_inp_literal_11,
   state_inp_fupdfupds_comp, state_inp_fupdcanon,
   state_inp_fupdcanon_comp,
   state_out_accessors, state_out_updates_eq_literal,
   state_out_accfupds, state_out_fupdfupds, state_out_literal_11,
   state_out_fupdfupds_comp, state_out_fupdcanon,
   state_out_fupdcanon_comp,
   transfer_options_accessors, transfer_options_updates_eq_literal,
   transfer_options_accfupds, transfer_options_fupdfupds,
   transfer_options_literal_11, transfer_options_fupdfupds_comp,
   transfer_options_fupdcanon, transfer_options_fupdcanon_comp,
   arm_output_accessors, arm_output_updates_eq_literal,
   arm_output_accfupds, arm_output_fupdfupds, arm_output_literal_11,
   arm_output_fupdfupds_comp, arm_output_fupdcanon,
   arm_output_fupdcanon_comp,
   bus_accessors, bus_updates_eq_literal,
   bus_accfupds, bus_fupdfupds, bus_literal_11,
   bus_fupdfupds_comp, bus_fupdcanon,
   bus_fupdcanon_comp,
   regs_case_def,shift_case_def,

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
   LDM_LIST_def,STM_LIST_def,

   EXCEPTION_def,BRANCH_def,DATA_PROCESSING_def,MRS_def,LDR_STR_def,
   MLA_MUL_def,SWP_def,MRC_def,MCR_OUT_def,MSR_def,LDM_STM_def,LDC_STC_def,
   LDRH_STRH_def,

   empty_memory_def,empty_registers_def,empty_psrs_def,
   SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) [] interrupt2exception_def,
   IS_Reset_def,PROJ_Dabort_def,PROJ_Reset_def,
   THE_DEF,IS_SOME_DEF,IS_NONE_EQ_NONE,NOT_IS_SOME_EQ_NONE,
   option_case_ID,option_case_SOME_ID,
   option_case_def,SOME_11,NOT_SOME_NONE,PROJ_IF_FLAGS_def,
   sumTheory.OUTL, sumTheory.OUTR, RUN_ARM_def,NEXT_ARM_def,
   SIMP_RULE (bool_ss++pred_setSimps.PRED_SET_ss) [] OUT_ARM_def,

   arm_sys_state_accessors, arm_sys_state_updates_eq_literal,
   arm_sys_state_accfupds, arm_sys_state_fupdfupds, arm_sys_state_literal_11,
   arm_sys_state_fupdfupds_comp, arm_sys_state_fupdcanon,
   arm_sys_state_fupdcanon_comp,
   coproc_accessors, coproc_updates_eq_literal,
   coproc_accfupds, coproc_fupdfupds,
   coproc_literal_11, coproc_fupdfupds_comp,
   coproc_fupdcanon, coproc_fupdcanon_comp,
   cp_output_accessors, cp_output_updates_eq_literal,
   cp_output_accfupds, cp_output_fupdfupds, cp_output_literal_11,
   cp_output_fupdfupds_comp, cp_output_fupdcanon,
   cp_output_fupdcanon_comp,
   bus_accessors, bus_updates_eq_literal,
   bus_accfupds, bus_fupdfupds, bus_literal_11,
   bus_fupdfupds_comp, bus_fupdcanon,
   bus_fupdcanon_comp,

   memop_case_def, fcpTheory.index_comp, decode_cp_enc_coproc,
   decode_27_enc_coproc, decode_cdp_enc, decode_mrc_mcr_enc,

   APPLY_LUPDATE_THM, fcpTheory.FCP_APPLY_UPDATE_THM,
   addr30_def, SET_BYTE_def, SET_HALF_def, TRANSFERS_def, TRANSFER_def,

   MEM_WRITE_BYTE_def, MEM_WRITE_HALF_def, MEM_WRITE_WORD_def,
   MEM_WRITE_def, OUT_CP_def, RUN_CP_def, NO_CP_def, NEXT_ARM_MMU];

val ARM_CONV = CBV_CONV arm_compset;
val ARM_RULE = CONV_RULE ARM_CONV;

fun add_rws f rws =
let val cmp_set = f()
    val _ = add_thms rws cmp_set
in cmp_set end;

val EVAL_UPDATE_CONV =
let val compset = add_rws reduceLib.num_compset
          [register_EQ_register,register2num_thm,APPLY_UPDATE_THM]
in
  computeLib.CBV_CONV compset
end;

val SORT_UPDATE_CONV =
let open arm_evalTheory fcpTheory updateTheory
    val rule = SIMP_RULE std_ss [register2num_lt_neq, psr2num_lt_neq,
                                 prim_recTheory.LESS_NOT_EQ]
    fun rule1 t = (rule o ISPEC t) UPDATE_SORT_RULE1
    fun rule2 t = (rule o ISPEC t) UPDATE_SORT_RULE2
    val Ua_RULE4 = rule1 `\x y. register2num x < register2num y`
    val Ub_RULE4 = rule2 `\x y. register2num x < register2num y`
    val Ua_RULE_PSR = rule1 `\x y. psr2num x < psr2num y`
    val Ub_RULE_PSR = rule2 `\x y. psr2num x < psr2num y`
    val FUa_RULE = (rule o SPEC `\x y. x < y`) FCP_UPDATE_SORT_RULE1
    val FUb_RULE = (rule o SPEC `\x y. x < y`) FCP_UPDATE_SORT_RULE2
    val compset = add_rws wordsLib.words_compset
        [o_THM,register_EQ_register,register2num_thm,psr_EQ_psr,psr2num_thm,
         SYM Ua_def,UPDATE_EQ_RULE,Ua_RULE4,Ub_RULE4,Ua_RULE_PSR,Ub_RULE_PSR,
         SYM FUa_def,FCP_UPDATE_EQ_RULE,FUa_RULE,FUb_RULE,
         LENGTH,SUC_RULE JOIN,listTheory.DROP_def,APPEND,
         PURE_REWRITE_RULE [SYM Ua_def] UPDATE_LUPDATE,
         LIST_UPDATE_SORT_RULE1,LIST_UPDATE_SORT_RULE2,GSYM LUa_def]
in
  computeLib.CBV_CONV compset
    THENC PURE_REWRITE_CONV [Ua_def,Ub_def,FUa_def,FUb_def,LUa_def,LUb_def]
    THENC SIMP_CONV (srw_ss()) [UPDATE_APPLY_IMP_ID,APPLY_UPDATE_THM,
            FCP_UPDATE_IMP_ID,FCP_APPLY_UPDATE_THM,FCP_BETA]
end;

val FOLD_UPDATE_CONV =
let val compset = add_rws wordsLib.words_compset
      [SET_IFMODE_def,SET_NZCV_def,FOLDL,APPLY_UPDATE_THM,
       psr_EQ_psr,psr2num_thm,mode_num_def,mode_case_def,
       register_EQ_register,register2num_thm,
       empty_registers_def,empty_memory_def,empty_psrs_def]
in
  computeLib.CBV_CONV compset THENC SORT_UPDATE_CONV
end;

val ARM_ASSEMBLE_CONV = let open instructionTheory
  val compset = add_rws wordsLib.words_compset
       [transfer_options_accessors,transfer_options_updates_eq_literal,
        transfer_options_accfupds,transfer_options_fupdfupds,
        transfer_options_literal_11,transfer_options_fupdfupds_comp,
        transfer_options_fupdcanon,transfer_options_fupdcanon_comp,
        condition2num_thm,arm_instruction_case_def,addr_mode1_case_def,
        addr_mode2_case_def,addr_mode3_case_def,
        msr_mode_case_def,condition_encode,
        shift_encode_def,addr_mode1_encode_def,
        addr_mode2_encode_def,addr_mode3_encode_def,
        msr_mode_encode_def,msr_psr_encode_def,
        options_encode_def,options_encode2_def,
        data_proc_encode_def,instruction_encode_def,K_THM,
        SET_NZCV_def,SET_IFMODE_def,mode_num_def,mode_case_def]
in
  computeLib.CBV_CONV compset
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

local
  fun do_dest_subst_reg t a =
        let val (i,d,m) = dest_subst t in
          do_dest_subst_reg m
              (if isSome (List.find (fn a => term_eq (fst a) i) a) then a
               else ((i,d)::a))
        end handle HOL_ERR _ => (``ARB:register``,t)::a;

  fun do_dest_subst_mem t a =
       let val (i,d,m) = dest_lupdate t in
          do_dest_subst_mem m ((i,fst (listSyntax.dest_list d))::a)
       end handle HOL_ERR _ =>
         let val (i,d,m) = dest_subst t in
            do_dest_subst_mem m ((i,[d])::a)
         end handle HOL_ERR _ => (``ARB:register``,[t])::(rev a);
in
  fun dest_subst_reg t = do_dest_subst_reg t []
  fun dest_subst_mem t = do_dest_subst_mem t []
end;

fun get_reg l rest r =
      case List.find (fn a => term_eq (fst a) r) l of
        SOME (x,y) => y
      | _ => (rhsc o EVAL_UPDATE_CONV o mk_comb) (rest,r);

fun get_pc t =
 let val regs = dest_subst_reg t
     val l = tl regs
     val rest = snd (hd regs)
 in
   get_reg l rest ``r15``
 end;

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

  fun print_reg l rest r =
        (print_term r; print "="; print_term (get_reg l rest r); print "; ");

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
in
  val print_all_regs = pprint_regs (K true);
  val print_usr_regs = pprint_regs (fn (i,m) => m = USR);
  val print_std_regs = pprint_regs (fn (i,m) => (m = USR) orelse (m = UND));
  fun print_regs l = pprint_regs (fn x => mem x l);
end;

local
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
end;

fun read_mem_block m n =
  let open Arbnum
      val dm = List.nth(dest_subst_mem m, n)
      val sa = eval_word (fst dm)
      val bl = snd dm
      val n4 = fromInt 4
      val addrs = List.tabulate(length bl, fn i => (sa + fromInt i) * n4)
  in
     zip addrs bl
  end;

fun mem_val_to_string(n, t) =
  "0x" ^ Arbnum.toHexString n ^ ": " ^
  (let val (l, r) = dest_comb t in
    if term_eq l ``enc`` then
      dest_instruction (SOME n) r
    else
      term_to_string t
   end handle HOL_ERR _ => term_to_string t);

fun print_mem_range m (start, n) =
  app printn (map mem_val_to_string (read_mem_range m start n));

fun print_mem_block m n =
  app printn (map mem_val_to_string (read_mem_block m n))
  handle HOL_ERR _ => ();

type arm_state = {mem : term, psrs : term, reg : term, undef : term};

fun dest_arm_eval t =
  case snd (TypeBase.dest_record t) of
     [("registers", reg), ("psrs", psrs),
      ("memory", mem), ("undefined", undef),("cp_state", cp_reg)] =>
         {mem = mem, reg = reg, psrs = psrs, undef = undef}
  | _ => raise ERR "dest_arm_eval" "";

(* ------------------------------------------------------------------------- *)

fun hol_assemble m a l = let
  val code = map (rhsc o ARM_ASSEMBLE_CONV o
                  (curry mk_comb ``instruction_encode``) o Term) l
  val block = listSyntax.mk_list(code,``:word32``)
in
  rhsc (SORT_UPDATE_CONV (mk_lupdate(mk_word30 a,block,m)))
end;

fun hol_assemble1 m a t = hol_assemble m a [t];

local
  fun add1 a = Data.add32 a Arbnum.one;
  fun div4 a = Arbnum.div(a,Arbnum.fromInt 4);
  fun mul4 a = Arbnum.*(a,Arbnum.fromInt 4);
  val start = Arbnum.zero;

  fun label_table() =
    ref (Redblackmap.mkDict String.compare);
    (*
    Polyhash.mkPolyTable
      (100,HOL_ERR {message = "Cannot find ARM label\n",
                    origin_function = "", origin_structure = "arm_evalLib"});
    *)

  fun mk_links [] ht n = ()
    | mk_links (h::r) ht n =
        case h of
          Data.Code c => mk_links r ht (add1 n)
        | Data.BranchS b => mk_links r ht (add1 n)
        | Data.BranchN b => mk_links r ht (add1 n)
        | Data.Label s =>
            (ht := Redblackmap.insert
                          (!ht, s, "0x" ^ Arbnum.toHexString (mul4 n));
            (*(Polyhash.insert ht (s, "0x" ^ Arbnum.toHexString (mul4 n));*)
             mk_links r ht n)
        | Data.Mark m => mk_links r ht (div4 m);

  fun mk_link_table code = let val ht = label_table() in
    mk_links code ht start; ht
  end;

  fun br_to_term (cond,link,label) ht n =
    let val s = assembler_to_string NONE (Data.BranchS(cond,link,"")) NONE
        val address =
          Redblackmap.find (!ht, label)
          handle Redblackmap.NotFound =>
            raise mk_HOL_ERR "arm_evalLib" "" "Cannot find ARM label\n"
          (*Polyhash.find ht label*)
    in
      mk_instruction ("0x" ^ Arbnum.toHexString (mul4 n) ^ ": " ^ s ^ address)
    end;

  fun mk_enc t = if type_of t = ``:word32`` then t else mk_comb(``enc``, t);

  fun is_label (Data.Label s) = true | is_label _ = false;

  fun lcons h [] = [[h]]
    | lcons h (x::l) = (h::x)::l;

  fun do_link m l [] ht n = zip m l
    | do_link m l (h::r) ht n =
        case h of
           Data.Code c =>
             do_link m (lcons (mk_enc (arm_to_term (validate_instruction c))) l)
               r ht (add1 n)
         | Data.BranchS b =>
             do_link m (lcons (mk_enc (br_to_term b ht n)) l) r ht (add1 n)
         | Data.BranchN b =>
             let val t = mk_enc (arm_to_term (branch_to_arm b (mul4 n))) in
               do_link m (lcons t l) r ht (add1 n)
             end
         | Data.Label s => do_link m l r ht n
         | Data.Mark mk => let val k = div4 mk in
               if k = n then
                 do_link m l r ht n
               else if null (hd l) then
                 do_link (k::(tl m)) l r ht k
               else
                 do_link (k::m) ([]::l) r ht k
             end;

  fun do_links code =
        let val l = do_link [start] [[]] code (mk_link_table code) start in
          rev (map (fn (a,b) => (a,rev b)) l)
        end;

  fun assemble_assambler m a = let
    val l = do_links a
    val b = map (fn (m,c) => (mk_word30 m,listSyntax.mk_list(c,``:word32``))) l
    val t = foldr (fn ((a,c),t) => mk_lupdate(a,c,t)) m b
  in
    rhsc (SORT_UPDATE_CONV t)
  end
in
  fun assemble m file = assemble_assambler m (parse_arm file);
  fun list_assemble m l =
    let val nll = String.concat (map (fn s => s ^ "\n") l)
        val c = substring(nll,0,size nll - 1)
    in
      assemble_assambler m (string_to_code c)
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
(* Running the model *)

fun init f m r s c =
 let
   val ftyp = type_of f
   val ttyp = type_of c
 in
   (PURE_ONCE_REWRITE_CONV [CONJUNCT1 STATE_ARM_MMU_def] o
    subst [``f:^(ty_antiq ftyp)`` |-> f, ``mem:mem`` |-> m,
           ``registers:registers`` |-> r, ``psrs:psrs`` |-> s,
           ``cp_state:^(ty_antiq ttyp)`` |-> c])
   ``STATE_ARM_MMU (f:^(ty_antiq ftyp))  0
        <| registers := registers; psrs :=  psrs;
           memory := mem; undefined := F;
           cp_state := cp_state:^(ty_antiq ttyp) |>``
 end;

(*
 reg - rator
 psr - rand rator
 mem - rand rand rator
 und - rand rand rand rator
 cps - rand rand rand rand
*)

val NEXT_ARM_CONV =
  ARM_CONV THENC
  ONCE_DEPTH_CONV (RATOR_CONV SORT_UPDATE_CONV) THENC
  ONCE_DEPTH_CONV (RAND_CONV (RATOR_CONV SORT_UPDATE_CONV)) THENC
  ONCE_DEPTH_CONV (RAND_CONV (RAND_CONV (RATOR_CONV SORT_UPDATE_CONV))) THENC
  ONCE_DEPTH_CONV
    (RAND_CONV (RAND_CONV (RAND_CONV (RAND_CONV SORT_UPDATE_CONV)))) THENC
  RATOR_CONV ARM_ASSEMBLE_CONV THENC
  RAND_CONV (RAND_CONV (RAND_CONV (RAND_CONV ARM_ASSEMBLE_CONV)));

fun next(f, t) =
  let val t0 = rhsc t
      val ttyp = type_of t0
      val ftyp = type_of f
      val t1 = (NEXT_ARM_CONV o
                subst [``f:^(ty_antiq ftyp)`` |-> f,
                       ``s:^(ty_antiq ttyp)`` |-> t0])
              ``NEXT_ARM_MMU (f:^(ty_antiq ftyp)) (s:^(ty_antiq ttyp))``
  in
     numLib.REDUCE_RULE (MATCH_MP STATE_ARM_MMU_NEXT (CONJ t t1))
  end;

fun done t = term_eq T (#undef (dest_arm_eval (rhsc t)));

fun lstate _ _ _ [] = []
  | lstate (tmr,prtr) n f (l as (t::ts)) =
      if n = 0 then l
      else
        let val _ = prtr (dest_arm_eval (rhsc t))
            val nl = (tmr next (f, t)) :: l
        in
          if done t then nl else lstate (tmr,prtr) (n - 1) f nl
        end;

fun state (tmr,prtr) n f s =
  if n = 0 then s
   else
     let val _ = prtr (dest_arm_eval (rhsc s))
         val ns = tmr next (f, s)
     in
       if done s then ns else state (tmr,prtr) (n - 1) f ns
     end;

fun pc_ptr (x : arm_state) =
  let val pc = eval_word (get_pc (#reg x)) in
    if term_eq T (#undef x) then
      print ("0x" ^ Arbnum.toHexString pc ^ ": undefined exception\n")
    else
      print_mem_range (#mem x) (pc, 1)
  end;

fun A f x = f x

fun evaluate_cp (n, f, m, r, s, p) = state (A,pc_ptr) n f (init f m r s p)
fun eval_cp (n, f, m, r, s, p) = lstate (time,pc_ptr) n f [init f m r s p]

fun evaluate (n, m, r, s) =
  evaluate_cp (n, ``NO_CP:unit coproc``, m, r, s, ``()``);

fun eval (n, m, r, s) =
  eval_cp (n, ``NO_CP:unit coproc``, m, r, s, ``()``);

(* ------------------------------------------------------------------------- *)

fun myprint Gs backend sys ppfns (pg,lg,rg) d t = let
  open Portable term_pp_types smpp
  infix >>
  val {add_string=strn,add_break=brk,ublock,add_newline,...} =
      ppfns : ppstream_funs
  val (l,typ) = listSyntax.dest_list t
  val _ = typ = ``:word32`` andalso not (null l) orelse raise UserPP_Failed
  fun delim act =
      case pg of
        Prec(_, "CONS") => act
      | _ => ublock CONSISTENT 0
                    (strn "[" >> brk (1,1) >>
                     ublock CONSISTENT 0 (act >> brk(1,0) >> strn "]"))
in
  delim (
    smpp.pr_list
      (sys {gravs = (Prec(0, "CONS"), Top, Top),
            depth = d - 1, binderp = false})
      (strn ";" >> add_newline)
      l)
end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _ = temp_add_user_printer
   ("arm_evalLib.myprint", ``x:word32 list``, myprint);

(* ------------------------------------------------------------------------- *)

end
