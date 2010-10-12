structure x64_Lib :> x64_Lib =
struct

open HolKernel boolLib bossLib;
open wordsLib stringLib listSyntax simpLib listTheory wordsTheory;
open opmonTheory bit_listTheory combinTheory ConseqConv;

open x64_Theory x64_seq_monadTheory x64_opsemTheory x64_astTheory;
open x64_coretypesTheory x64_icacheTheory;


(* decoder *)

fun nTimes n f x = if n = 0 then x else nTimes (n-1) f (f x)

val Zreg_distinct = x64_decoderTheory.Zreg_distinct;

fun eval_term_ss tm_name tm = conv_ss
  { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };

val bytes_LEMMA = SIMP_RULE std_ss [LENGTH] (Q.SPEC `[v1;v2;v3;v4;v5;v6;v7;v8]` bits2num_LESS)

val n2w_SIGN_EXTEND = prove(
  ``!n. n < 256 ==> (n2w (SIGN_EXTEND 8 32 n):word32 = sw2sw ((n2w n):word8))``,
  SIMP_TAC (std_ss++SIZES_ss) [sw2sw_def,w2n_n2w]);  

fun raw_x64_decode s = let
  fun mk_bool_list n =
    if n = 0 then ``[]:bool list`` else
      mk_cons(mk_var("vvv"^int_to_string n,``:bool``),mk_bool_list (n-1))
  val l = length (explode s) div 2
  val tm = mk_bool_list (8 * (20 - l))
  val tm = subst [``s:string`` |-> fromMLstring s, ``t:bool list``|->tm] ``bytebits s ++ t``
  val tm = (snd o dest_eq o concl o EVAL) tm
  val th = EVAL (mk_comb(``x64_decode``,tm))
  val _  = computeLib.add_funs [th]
  val (th,l) = let
    val x = find_term (can (match_term ``bits2num xs``)) (concl th)
    val thi = Q.INST [`w`|->`imm32`] w2bits_word32
    val i = fst (match_term (snd (dest_comb x)) ((snd o dest_eq o concl o SPEC_ALL) thi))
    val th = REWRITE_RULE [GSYM thi] (INST i th)
    val th = REWRITE_RULE [bits2num_w2bits,n2w_w2n] th
    in (th,l+4) end handle e => (th,l)
  val (th,l) = let
    val x = find_term (can (match_term ``bits2num xs``)) (concl th) 
    val th = REWRITE_RULE [bytes_LEMMA, MATCH_MP n2w_SIGN_EXTEND bytes_LEMMA] th
    val thi = Q.INST [`w`|->`imm8`] w2bits_word8
    val i = fst (match_term (snd (dest_comb x)) ((snd o dest_eq o concl o SPEC_ALL) thi))
    val th = REWRITE_RULE [GSYM thi] (INST i th)
    val th = REWRITE_RULE [bits2num_w2bits,n2w_w2n] th
    in (th,l+1) end handle e => (th,l)
  val tm = (snd o dest_comb o fst o dest_eq o concl) th
  in (th,tm,l) end;

fun x64_decode s = let
  val (th,tm,l) = raw_x64_decode s
  val th = MATCH_MP X64_NEXT_THM th
  val th = SIMP_RULE std_ss [LENGTH] th
  val th = nTimes l (SIMP_RULE std_ss [EVERY_DEF] o ONCE_REWRITE_RULE [ZREAD_INSTR_BYTES_def]) th
  fun assums i n =
    if i = 0 then [] else
      subst [``n:num``|->numSyntax.term_of_int n]
       ``ZREAD_INSTR (ZREAD_RIP s + n2w n) s = SOME (b2w I (TAKE 8 (DROP (8 * n) t)))`` :: assums (i-1) (n+1)
  val th = foldr (uncurry DISCH) th (assums l 0)
  val th = SIMP_RULE std_ss [WORD_ADD_0,GSYM WORD_ADD_ASSOC,word_add_n2w] th
  val th = INST [``t:bool list``|->tm] th
  val b2w_ss = eval_term_ss "b2w" ``(TAKE n t):bool list``
  val w2bits_ss = eval_term_ss "w2bits" ``w2bits ((b2w I x):word8):bool list``
  val th = SIMP_RULE (std_ss++b2w_ss) [FOLDR,MAP] th
  val th = REWRITE_RULE [w2bits_b2w_word32,APPEND,CONS_11,COLLECT_BYTES_n2w_bits2num] th
  val th = nTimes l UNDISCH th
  val th = nTimes 20 (SIMP_RULE std_ss [EVERY_DEF,GSYM WORD_ADD_ASSOC,word_add_n2w] o
                      ONCE_REWRITE_RULE [ZREAD_INSTR_BYTES_def]) th
  val th = SIMP_RULE std_ss [MAP,FOLDR,GSYM WORD_ADD_ASSOC,word_add_n2w,EVERY_DEF] th
  val th = REWRITE_RULE [GSYM AND_IMP_INTRO,w2bits_EL] th
  fun inst_one th = let
    val (x,y) = (dest_eq o fst o dest_imp o concl) th
    in UNDISCH (INST [y|->x] th) end
  val th = repeat inst_one th
  val th = REWRITE_RULE [] (DISCH_ALL th)
  val th = REWRITE_RULE [GSYM w2bits_word8,COLLECT_BYTES_n2w_bits2num] th
  val th = REWRITE_RULE [AND_IMP_INTRO,CONJ_ASSOC] th
  val th = ONCE_REWRITE_RULE [CONJ_COMM] th
  val th = REWRITE_RULE [GSYM CONJ_ASSOC,GSYM AND_IMP_INTRO] th
  val any_b2w_ss = eval_term_ss "any_b2w" ``(b2w I xs):'a word``
  val th = SIMP_RULE (std_ss++any_b2w_ss) [] th
  in th end handle e => (print "  Decoding failed.\n" ; raise e);

(* one step symbolic simulation *)

val else_none_read_mem_lemma = (UNDISCH o SPEC_ALL) x64_else_none_read_mem_lemma
val else_none_write_mem_lemma = (UNDISCH o SPEC_ALL) x64_else_none_write_mem_lemma
val else_none_eflag_lemma = (UNDISCH o SPEC_ALL) x64_else_none_eflag_lemma
val else_none_assert_lemma = (UNDISCH o SPEC_ALL) option_apply_assertT
val else_none_conv1 = (fst o dest_eq o concl) else_none_read_mem_lemma
val else_none_conv2 = (fst o dest_eq o concl) else_none_write_mem_lemma
val else_none_conv3 = (fst o dest_eq o concl) else_none_eflag_lemma
val else_none_conv4 = (fst o dest_eq o concl) else_none_assert_lemma
fun else_none_conv tm = let
  val ((i,t),th) = (match_term else_none_conv1 tm, else_none_read_mem_lemma) handle HOL_ERR _ =>
                   (match_term else_none_conv2 tm, else_none_write_mem_lemma) handle HOL_ERR _ =>
                   (match_term else_none_conv3 tm, else_none_eflag_lemma) handle HOL_ERR _ =>
                   (match_term else_none_conv4 tm, else_none_assert_lemma)
  in INST i (INST_TYPE t th) end;

val ss = rewrites [x64_exec_def, ZREAD_REG_def, ZREAD_EFLAG_def,
  ZREAD_MEM_def, ZREAD_RIP_def, ZWRITE_REG_def, ZWRITE_EFLAG_def,
  ZWRITE_REG_def, ZWRITE_MEM_def, ZWRITE_RIP_def, bump_rip_def,
  constT_def, addT_def, lockT_def, failureT_def, seqT_def, parT_def,
  parT_unit_def, write_reg_def, read_reg_def, write_eflag_def,
  read_eflag_def, write_rip_def, read_rip_def, write_m32_def,
  read_m32_def, write_m8_def, read_m8_def, write_m16_def,
  read_m16_def, write_m64_def, read_m64_def, seq_monad_thm,
  write_monop_def, ea_Zr_def, ea_Zi_def, ea_Zrm_base_def,
  ea_Zrm_index_def, ea_Zrm_def, ea_Zdest_def, ea_Zsrc_def,
  ea_Zimm_rm_def, read_ea_def, read_src_ea_def, read_dest_ea_def,
  write_ea_def, write_PF_def, write_ZF_def, write_SF_def,
  write_logical_eflags_def, x64_exec_pop_def, x64_exec_pop_rip_def,
  write_binop_with_carry_def, write_arith_eflags_except_CF_OF_def,
  write_arith_eflags_def, add_with_carry_out_def,
  clear_icache_seq_def, sub_with_borrow_out_def,
  write_arith_result_def, clear_icache_def,
  write_arith_result_no_CF_OF_def, write_arith_result_no_write_def,
  write_logical_result_def, write_logical_result_no_write_def,
  write_binop_def, write_monop_def, read_cond_def, read_reg_seq_def,
  read_rip_seq_def, write_rip_seq_def, read_m8_seq_def,
  write_m8_seq_def, read_m32_seq_def, write_m32_seq_def,
  read_m16_seq_def, write_m16_seq_def, read_m64_seq_def,
  write_m64_seq_def, APPLY_UPDATE_THM, WORD_EQ_ADD_LCANCEL,
  x64_address_lemma, write_reg_seq_def, jump_to_ea_def,
  x64_exec_push_def, x64_exec_push_rip_def, Zrm_is_memory_access_def,
  write_eflag_seq_def, if_some_lemma, ZREAD_CLAUSES,
  call_dest_from_ea_def, Zbinop_name_distinct, get_ea_address_def,
  erase_eflags_def, write_result_erase_eflags_def,restrict_size_def,
  word_signed_overflow_add_def, word_signed_overflow_sub_def, w2w_n2w,
  bitTheory.BITS_THM, value_width_def, word_size_msb_def]

fun x64_step s = let
  val th = x64_decode s
  val tm = (fst o dest_eq o fst o dest_imp o concl) th
  val th1 = SIMP_CONV (std_ss++ss++wordsLib.SIZES_ss)
              [x64_execute_def,Zrm_distinct,Zrm_11,Zreg_distinct] tm
  fun cc th = CONV_RULE (ONCE_DEPTH_CONV else_none_conv) th
  fun f th = (DISCH_ALL o CONV_RULE (RAND_CONV (SIMP_CONV std_ss [pull_if_lemma])) o
              UNDISCH_ALL o SIMP_RULE (std_ss++ss) [LET_DEF,Zreg_distinct,Zeflags_distinct] o
              DISCH_ALL o cc) th
  fun change f x = let val y = f x in if concl y = concl x then x else change f y end
  val th1 = change f th1
  val th1 = SIMP_RULE (std_ss++ss) [Zreg_distinct, Zeflags_distinct] th1
  val th1 = DISCH_ALL (MATCH_MP th (UNDISCH_ALL th1))
  val th1 = REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] (DISCH_ALL th1)
  val th1 = REWRITE_RULE [GSYM ZREAD_MEM2_WORD64_def, GSYM ZREAD_MEM2_WORD32_def,
                          GSYM ZREAD_MEM2_WORD16_def,
                          GSYM ZWRITE_MEM2_WORD64_def, GSYM ZWRITE_MEM2_WORD32_def,
                          GSYM ZWRITE_MEM2_WORD16_def] th1
  val th1 = STRENGTHEN_CONSEQ_CONV_RULE
    (CONSEQ_REWRITE_CONV ([],[CAN_ZREAD_ZWRITE_THM],[])) th1
    handle UNCHANGED => th1
  val th1 = SIMP_RULE bool_ss [GSYM AND_IMP_INTRO,pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY] th1
  val th1 = SIMP_RULE bool_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC] th1
  val th1 = SIMP_RULE bool_ss [SIMP_RULE (srw_ss()) [] (INST_TYPE[``:'a``|->``:32``]w2n_lt)] th1
  in th1 end;

(*

  open x64_encodeLib;

  val th = x64_step (x64_encode "dec eax")
  val th = x64_step "E9" (* example of partial decoder evaluation with imm32 *)
  val th = x64_step "83F1" (* example of partial decoder evaluation with imm8 *)
  val th = x64_step (x64_encode "mov DWORD [rsi],5000")
  val th = x64_step (x64_encode "mov BYTE [rax],-100")
  val th = x64_step (x64_encode "mov [rsi],rdx");
  val th = x64_step (x64_encode "INC r11");
  val th = x64_step (x64_encode "DEC QWORD [rax]");
  val th = x64_step (x64_encode "NOT bx");
  val th = x64_step (x64_encode "NEG r15");
  val th = x64_step (x64_encode "div rsi")
  val th = x64_step (x64_encode "ADD rax, 4");
  val th = x64_step (x64_encode "ADC rbx, rax");
  val th = x64_step (x64_encode "AND [rax+r11],rax");
  val th = x64_step (x64_encode "XOR WORD [4000],45");
  val th = x64_step (x64_encode "OR r12, 50000");
  val th = x64_step (x64_encode "SBB eax,[rax]");
  val th = x64_step (x64_encode "SUB r11,r12");
  val th = x64_step (x64_encode "CMP rax,3");
  val th = x64_step (x64_encode "TEST eax,3");
  val th = x64_step (x64_encode "xchg [rbx],rax")
  val th = x64_step (x64_encode "SHL eax,1");
  val th = x64_step (x64_encode "SHR rax,3");
  val th = x64_step (x64_encode "SAR bx,4");
  val th = x64_step (x64_encode "CMOVE rax, [r15+67]");
  val th = x64_step (x64_encode "CMOVNE eax, [rsi]");
  val th = x64_step (x64_encode "LEA rax, [8*rbx+rcx+5000000]");
  val th = x64_step (x64_encode "LOOP -5");
  val th = x64_step (x64_encode "LOOPE -15");
  val th = x64_step (x64_encode "LOOPNE 50");
  val th = x64_step (x64_encode "JB 40");
  val th = x64_step (x64_encode "JNB -4000");
  val th = x64_step (x64_encode "JMP 400");
  val th = x64_step (x64_encode "JMP rax");
  val th = x64_step (x64_encode "POP rax");
  val th = x64_step (x64_encode "PUSH [rbx]");
  val th = x64_step (x64_encode "DIV r11");
  val th = x64_step (x64_encode "MUL r12d");
  val th = x64_step (x64_encode "XADD rax,rdx");
  val th = x64_step (x64_encode "RET");
  val th = x64_step (x64_encode "RET 15");
  val th = x64_step (x64_encode "CALL r15");
  val th = x64_step (x64_encode "CMPXCHG r11,r14");
  val th = x64_step (x64_encode "mov rsi,4611686018427844360")
  val th = x64_step (x64_encode "movzx rdx,BYTE [rax]");
  val th = x64_step (x64_encode "movzx rdx,al");
  val th = x64_step (x64_encode "movzx rdx,WORD [rax]");
  val th = x64_step (x64_encode "movzx rdx,ax");

*)

val _ = output_words_as_hex();

fun x64_test_aux inst input output = let
  val rw = x64_step inst
  fun format state (i,j) =
    if i = "RIP"
    then ("ZREAD_RIP "^state^" = 0x"^j^"w")
    else if length (explode i) = 3
    then ("ZREAD_REG "^i^" "^state^" = 0x"^j^"w")
    else if length (explode i) = 2
    then ("ZREAD_EFLAG Z_"^i^" "^state^" = SOME "^j)
    else ("ZREAD_MEM 0x"^i^"w "^state^" = SOME (0x"^j^"w)")
  fun p y = Parse.Term [QUOTE y]
  fun f s = map (p o format s)
  val th = foldr (fn (x,y) => DISCH x y) rw (f "s" input)
  val th = SIMP_RULE std_ss [Zrm_distinct,Zrm_11,Zreg_distinct,Zeflags_distinct] th
  val th = SIMP_RULE std_ss [word_add_n2w,WORD_ADD_0,b2w_def,bits2num_def,GSYM AND_IMP_INTRO] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_n2w,word_mul_n2w,word_add_n2w,word_sub_def,word_2comp_n2w] th
  val ss = eval_term_ss "a" ``(bytes2word (xs:word8 list)):word32``
  val th = SIMP_RULE (std_ss++ss++SIZES_ss) [n2w_11] th
  val th = ONCE_REWRITE_RULE [ZREAD_RIP_ADD_0] th
  val th = REWRITE_RULE [AND_IMP_INTRO] th
  val th = REWRITE_RULE [GSYM CONJ_ASSOC] th
  val xs = find_terms (can (match_term ``ZWRITE_EFLAG x NONE``)) (concl th)
  val xs = map (implode o tl o tl o explode o fst o dest_const o snd o dest_comb o fst o dest_comb) xs
  fun distinct [] = [] | distinct (x::xs) = x::distinct (filter (fn y => not (y = x)) xs)
  val xs = distinct xs
  val output2 = filter (fn (x,y) => not (mem x xs)) output
  val output1 = filter (fn (x,y) => mem x xs) output
  val _ = map (fn (x,y) => print ("  Value of "^x^" is left unspecified by model.\n")) output1
  val tm = list_mk_conj (f "(THE (X64_NEXT s))" output2)
  val tm2 = (hd o hyp o UNDISCH) th
  val goal = mk_imp(tm2,tm)
(*
  set_goal([],goal)
*)
  val result = prove(goal,
    STRIP_TAC
    THEN (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO]) th
    THEN ASM_SIMP_TAC std_ss [ZREAD_CLAUSES,optionTheory.THE_DEF,Zreg_distinct,Zeflags_distinct]
    THEN STRIP_ASSUME_TAC x64_state_EZPAND
    THEN FULL_SIMP_TAC std_ss [ZREAD_REG_def,ZREAD_EFLAG_def,ZREAD_MEM_def,ZREAD_RIP_def,
           ZWRITE_MEM_def,ZWRITE_REG_def,ZWRITE_EFLAG_def,ZWRITE_RIP_def, APPLY_UPDATE_THM,Zreg_distinct]
    THEN EVAL_TAC)
  val result = REWRITE_RULE [GSYM AND_IMP_INTRO] result
  in result end;

fun x64_test inst input output = let
  fun p s = if length (explode s) < 4 then s else "["^s^"]"
  val _ = print ("\nTesting:\n  instruction = "^inst^"\n")
  val _ = print ("Input:\n")
  val _ = map (fn (x,y) => print ("  "^(p x)^" = "^y^"\n")) input
  val _ = print ("Output:\n")
  val _ = map (fn (x,y) => print ("  "^(p x)^" = "^y^"\n")) output
  val _ = print ("Result:\n")
  val th = SOME (x64_test_aux inst input output) handle e => NONE
  in case th of
      NONE => (print "  Test failed.\n"; TRUTH)
    | SOME th => (print "  Test successful.\n\n"; print_thm th; print "\n\n"; th)
  end;


end
