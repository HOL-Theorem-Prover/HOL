structure x86_Lib :> x86_Lib =
struct

open HolKernel boolLib bossLib;
open wordsLib stringLib listSyntax simpLib listTheory wordsTheory;
open opmonTheory bit_listTheory combinTheory ConseqConv;

open x86_Theory x86_seq_monadTheory x86_opsemTheory x86_astTheory;
open x86_coretypesTheory x86_icacheTheory;


(* decoder *)

fun nTimes n f x = if n = 0 then x else nTimes (n-1) f (f x)

fun eval_term_ss tm_name tm = conv_ss
  { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };

fun raw_x86_decode s = let
  fun mk_bool_list n =
    if n = 0 then ``[]:bool list`` else
      mk_cons(mk_var("vvv"^int_to_string n,``:bool``),mk_bool_list (n-1))
  val l = length (explode s) div 2
  val tm = mk_bool_list (8 * (20 - l))
  val tm = subst [``s:string`` |-> fromMLstring s, ``t:bool list``|->tm] ``bytebits s ++ t``
  val tm = (snd o dest_eq o concl o EVAL) tm
  val th = EVAL (mk_comb(``x86_decode``,tm))
  val _  = computeLib.add_funs [th]
  val (th,l) = let
    val x = find_term (can (match_term ``bits2num xs``)) (concl th)
    val thi = Q.INST [`w`|->`imm32`] w2bits_word32
    val i = fst (match_term (snd (dest_comb x)) ((snd o dest_eq o concl o SPEC_ALL) thi))
    val th = REWRITE_RULE [GSYM thi] (INST i th)
    val th = REWRITE_RULE [bits2num_w2bits,n2w_w2n] th
    in (th,l+4) end handle e => (th,l)
  val tm = (snd o dest_comb o fst o dest_eq o concl) th
  in (th,tm,l) end;

fun x86_decode s = let
  val (th,tm,l) = raw_x86_decode s
  val th = MATCH_MP X86_NEXT_THM th
  val th = SIMP_RULE std_ss [LENGTH] th
  val th = nTimes l (SIMP_RULE std_ss [EVERY_DEF] o ONCE_REWRITE_RULE [XREAD_INSTR_BYTES_def]) th
  fun assums i n =
    if i = 0 then [] else
      subst [``n:num``|->numSyntax.term_of_int n]
       ``XREAD_INSTR (XREAD_EIP s + n2w n) s = SOME (b2w I (TAKE 8 (DROP (8 * n) t)))`` :: assums (i-1) (n+1)
  val th = foldr (uncurry DISCH) th (assums l 0)
  val th = SIMP_RULE std_ss [WORD_ADD_0,GSYM WORD_ADD_ASSOC,word_add_n2w] th
  val th = INST [``t:bool list``|->tm] th
  val b2w_ss = eval_term_ss "b2w" ``(TAKE n t):bool list``
  val w2bits_ss = eval_term_ss "w2bits" ``w2bits ((b2w I x):word8):bool list``
  val th = SIMP_RULE (std_ss++b2w_ss) [FOLDR,MAP] th
  val th = REWRITE_RULE [w2bits_b2w_word32,APPEND,CONS_11,COLLECT_BYTES_n2w_bits2num] th
  val th = nTimes l UNDISCH th
  val th = nTimes 20 (SIMP_RULE std_ss [EVERY_DEF,GSYM WORD_ADD_ASSOC,word_add_n2w] o
                      ONCE_REWRITE_RULE [XREAD_INSTR_BYTES_def]) th
  val th = SIMP_RULE std_ss [MAP,FOLDR,GSYM WORD_ADD_ASSOC,word_add_n2w,EVERY_DEF] th
  val th = REWRITE_RULE [GSYM AND_IMP_INTRO,w2bits_EL] th
  fun inst_one th = let
    val (x,y) = (dest_eq o fst o dest_imp o concl) th
    in UNDISCH (INST [y|->x] th) end
  val th = repeat inst_one th
  val th = REWRITE_RULE [] (DISCH_ALL th)
  val th = REWRITE_RULE [AND_IMP_INTRO,CONJ_ASSOC] th
  val th = ONCE_REWRITE_RULE [CONJ_COMM] th
  val th = REWRITE_RULE [GSYM CONJ_ASSOC,GSYM AND_IMP_INTRO] th
  val any_b2w_ss = eval_term_ss "any_b2w" ``(b2w I xs):'a word``
  val th = SIMP_RULE (std_ss++any_b2w_ss) [] th
  in th end handle e => (print "  Decoding failed.\n" ; raise e);


(* one step symbolic simulation *)

val else_none_read_mem_lemma = (UNDISCH o SPEC_ALL) x86_else_none_read_mem_lemma
val else_none_write_mem_lemma = (UNDISCH o SPEC_ALL) x86_else_none_write_mem_lemma
val else_none_eflag_lemma = (UNDISCH o SPEC_ALL) x86_else_none_eflag_lemma
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

val ss = rewrites [x86_exec_def, XREAD_REG_def, XREAD_EFLAG_def,
  XREAD_MEM_def, XREAD_EIP_def, XWRITE_REG_def, XWRITE_EFLAG_def,
  XWRITE_REG_def, XWRITE_MEM_def, XWRITE_EIP_def, bump_eip_def,
  constT_def, addT_def, lockT_def, failureT_def, seqT_def, parT_def,
  parT_unit_def, write_reg_def, read_reg_def, write_eflag_def,
  read_eflag_def, write_eip_def, read_eip_def, write_m32_def,
  read_m32_def, write_m8_def, read_m8_def, seq_monad_thm,
  read_src_ea_byte_def, write_ea_byte_def, read_ea_byte_def,
  write_monop_def, ea_Xr_def, ea_Xi_def, ea_Xrm_base_def,
  ea_Xrm_index_def, ea_Xrm_def, ea_Xdest_def, ea_Xsrc_def,
  read_dest_ea_byte_def, ea_Ximm_rm_def, read_ea_def, read_src_ea_def,
  read_dest_ea_def, write_ea_def, write_PF_def, write_ZF_def,
  write_SF_def, write_logical_eflags_def, x86_exec_pop_def,
  x86_exec_pop_eip_def, write_arith_eflags_except_CF_def,
  write_arith_eflags_def, add_with_carry_out_def,
  clear_icache_seq_def, sub_with_borrow_out_def,
  write_arith_result_def, clear_icache_def,
  write_arith_result_no_CF_def, write_arith_result_no_write_def,
  write_logical_result_def, write_logical_result_no_write_def,
  write_binop_def, write_monop_def, read_cond_def, read_reg_seq_def,
  read_eip_seq_def, write_eip_seq_def, read_m8_seq_def,
  write_m8_seq_def, read_m32_seq_def, write_m32_seq_def,
  APPLY_UPDATE_THM, WORD_EQ_ADD_LCANCEL, x86_address_lemma,
  write_reg_seq_def, jump_to_ea_def, x86_exec_push_def,
  x86_exec_push_eip_def, rm_is_memory_access_def, write_eflag_seq_def,
  if_some_lemma, XREAD_CLAUSES, call_dest_from_ea_def,
  get_ea_address_def, erase_eflags_def, write_result_erase_eflags_def,
  word_signed_overflow_add_def, word_signed_overflow_sub_def]

fun x86_step s = let
  val th = x86_decode s
  val tm = (fst o dest_eq o fst o dest_imp o concl) th
  val th1 = SIMP_CONV (std_ss++ss++wordsLib.SIZES_ss)
              [x86_execute_def,Xrm_distinct,Xrm_11,Xreg_distinct] tm
  fun cc th = CONV_RULE (ONCE_DEPTH_CONV else_none_conv) th
  fun f th = (DISCH_ALL o CONV_RULE (RAND_CONV (SIMP_CONV std_ss [pull_if_lemma])) o
              UNDISCH_ALL o SIMP_RULE (std_ss++ss) [LET_DEF,Xreg_distinct,Xeflags_distinct] o
              DISCH_ALL o cc) th
  fun change f x = let val y = f x in if concl y = concl x then x else change f y end
  val th1 = change f th1
  val th1 = SIMP_RULE (std_ss++ss) [Xreg_distinct, Xeflags_distinct] th1
  val th1 = DISCH_ALL (MATCH_MP th (UNDISCH_ALL th1))
  val th1 = REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] (DISCH_ALL th1)
  val th1 = REWRITE_RULE [GSYM XREAD_MEM2_WORD_def,GSYM XWRITE_MEM2_WORD_def] th1
  val th1 = STRENGTHEN_CONSEQ_CONV_RULE
    (CONSEQ_REWRITE_CONV ([],[CAN_XREAD_XWRITE_THM],[])) th1
    handle UNCHANGED => th1
  val th1 = SIMP_RULE bool_ss [GSYM AND_IMP_INTRO,pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY] th1
  val th1 = SIMP_RULE bool_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC] th1
  in th1 end;


(*

  open x86_encodeLib;

  (* works *)

  val th = x86_step (x86_encode "dec eax")
  val th = x86_step "E9" (* example of partial decoder evaluation *)
  val th = x86_step (x86_encode "mov [esi],45")
  val th = x86_step (x86_encode "mov BYTE [eax],-100")
  val th = x86_step (x86_encode "div esi")
  val th = x86_step (x86_encode "jmp esi")
  val th = x86_step (x86_encode "xchg [ebx],eax")
  val th = x86_step (x86_encode "mov BYTE [esi],edx");
  val th = x86_step "0FB63E";          (* mov_byte edi,[esi] *)
  val th = x86_step "0538000000";      (* add eax,56 *)
  val th = x86_step "8B3E";            (* mov edi,[esi] *)
  val th = x86_step "810037020000";    (* add dword [eax],567 *)
  val th = x86_step "010B";            (* add [ebx], ecx *)
  val th = x86_step "0119";            (* add [ecx], ebx *)
  val th = x86_step "2538000000";      (* and eax,56 *)
  val th = x86_step "812037020000";    (* and dword [eax],567 *)
  val th = x86_step "210B";            (* and [ebx], ecx *)
  val th = x86_step "2319";            (* and ebx, [ecx] *)
  val th = x86_step "81FE38000000";    (* cmp esi,56 *)
  val th = x86_step "813B37020000";    (* cmp dword [ebx],567 *)
  val th = x86_step "390B";            (* cmp [ebx], ecx *)
  val th = x86_step "3B19";            (* cmp ebx, [ecx] *)
  val th = x86_step "893E";            (* mov [esi],edi *)
  val th = x86_step "8B3E";            (* mov edi,[esi] *)
  val th = x86_step "BC37020000";      (* mov esp,567 *)
  val th = x86_step "81CE38000000";    (* or  esi,56 *)
  val th = x86_step "810B37020000";    (* or  dword [ebx],567 *)
  val th = x86_step "090B";            (* or  [ebx], ecx *)
  val th = x86_step "0B19";            (* or  ebx, [ecx] *)
  val th = x86_step "81EE38000000";    (* sub esi,56 *)
  val th = x86_step "812B37020000";    (* sub dword [ebx],567 *)
  val th = x86_step "290B";            (* sub [ebx], ecx *)
  val th = x86_step "2B19";            (* sub ebx, [ecx] *)
  val th = x86_step "F7C638000000";    (* test esi,56 *)
  val th = x86_step "F70337020000";    (* test dword [ebx],567 *)
  val th = x86_step "850B";            (* test [ebx], ecx *)
  val th = x86_step "81F638000000";    (* xor esi,56 *)
  val th = x86_step "813337020000";    (* xor dword [ebx],567 *)
  val th = x86_step "310B";            (* xor [ebx], ecx *)
  val th = x86_step "3319";            (* xor ebx, [ecx] *)
  val th = x86_step "FF4E3C";          (* dec dword [esi+60] *)
  val th = x86_step "4C";              (* dec esp *)
  val th = x86_step "FF80401F0000";    (* inc dword [eax+8000] *)
  val th = x86_step "40";              (* inc eax *)
  val th = x86_step "F750C8";          (* not dword [eax-56] *)
  val th = x86_step "EBB9";            (* jmp l1 *)
  val th = x86_step "F7583C";          (* neg dword [eax+60] *)
  val th = x86_step "74B7";            (* je l1 *)
  val th = x86_step "75B5";            (* jne l1 *)
  val th = x86_step "0F44C1";          (* cmove eax, ecx *)
  val th = x86_step "0F454104";        (* cmovne eax, [ecx+4] *)
  val th = x86_step "8F0590010000";    (* pop dword [400] *)
  val th = x86_step "50";              (* push eax *)
  val th = x86_step "C3";              (* ret *)
  val th = x86_step "C20500";          (* ret 5 *)
  val th = x86_step "E8BDFFFFFF";      (* call l1 *)
  val th = x86_step "FFB42DEA000000";  (* push dword [ebp + ebp + 234] *)
  val th = x86_step "FFB498C8010000";  (* push dword [eax + 4*ebx + 456] *)
  val th = x86_step "FF749801";        (* push dword [eax + 4*ebx + 1] *)
  val th = x86_step "FF74AD02";        (* push dword [ebp + 4*ebp + 2] *)
  val th = x86_step "FF746D2D";        (* push dword [ebp + 2*ebp + 45] *)
  val th = x86_step "FFB4B6EE711202";  (* push dword [esi + 4*esi + 34763246] *)
  val th = x86_step "E2AF";            (* loop l1 *)
  val th = x86_step "E1AD";            (* loope l1 *)
  val th = x86_step "E0AB";            (* loopne l1 *)
  val th = x86_step "59";              (* pop ecx *)
  val th = x86_step "FFD0";            (* call eax *)
  val th = x86_step "0FB110";          (* cmpxchg [eax],edx *)
  val th = x86_step "0FC11E";          (* xadd [esi],ebx *)
  val th = x86_step "93";              (* xchg eax, ebx *)
  val th = x86_step "8731";            (* xchg [ecx], esi *)
  val th = x86_step "F720";            (* mul dword [eax] *)
  val th = x86_step "F7F6";            (* div esi *)

  (* not sure *)

  val th = x86_step "60";              (* pushad *)
  val th = x86_step "61";              (* popad *)

*)

val _ = output_words_as_hex();

fun x86_test_aux inst input output = let
  val rw = x86_step inst
  fun format state (i,j) =
    if i = "EIP"
    then ("XREAD_EIP "^state^" = 0x"^j^"w")
    else if length (explode i) = 3
    then ("XREAD_REG "^i^" "^state^" = 0x"^j^"w")
    else if length (explode i) = 2
    then ("XREAD_EFLAG X_"^i^" "^state^" = SOME "^j)
    else ("XREAD_MEM 0x"^i^"w "^state^" = SOME (0x"^j^"w)")
  fun p y = Parse.Term [QUOTE y]
  fun f s = map (p o format s)
  val th = foldr (fn (x,y) => DISCH x y) rw (f "s" input)
  val th = SIMP_RULE std_ss [Xrm_distinct,Xrm_11,Xreg_distinct,Xeflags_distinct] th
  val th = SIMP_RULE std_ss [word_add_n2w,WORD_ADD_0,b2w_def,bits2num_def,GSYM AND_IMP_INTRO] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_n2w,word_mul_n2w,word_add_n2w,word_sub_def,word_2comp_n2w] th
  val ss = eval_term_ss "a" ``(bytes2word (xs:word8 list)):word32``
  val th = SIMP_RULE (std_ss++ss++SIZES_ss) [n2w_11] th
  val th = ONCE_REWRITE_RULE [XREAD_EIP_ADD_0] th
  val th = REWRITE_RULE [AND_IMP_INTRO] th
  val th = REWRITE_RULE [GSYM CONJ_ASSOC] th
  val xs = find_terms (can (match_term ``XWRITE_EFLAG x NONE``)) (concl th)
  val xs = map (implode o tl o tl o explode o fst o dest_const o snd o dest_comb o fst o dest_comb) xs
  fun distinct [] = [] | distinct (x::xs) = x::distinct (filter (fn y => not (y = x)) xs)
  val xs = distinct xs
  val output2 = filter (fn (x,y) => not (mem x xs)) output
  val output1 = filter (fn (x,y) => mem x xs) output
  val _ = map (fn (x,y) => print ("  Value of "^x^" is left unspecified by model.\n")) output1
  val tm = list_mk_conj (f "(THE (X86_NEXT s))" output2)
  val tm2 = (hd o hyp o UNDISCH) th
  val goal = mk_imp(tm2,tm)
(*
  set_goal([],goal)
*)
  val result = prove(goal,
    STRIP_TAC
    THEN (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO]) th
    THEN ASM_SIMP_TAC std_ss [XREAD_CLAUSES,optionTheory.THE_DEF,Xreg_distinct,Xeflags_distinct]
    THEN STRIP_ASSUME_TAC x86_state_EXPAND
    THEN FULL_SIMP_TAC std_ss [XREAD_REG_def,XREAD_EFLAG_def,XREAD_MEM_def,XREAD_EIP_def,
           XWRITE_MEM_def,XWRITE_REG_def,XWRITE_EFLAG_def,XWRITE_EIP_def, APPLY_UPDATE_THM,Xreg_distinct]
    THEN EVAL_TAC)
  val result = REWRITE_RULE [GSYM AND_IMP_INTRO] result
  in result end;

fun x86_test inst input output = let
  fun p s = if length (explode s) < 4 then s else "["^s^"]"
  val _ = print ("\nTesting:\n  instruction = "^inst^"\n")
  val _ = print ("Input:\n")
  val _ = map (fn (x,y) => print ("  "^(p x)^" = "^y^"\n")) input
  val _ = print ("Output:\n")
  val _ = map (fn (x,y) => print ("  "^(p x)^" = "^y^"\n")) output
  val _ = print ("Result:\n")
  val th = SOME (x86_test_aux inst input output) handle e => NONE
  in case th of
      NONE => (print "  Test failed.\n"; TRUTH)
    | SOME th => (print "  Test successful.\n\n"; print_thm th; print "\n\n"; th)
  end;


end
