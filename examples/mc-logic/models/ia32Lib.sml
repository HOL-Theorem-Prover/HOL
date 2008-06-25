structure ia32Lib :> ia32Lib =
struct
 
open HolKernel boolLib bossLib;
open wordsLib stringLib listSyntax simpLib listTheory wordsTheory;
open opmonTheory bit_listTheory combinTheory;

open ia32Theory;


(* decoder *)

fun nTimes n f x = if n = 0 then x else nTimes (n-1) f (f x) 

fun eval_term_ss tm_name tm = conv_ss 
  { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };

fun raw_ia32_decode s = let
  fun mk_bool_list n = 
    if n = 0 then ``[]:bool list`` else 
      mk_cons(mk_var("vvv"^int_to_string n,``:bool``),mk_bool_list (n-1))
  val l = length (explode s) div 2
  val tm = mk_bool_list (8 * (20 - l))
  val tm = subst [``s:string`` |-> fromMLstring s, ``t:bool list``|->tm] ``bytebits s ++ t``
  val tm = (snd o dest_eq o concl o EVAL) tm
  val th = EVAL (mk_comb(``x86_decode``,tm))
  val _  = computeLib.add_funs [th]
  in (th,tm,l) end;

fun ia32_decode s = let
  val (th,tm,l) = raw_ia32_decode s
  val th = MATCH_MP X86_NEXT_THM th
  val th = SIMP_RULE std_ss [LENGTH] th  
  val th = nTimes l (SIMP_RULE std_ss [EVERY_DEF] o ONCE_REWRITE_RULE [XREAD_MEM_BYTES_def]) th
  fun assums i n = 
    if i = 0 then [] else 
      subst [``n:num``|->numSyntax.term_of_int n]
       ``XREAD_MEM (e + n2w n) (r,f,e,m) = SOME (b2w I (TAKE 8 (DROP (8 * n) t)))`` :: assums (i-1) (n+1)
  val th = foldr (uncurry DISCH) th (assums l 0)
  val th = SIMP_RULE std_ss [WORD_ADD_0,GSYM WORD_ADD_ASSOC,word_add_n2w] th
  val th = INST [``t:bool list``|->tm] th
  val b2w_ss = eval_term_ss "b2w" ``(TAKE n t):bool list``
  val w2bits_ss = eval_term_ss "w2bits" ``w2bits ((b2w I x):word8):bool list``
  val th = SIMP_RULE (std_ss++b2w_ss) [FOLDR,MAP] th
  val th = SIMP_RULE (std_ss++w2bits_ss) [FOLDR,MAP,APPEND,CONS_11] th
  val th = nTimes l UNDISCH th
  val th = nTimes 20 (SIMP_RULE std_ss [EVERY_DEF,GSYM WORD_ADD_ASSOC,word_add_n2w] o ONCE_REWRITE_RULE [XREAD_MEM_BYTES_def]) th
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
  in th end;



(* one step symbolic simulation *)

fun tac g = prove(g,  Cases THEN SIMP_TAC std_ss []);

val if_some_lemma = tac
  ``!b x y:'a. (if b then SOME x else SOME y) = SOME (if b then x else y)``;
val pull_if_lemma = tac
  ``!b x y (f:'a->'b). f (if b then x else y) = if b then f x else f y``;
val else_none_lemma = (UNDISCH o SPEC_ALL o tac) 
  ``!b. b ==> ((if b then x:'a option else NONE) = x)``;

val ss = rewrites [x86_execute_def, x86_exec_def, LOCAL_def,
  XREAD_REG_def, XREAD_EFLAG_def, XREAD_EIP_def, XREAD_MEM_def,
  XWRITE_REG_def, XWRITE_EFLAG_def, XWRITE_EIP_def, XWRITE_MEM_def,
  read_reg_def, read_eip_def, read_eflag_def, write_reg_def,
  write_eip_def, write_eflag_def, write_CF_flag_def, unset_flag_def,
  set_flag_def, calc_PF_def, calc_ZF_def, calc_SF_def,
  option_then_assoc, calc_logical_op_eflags_def, opt_push_const_def,
  calc_arith_op_eflags_except_CF_def, calc_arith_op_eflags_def,
  XWRITE_MEM_BYTES_def, XREAD_MDATA_def, XWRITE_MDATA_def,
  mem_access_ok_def, read_mem_def, write_mem_def, ea_Xr_def,
  ea_Xi_def, ea_Xrm_base_def, ea_Xrm_index_def, ea_Xrm_def,
  ea_Xdest_def, ea_Xsrc_def, ea_Ximm_rm_def, load_ea_aux_def,
  load_ea_def, store_ea_aux_def, store_ea_def, next_eip_def,
  bump_eip_def, add_with_carry_out_def, sub_with_borrow_out_def,
  store_arith_op_result_def, do_binop_def, do_monop_def, opt_thm,
  eval_cond_def, x86_exec_def, x86_execute_def, option_parallel_def,
  opt_monop_the_def, opt_cond_def, opt_s_pop_def, if_some_lemma,
  XREAD_MEM_BYTES_thm, EVERY_DEF, word2bytes_thm, WORD_MULT_CLAUSES,
  WORD_ADD_0, GSYM WORD_ADD_ASSOC, word_add_n2w, MAP, Xcond_distinct,
  APPLY_UPDATE_THM, option_fail_def, Xeflags_distinct];

val else_none_conv = 
  let val tm1 = (fst o dest_eq o concl) else_none_lemma in 
    fn tm => (let val (i,t) = match_term tm1 tm
              in INST i (INST_TYPE t else_none_lemma) end) end;

fun ia32_step s = let
  val th = ia32_decode s
  val tm = (fst o dest_eq o fst o dest_imp o concl) th
  val th1 = SIMP_CONV (std_ss++ss++wordsLib.SIZES_ss) [] tm;
  fun cc th = CONV_RULE (ONCE_DEPTH_CONV else_none_conv) th handle e => th
  val th1 = SIMP_RULE std_ss [WORD_OR_IDEM, LET_DEF] (DISCH_ALL (cc th1))
  val th1 = SIMP_RULE std_ss [WORD_OR_IDEM, LET_DEF] (DISCH_ALL (cc th1))
  val th1 = SIMP_RULE std_ss [WORD_OR_IDEM, LET_DEF] (DISCH_ALL (cc th1))
  val th1 = SIMP_RULE std_ss [WORD_OR_IDEM, LET_DEF] (DISCH_ALL (cc th1))
  val th1 = DISCH_ALL (MATCH_MP th (UNDISCH_ALL th1))
  val th1 = SIMP_RULE bool_ss [pull_if_lemma, pairTheory.SND] th1
  in REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] (DISCH_ALL th1) end;

(*

  test cases:

val s = "0538000000"

  val th = ia32_step "0538000000";      (* add eax,56 *)
  val th = ia32_step "810037020000";    (* add dword [eax],567 *)
  val th = ia32_step "010B";            (* add [ebx], ecx *)
  val th = ia32_step "0119";            (* add [ecx], ebx *)
  val th = ia32_step "2538000000";      (* and eax,56 *)
  val th = ia32_step "812037020000";    (* and dword [eax],567 *)
  val th = ia32_step "210B";            (* and [ebx], ecx *)
  val th = ia32_step "2319";            (* and ebx, [ecx] *)
  val th = ia32_step "0F44C1";          (* cmove eax, ecx *)
  val th = ia32_step "0F454104";        (* cmovne eax, [ecx+4] *)
  val th = ia32_step "81FE38000000";    (* cmp esi,56 *)
  val th = ia32_step "813B37020000";    (* cmp dword [ebx],567 *)
  val th = ia32_step "390B";            (* cmp [ebx], ecx *)
  val th = ia32_step "3B19";            (* cmp ebx, [ecx] *)
  val th = ia32_step "893E";            (* mov [esi],edi *)
  val th = ia32_step "8B3E";            (* mov edi,[esi] *)
  val th = ia32_step "BC37020000";      (* mov esp,567 *)
  val th = ia32_step "81CE38000000";    (* or  esi,56 *)
  val th = ia32_step "810B37020000";    (* or  dword [ebx],567 *)
  val th = ia32_step "090B";            (* or  [ebx], ecx *)
  val th = ia32_step "0B19";            (* or  ebx, [ecx] *)
  val th = ia32_step "81EE38000000";    (* sub esi,56 *)
  val th = ia32_step "812B37020000";    (* sub dword [ebx],567 *)
  val th = ia32_step "290B";            (* sub [ebx], ecx *)
  val th = ia32_step "2B19";            (* sub ebx, [ecx] *)
  val th = ia32_step "F7C638000000";    (* test esi,56 *)
  val th = ia32_step "F70337020000";    (* test dword [ebx],567 *)
  val th = ia32_step "850B";            (* test [ebx], ecx *)
  val th = ia32_step "81F638000000";    (* xor esi,56 *)
  val th = ia32_step "813337020000";    (* xor dword [ebx],567 *)
  val th = ia32_step "310B";            (* xor [ebx], ecx *)
  val th = ia32_step "3319";            (* xor ebx, [ecx] *)
  val th = ia32_step "0FB110";          (* cmpxchg [eax],edx *)
  val th = ia32_step "0FC11E";          (* xadd [esi],ebx *)
  val th = ia32_step "FF4E3C";          (* dec dword [esi+60] *)

  val th = ia32_step "4C";              (* dec esp *)

  val th = ia32_step "FF80401F0000";    (* inc dword [eax+8000] *)
  val th = ia32_step "40";              (* inc eax *)
  val th = ia32_step "F750C8";          (* not dword [eax-56] *)
  val th = ia32_step "F720";            (* mul dword [eax] *)
  val th = ia32_step "F7F6";            (* div esi *)
  val th = ia32_step "8F0590010000";    (* pop dword [400] *)
  val th = ia32_step "59";              (* pop ecx *)
  val th = ia32_step "FFB498C8010000";  (* push dword [eax + 4*ebx + 456] *)
  val th = ia32_step "FF749801";        (* push dword [eax + 4*ebx + 1] *)
  val th = ia32_step "FF74AD02";        (* push dword [ebp + 4*ebp + 2] *)
  val th = ia32_step "FF746D2D";        (* push dword [ebp + 2*ebp + 45] *)
  val th = ia32_step "FFB42DEA000000";  (* push dword [ebp + ebp + 234] *)
  val th = ia32_step "FFB4B6EE711202";  (* push dword [esi + 4*esi + 34763246] *)
  val th = ia32_step "50";              (* push eax *)
  val th = ia32_step "E8BDFFFFFF";      (* call l1 *)
  val th = ia32_step "FFD0";            (* call eax *)
  val th = ia32_step "EBB9";            (* jmp l1 *)
  val th = ia32_step "74B7";            (* je l1 *)
  val th = ia32_step "75B5";            (* jne l1 *)
  val th = ia32_step "C3";              (* ret *)
  val th = ia32_step "C20500";          (* ret 5 *)
  val th = ia32_step "E2AF";            (* loop l1 *)
  val th = ia32_step "E1AD";            (* loope l1 *)
  val th = ia32_step "E0AB";            (* loopne l1 *)
  val th = ia32_step "60";              (* pushad *)
  val th = ia32_step "61";              (* popad *)
  val th = ia32_step "0FAEF0";          (* mfence *)
  val th = ia32_step "0FAEF8";          (* sfence *)
  val th = ia32_step "0FAEE8";          (* lfence *)
  val th = ia32_step "93";              (* xchg eax, ebx *)
  val th = ia32_step "8731";            (* xchg [ecx], esi *)
  val th = ia32_step "F7583C";          (* neg dword [eax+60] *)

*)


end
