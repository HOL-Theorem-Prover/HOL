structure prog_x86Lib :> prog_x86Lib =
struct

open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory x86_Theory x86_Lib helperLib;
open x86_seq_monadTheory x86_coretypesTheory x86_astTheory x86_icacheTheory;
open prog_x86Theory;

val x86_status = xS_HIDE;
val x86_pc = ``xPC``;
val x86_exec_flag = ref false;
val x86_code_write_perm = ref false;
val x86_use_stack = ref false;
fun set_x86_exec_flag b = (x86_exec_flag := b);
fun set_x86_code_write_perm_flag b = (x86_code_write_perm := b);
fun set_x86_use_stack b = (x86_use_stack := b);

fun name_for_resource counter tm = let
  val to_lower_drop_two = implode o tl o tl o explode o to_lower
  in if type_of tm = ``:Xreg`` then (to_lower o fst o dest_const) tm else
     if type_of tm = ``:Xeflags`` then (to_lower_drop_two o fst o dest_const) tm else
     (counter := 1 + !counter; ("x" ^ int_to_string (!counter))) end;

fun pre_process_thm th = let
  val x = ref 0
  fun all_distinct [] = []
    | all_distinct (x::xs) = x :: all_distinct (filter (fn y => x !~ y) xs)
  val rs = find_terml (fn tm => type_of tm = ``:Xreg``) (concl th)
  val fs = find_terml (fn tm => type_of tm = ``:Xeflags``) (concl th)
  val ws = find_terml (can (match_term ``XREAD_MEM2_WORD a``)) (concl th)
  val ws = ws @ find_terml (can (match_term ``XWRITE_MEM2_WORD a``)) (concl th)
  val ws = all_distinct (map cdr ws)
  val bs = find_terml (can (match_term ``XREAD_MEM2 a``)) (concl th)
  val bs = bs @ find_terml (can (match_term ``XWRITE_MEM2 a``)) (concl th)
  val bs = all_distinct (map cdr bs)
  fun make_eq_tm pattern lhs name = let
    val var = mk_var(name_for_resource x name, type_of pattern)
    in mk_eq(subst [lhs |-> name] pattern,var) end
  val rs2 = map (make_eq_tm ``XREAD_REG r s`` ``r:Xreg``) rs
  val fs2 = map (make_eq_tm ``XREAD_EFLAG f s`` ``f:Xeflags``) fs
  val ws2 = map (make_eq_tm ``XREAD_MEM2_WORD a s`` ``a:word32``) ws
  val bs2 = map (make_eq_tm ``XREAD_MEM2 a s`` ``a:word32``) bs
  val result = rs2 @ fs2 @ ws2 @ bs2 @ [``XREAD_EIP s = eip``]
  val th = foldr (uncurry DISCH) th result
  val th = RW [AND_IMP_INTRO,GSYM CONJ_ASSOC,wordsTheory.WORD_XOR_CLAUSES,
             wordsTheory.WORD_AND_CLAUSES,wordsTheory.WORD_ADD_0] (SIMP_RULE std_ss [] th)
  in th end;

fun x86_pre_post g s = let
  val h = g
  val xs = find_terml (can (match_term ``(XREAD_REG x s = y)``)) h
         @ find_terml (can (match_term ``(XREAD_MEM2_WORD x s = y)``)) h
         @ find_terml (can (match_term ``(XREAD_MEM2 x s = y)``)) h
         @ find_terml (can (match_term ``(XREAD_EFLAG x s = y)``)) h
  val xs = map (fn tm => ((cdr o car o cdr o car) tm, cdr tm)) xs
  val ys = find_terml (can (match_term ``XWRITE_EFLAG a x``)) h
         @ find_terml (can (match_term ``XWRITE_MEM2 a x``)) h
         @ find_terml (can (match_term ``XWRITE_MEM2_WORD a x``)) h
         @ find_terml (can (match_term ``XWRITE_REG a x``)) h
  val ys = map (fn tm => ((cdr o car) tm, cdr tm)) ys
  val new_eip = (cdr o hd) (find_terml (can (match_term ``XWRITE_EIP e``)) h)
  fun assigned_aux x y [] = y
    | assigned_aux x y ((q,z)::zs) = if aconv x q then z else assigned_aux x y zs
  fun get_assigned_value x y = assigned_aux x y ys
  fun mk_pre_post_assertion (name,var) = let
    val (pattern,name_tm,var_tm) =
          if type_of name = ``:Xreg`` then
            (``xR a w``,``a:Xreg``,``w:word32``)
          else if type_of name = ``:Xeflags`` then
            (``xS1 a w``,``a:Xeflags``,``w:bool option``)
          else if type_of var = ``:word8`` then
            (``~(xM1 a (SOME (w,xDATA_PERM ex)))``,``a:word32``,``w:word8``)
          else if type_of var = ``:word32`` then
            (``xM a w``,``a:word32``,``w:word32``) else fail()
    in (subst [name_tm|->name,var_tm|->var] pattern,
        subst [name_tm|->name,var_tm|->get_assigned_value name var] pattern) end
  val pre_post = map mk_pre_post_assertion xs
  val pre = list_mk_star (map fst pre_post) ``:x86_set -> bool``
  val post = list_mk_star (map snd pre_post) ``:x86_set -> bool``
  fun is_precond tm =
   (not (can (match_term ``XREAD_REG r s = v``) tm) andalso
    not (can (match_term ``XREAD_MEM2 r s = v``) tm) andalso
    not (can (match_term ``XREAD_MEM2_WORD r s = v``) tm) andalso
    not (can (match_term ``CAN_XWRITE_MEM r s``) tm) andalso
    not (can (match_term ``CAN_XREAD_MEM r s``) tm) andalso
    not (can (match_term ``XREAD_INSTR r s = v``) tm) andalso
    not (can (match_term ``XREAD_EFLAG r s = v``) tm) andalso
    not (can (match_term ``XREAD_EIP s = v``) tm)) handle e => true
  val all_conds = (list_dest dest_conj o fst o dest_imp) h
  val pre_conds = (filter is_precond) all_conds
  val ss = foldr (fn (x,y) => (fst (dest_eq x) |-> snd (dest_eq x)) :: y handle e => y) []
             (filter is_precond pre_conds)
  val ss = ss @ map ((fn tm => mk_var((fst o dest_var o cdr) tm,``:bool option``) |-> tm) o cdr)
    (filter (can (match_term ``XREAD_EFLAG x s = SOME y``)) all_conds)
  val pre = subst ss pre
  val post = subst ss post
  val pre = mk_star (pre,``xPC eip``)
  val post = mk_star (post,mk_comb(``xPC``,new_eip))
  val pre = if null pre_conds then pre else mk_cond_star(pre,mk_comb(``Abbrev``,list_mk_conj pre_conds))
  in (pre,post) end;

fun introduce_xMEMORY th = let
  val (_,p,c,q) = dest_spec(concl th)
  val tm = find_term (can (match_term ``xM x y``)) p
  val c = LIST_MOVE_OUT_CONV true [car tm]
  val th = CONV_RULE (POST_CONV c THENC PRE_CONV c) th
  val th = MATCH_MP xMEMORY_INTRO (RW [GSYM STAR_ASSOC] th)
  val th = RW [GSYM progTheory.SPEC_MOVE_COND,STAR_ASSOC] th
  fun replace_access_in_pre th = let
    val (_,p,c,q) = dest_spec(concl th)
    val tm = find_term (can (match_term ``(a:'a =+ w:'b) f``)) p
    val (tm,y) = dest_comb tm
    val (tm,x) = dest_comb tm
    val a = snd (dest_comb tm)
    val th = REWRITE_RULE [APPLY_UPDATE_ID] (INST [x |-> mk_comb(y,a)] th)
    in th end handle e => th
  val th = replace_access_in_pre th
  in th end handle e => th;

fun introduce_xBYTE_MEMORY_ANY th = let
  val (_,p,c,q) = dest_spec(concl th)
  val tm1 = find_term (can (match_term ``xM1 x y``)) p
  val tm2 = find_term (can (match_term ``xM1 x y``)) q
  val c1 = LIST_MOVE_OUT_CONV true [tm1]
  val c2 = LIST_MOVE_OUT_CONV true [tm2]
  val th = CONV_RULE (POST_CONV c2 THENC PRE_CONV c1) th
  val th = MATCH_MP xBYTE_MEMORY_ANY_INTRO (RW [GSYM STAR_ASSOC] th)
  val th = RW [GSYM progTheory.SPEC_MOVE_COND,STAR_ASSOC] th
  fun replace_access_in_pre th = let
    val (_,p,c,q) = dest_spec(concl th)
    val tm = find_term (can (match_term ``(a:'a =+ w:'b) f``)) p
    val (tm,y) = dest_comb tm
    val (tm,x) = dest_comb tm
    val a = snd (dest_comb tm)
    val th = REWRITE_RULE [APPLY_UPDATE_ID] (INST [x |-> mk_comb(y,a)] th)
    in th end handle e => th
  val th = replace_access_in_pre th
  in th end handle e => th;

fun introduce_xSTACK th =
  if not (!x86_use_stack) then th else let
  val (_,p,c,q) = dest_spec(concl th)
  val ebp = mk_var("ebp",``:word32``)
  fun access_ebp tm = (tm ~~ ebp) orelse
    (can (match_term ``(v:word32) - n2w n``) tm andalso (ebp ~~ (cdr o car) tm))
  val tm1 = find_term (fn tm =>
              can (match_term ``xM x y``) tm andalso (access_ebp o cdr o car) tm) p
  val tm2 = find_term (can (match_term (mk_comb(car tm1,genvar(``:word32``))))) q
  val c1 = MOVE_OUT_CONV ``xR EBP`` THENC MOVE_OUT_CONV (car tm1)
  val c2 = MOVE_OUT_CONV ``xR EBP`` THENC MOVE_OUT_CONV (car tm2)
  val th = CONV_RULE (POST_CONV c2 THENC PRE_CONV c1) th
  val th = DISCH ``ALIGNED ebp`` th
  val th = MATCH_MP xSTACK_INTRO_EBX th
  fun mk_stack_var i = mk_var("s" ^ int_to_string i,``:word32``)
  val index = (Arbnum.toInt o numSyntax.dest_numeral o cdr o cdr o cdr o car) tm1
  val index = index div 4
  fun mk_slist i = if i = 0 then ``[]:word32 list`` else
                     listSyntax.mk_cons(mk_stack_var (index - i), mk_slist (i-1))
  val th = SPECL [mk_slist index,mk_var("ss",``:word32 list``)] th
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [listTheory.LENGTH]) THENC
                      REWRITE_CONV [listTheory.APPEND]) th
  val th = INST [cdr tm1 |-> mk_stack_var index] th
  in th end handle e => th;

fun calculate_length_and_jump th = let
  val (_,_,c,q) = dest_spec (concl th)
  val l = (length o fst o listSyntax.dest_list o cdr o car o cdr o cdr o car) c
  in
    let val v = find_term (can (match_term ``xPC (p + n2w n)``)) q
    in (th,l,SOME (0 + (numSyntax.int_of_term o cdr o cdr o cdr) v)) end
  handle e =>
    let val v = find_term (can (match_term ``xPC (p - n2w n)``)) q
    in (th,l,SOME (0 - (numSyntax.int_of_term o cdr o cdr o cdr) v)) end
  handle e =>
    (th,l,NONE) end

fun post_process_thm th = let
  val th = SIMP_RULE (std_ss++sw2sw_ss++w2w_ss) [wordsTheory.word_mul_n2w,SEP_CLAUSES] th
  val th = CONV_RULE FIX_WORD32_ARITH_CONV th
  val th = introduce_xSTACK th
  val th = introduce_xMEMORY th
  val th = introduce_xBYTE_MEMORY_ANY th
  val th = SIMP_RULE (std_ss++sw2sw_ss++w2w_ss) [GSYM wordsTheory.WORD_ADD_ASSOC,
    word_arith_lemma1,word_arith_lemma2,word_arith_lemma3,word_arith_lemma4] th
  val th = CONV_RULE FIX_WORD32_ARITH_CONV th
  val th = RW [wordsTheory.WORD_ADD_ASSOC,wordsTheory.WORD_ADD_0] th
  fun f th = let
    val x = find_term (can (match_term ``(THE x):'a``)) (concl th)
    val y = optionSyntax.mk_some(mk_var(fst (dest_var (cdr x)),type_of x))
    val th = INST [cdr x |-> y] th
    val th = SIMP_RULE bool_ss [SEP_CLAUSES,optionLib.option_rws] th
    in th end
  val th = repeat f th
  val th = RW [ALIGNED_def] th
  val th = SIMP_RULE std_ss [wordsTheory.WORD_EQ_SUB_ZERO,w2w_eq_n2w,w2w_CLAUSES] th
  in calculate_length_and_jump th end;

fun calc_code th = let
  val tms = find_terml (can (match_term ``XREAD_INSTR a s = SOME x``)) (concl th)
  val tms = map dest_eq tms
  fun addr tm = (Arbnum.toInt o numSyntax.dest_numeral o cdr o cdr o cdr o car) tm
                handle e => 0
  val tms = map (fn (x,y) => (addr x, cdr y)) tms
  val code = map snd (sort (fn (x,_) => fn (y,_) => x <= y) tms)
  in listSyntax.mk_list (code, ``:word8``) end;

fun x86_prove_one_spec th c = let
  val g = concl th
  val s = find_term (can (match_term ``X86_NEXT x = SOME y``)) g
  val s = (snd o dest_comb o snd o dest_comb) s
  val (pre,post) = x86_pre_post g s
  val tm = ``SPEC X86_MODEL pre {(eip,(c,w))} post``
  val tm = subst [mk_var("pre",type_of pre) |-> pre,
                  mk_var("post",type_of post) |-> post,
                  mk_var("c",type_of c) |-> c] tm
  val FLIP_TAC = CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ])
  val th1 = Q.INST [`s`|->`X86_ICACHE_UPDATE x (r,e,t,m,i)`] th
  val th1 = RW [XREAD_CLAUSES,XWRITE_MEM2_WORD_def] th1
  val th1 = RW [XWRITE_EFLAG_def,X86_ICACHE_UPDATE_def,XWRITE_MEM2_def,XWRITE_REG_def,
        APPLY_UPDATE_THM,WORD_EQ_ADD_CANCEL,x86_address_lemma,XWRITE_EIP_def] th1
  val th = prove(tm,
(*
    set_goal([],tm)
*)
    MATCH_MP_TAC IMP_X86_SPEC \\ REPEAT STRIP_TAC
    \\ EXISTS_TAC ((cdr o cdr o concl o UNDISCH) th1)
    \\ STRIP_TAC \\ REWRITE_TAC [X86_ICACHE_UPDATE_def]
    THENL [MATCH_MP_TAC th1,ALL_TAC]
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x86_2set, IN_DELETE, APPLY_UPDATE_THM, Xreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Xeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET, SEP_CLAUSES,X86_ICACHE_UPDATE_def,XCLEAR_ICACHE_def,
         X86_ICACHE_REVERT_def,xM_def,WORD_EQ_ADD_CANCEL,x86_address_lemma]
    \\ ONCE_REWRITE_TAC [CODE_POOL_x86_2set]
    \\ REWRITE_TAC [listTheory.LENGTH,address_list_def]
    \\ SIMP_TAC std_ss [arithmeticTheory.ADD1,X86_ICACHE_EXTRACT_def]
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x86_2set, IN_DELETE, APPLY_UPDATE_THM, Xreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Xeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET,x86_pool_def,X86_ACCURATE_CLAUSES]
    \\ SIMP_TAC std_ss [XREAD_REG_def,XREAD_EFLAG_def,XREAD_EIP_def]
    \\ NTAC 3 (FLIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO])
    \\ SIMP_TAC std_ss [CAN_XREAD_MEM,CAN_XWRITE_MEM,IN_INSERT]
    \\ SIMP_TAC std_ss [XREAD_MEM2_WORD_def,XREAD_MEM2_def,wordsTheory.WORD_ADD_0]
    \\ SIMP_TAC std_ss [bit_listTheory.bytes2word_thm,IN_xDATA_PERM]
    THEN1 (SIMP_TAC std_ss [markerTheory.Abbrev_def]
           \\ REPEAT STRIP_TAC \\ FLIP_TAC \\ MATCH_MP_TAC XREAD_INSTR_IMP
           \\ Q.EXISTS_TAC `w` \\ ASM_SIMP_TAC std_ss []
           \\ FULL_SIMP_TAC std_ss [wordsTheory.word_add_n2w,GSYM wordsTheory.WORD_ADD_ASSOC])
    \\ SIMP_TAC std_ss [word2bytes_thm,EL_thm,INSERT_SUBSET,IN_INSERT,EMPTY_SUBSET]
    \\ FULL_SIMP_TAC std_ss [UPDATE_x86_2set'',word_arith_lemma1,
         ALIGNED_CLAUSES,icache_revert_ID,X86_ACCURATE_UPDATE]
    \\ SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ STRIP_TAC \\ IMP_RES_TAC X86_ACCURATE_IMP
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def])
  val th = INST [``w:bool``|-> (if !x86_code_write_perm then T else F)] th
  in RW [STAR_ASSOC,SEP_CLAUSES,markerTheory.Abbrev_def] th end;

fun x86_prove_specs s = let
  val th = x86_step s
  val c = calc_code th
  val th = pre_process_thm th
  fun replace_conv th tm = if (fst o dest_eq o concl) th ~~ tm then th else ALL_CONV tm
  in if (is_cond o cdr o cdr o snd o dest_imp o concl) th then let
       val (x,y,z) = dest_cond (find_term is_cond (concl th))
       fun prove_branch cth th = let
         val tm1 = (fst o dest_imp o concl o ISPECL [x,y,z]) cth
         val th1 = CONV_RULE (DEPTH_CONV (replace_conv (UNDISCH (ISPECL [x,y,z] cth)))) th
         val th1 = (RW [AND_IMP_INTRO,GSYM CONJ_ASSOC] o DISCH_ALL) th1
         val th1 = x86_prove_one_spec th1 c
         val th1 = SIMP_RULE std_ss [SEP_CLAUSES] (DISCH tm1 th1)
         val th1 = RW [CONTAINER_def] th1
         val th1 = RW [RW [GSYM precond_def] (GSYM progTheory.SPEC_MOVE_COND)] th1
         in post_process_thm th1 end
       in (prove_branch CONTAINER_IF_T th, SOME (prove_branch CONTAINER_IF_F th)) end
     else (post_process_thm (x86_prove_one_spec th c),NONE) end

fun x86_jump (tm1:term) (tm2:term) (jump_length:int) (forward:bool) = ("",0)

val x86_spec_aux = cache x86_prove_specs;
fun x86_spec s = let
  val (s,rename,exec_flag) = parse_renamer s
  val ((th,i,j),other) = x86_spec_aux s
  val b = if exec_flag then T else F
  val th = INST [``ex:bool``|->b] th
  val th = RW [GSYM xBYTE_MEMORY_def,GSYM xBYTE_MEMORY_X_def] th
  val other = case other of NONE => NONE | SOME (th,i,j) => SOME (rename th,i,j)
  in ((rename th,i,j),other) end

val x86_tools = (x86_spec, x86_jump, x86_status, x86_pc)
val x86_tools_no_status = (x86_spec, x86_jump, TRUTH, x86_pc);

(*

open x86_encodeLib;

  val th = x86_spec "40";              (* inc eax *)
  val th = x86_spec "F7C203000000";    (* test edx,3 *)
  val th = x86_spec "89EE";            (* mov esi,ebp *)
  val th = x86_spec "81E603000000";    (* and esi,3 *)
  val th = x86_spec "4E";              (* dec esi *)
  val th = x86_spec "89EA";            (* mov edx,ebp *)
  val th = x86_spec "4A";              (* dec edx *)
  val th = x86_spec "89CD";            (* mov ebp,ecx *)
  val th = x86_spec "45";              (* inc ebp *)
  val th = x86_spec "EBF7";            (* jmp L1 *)
  val th = x86_spec "8B36";            (* mov esi, [esi] *)
  val th = x86_spec "8B2A";            (* mov ebp,[edx] *)
  val th = x86_spec "8B7204";          (* mov esi,[edx+4] *)
  val th = x86_spec "8929";            (* mov [ecx],ebp *)
  val th = x86_spec "897104";          (* mov [ecx+4],esi *)
  val th = x86_spec "892A";            (* mov [edx],ebp *)
  val th = x86_spec "813337020000";    (* xor dword [ebx],567 *)
  val th = x86_spec "310B";            (* xor [ebx], ecx *)
  val th = x86_spec "F720";            (* mul dword [eax] *)
  val th = x86_spec "F7F6";            (* div esi *)
  val th = x86_spec "883E";            (* mov_byte [esi],edi *)
  val th = x86_spec "0FB63E";          (* mov_byte edi,[esi] *)
  val th = x86_spec "E2FD";            (* loop L *)
  val th = x86_spec "751D";            (* jne L1 *)
  val th = x86_spec "740D";            (* je L2 *)
  val th = x86_spec "0F44C1";          (* cmove eax, ecx *)
  val th = x86_spec (x86_encode "mov_byte [esi],-10")

  val th = x86_spec "31C0";
  val th = x86_spec "85F6";
  val th = x86_spec "8B36";
  val th = x86_spec "85F6";
  val th = x86_spec "7405";

  val th = x86_spec (x86_encode "jmp edx")
  val th = x86_spec (x86_encode "add [ebp-20],eax")

  val th = x86_spec
val s = (x86_encode "mov [edi+400],3477")

  val th = x86_spec "813337020000";    (* mov dword [ebx],567 *)

  val th = x86_spec "E9";              (* jmp imm32 *)

*)

end
