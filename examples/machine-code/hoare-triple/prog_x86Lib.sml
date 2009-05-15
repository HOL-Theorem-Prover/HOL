structure prog_x86Lib :> prog_x86Lib =
struct
 
open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory x86_Theory x86_Lib prog_x86Theory helperLib;
open x86_seq_monadTheory x86_coretypesTheory x86_astTheory;

infix \\ 
val op \\ = op THEN;
val eq = Term.eq;


val x86_status = xS_HIDE;
val x86_pc = ``xPC``;

fun process v tm = let
  fun replace_plus c = if c = #"+" then #"_" else c;
  fun name_of_tm tm = 
    "m_" ^ (implode o filter is_normal_char o map replace_plus o explode o term_to_string) tm;
  val to_lower_drop_two = implode o tl o tl o explode o to_lower
  in if type_of tm = ``:Xreg`` then 
       (mk_comb(``xR1``,tm),mk_var((to_lower o fst o dest_const) tm,``:word32``))
     else if type_of tm = ``:Xeflags`` then 
       (mk_comb(``xS1``,tm),mk_var((to_lower_drop_two o fst o dest_const) tm,``:bool option``))
     else if type_of tm = ``:word32`` then
       (mk_comb(``xM1``,tm),v)
     else hd [] end;

fun pre_process_thm th = let
  val rs = find_terml (can (match_term ``XREAD_REG x s``)) (concl th)
  val fs = find_terml (can (match_term ``XREAD_EFLAG x s``)) (concl th)
  val regs = map (fn tm => mk_eq(tm,(snd o process T o cdr o car) tm)) rs
  fun f t = optionSyntax.mk_some o (fn x => mk_var(x,t)) o fst o dest_var
  val flags = map (fn tm => mk_eq(tm,(f ``:bool`` o snd o process T o cdr o car) tm)) fs
  val th = foldr (uncurry DISCH) th (regs @ flags @ [``XREAD_EIP s = eip``])
  val th = SIMP_RULE bool_ss [optionTheory.option_CLAUSES] th
  val ms = find_terml (can (match_term ``~(XREAD_MEM x s = NONE)``)) (concl th)
  val ms = map (fst o dest_eq o dest_neg) ms
  val mems = map (fn tm => mk_eq(tm,f ``:word8`` (genvar(``:bool``)))) ms
  val th = foldr (uncurry DISCH) th mems
  val th = RW [AND_IMP_INTRO,GSYM CONJ_ASSOC,wordsTheory.WORD_XOR_CLAUSES,
             wordsTheory.WORD_AND_CLAUSES] (SIMP_RULE std_ss [] th)
  in th end;

fun x86_pre_post g s = let
  val h = g
  val regs = collect_term_of_type ``:Xreg`` g;
  val bits = collect_term_of_type ``:Xeflags`` g;
  val mems = find_terml (can (match_term ``(XREAD_MEM x s = SOME y)``)) h
  val mems = filter (is_var o cdr o cdr) mems
  val mems = map (fn tm => ((cdr o car o fst o dest_eq) tm, cdr tm)) mems
  val assignments = find_terml (can (match_term ``XWRITE_EFLAG a x``)) h
                  @ find_terml (can (match_term ``XWRITE_REG a x``)) h
                  @ find_terml (can (match_term ``XWRITE_MEM a x``)) h
  val assignments = map (fn tm => (cdr (car tm) handle e => ``EIP``, cdr tm)) assignments  
  val new_eip = (cdr o hd) (find_terml (can (match_term ``XWRITE_EIP e``)) h)
  fun assigned_aux x y [] = y
    | assigned_aux x y ((q,z)::zs) = if eq x q then z else assigned_aux x y zs
  fun get_assigned_value x y = assigned_aux x y assignments
  fun mk_pre_post_assertion (x,v) = let
    val (y,z) = process v x
    val q = get_assigned_value x z
    in (mk_comb(y,z),mk_comb(y,q)) end   
  val pre_post = map mk_pre_post_assertion (map (fn tm => (tm,T)) (regs @ bits) @ mems) 
  val pre = list_mk_star (map fst pre_post) ``:x86_set -> bool``
  val post = list_mk_star (map snd pre_post) ``:x86_set -> bool``
  fun is_precond tm =
   (not (can (match_term ``XREAD_REG r s = v``) tm) andalso
    not (can (match_term ``XREAD_MEM r s = v``) tm) andalso
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
  val tm3 = find_term (can (match_term ``xM1 (x + 3w) y``)) p
  val tm2 = find_term (can (match_term ``xM1 (x + 2w) y``)) p
  val tm1 = find_term (can (match_term ``xM1 (x + 1w) y``)) p
  val tm0 = find_term (can (match_term ``xM1 (x + 0w) y``)) p
  val c = MOVE_OUT_CONV (car tm3) THENC MOVE_OUT_CONV (car tm2) THENC
          MOVE_OUT_CONV (car tm1) THENC MOVE_OUT_CONV (car tm0) THENC STAR_REVERSE_CONV
  val th = CONV_RULE (POST_CONV c THENC PRE_CONV c) th
  val f = cdr o cdr
  fun g th tm tm' = if is_var tm then INST [ tm |-> tm' ] th else th
  val th = g th (f tm0) ``((7 >< 0) (w:word32)):word8``   
  val th = g th (f tm1) ``((7 >< 0) ((w >> 8):word32)):word8``   
  val th = g th (f tm2) ``((7 >< 0) ((w >> 16):word32)):word8``   
  val th = g th (f tm3) ``((7 >< 0) ((w >> 24):word32)):word8``   
  val h = REWRITE_RULE [GSYM STAR_ASSOC,x86_seq_monadTheory.word2bytes_thm,x86_seq_monadTheory.EL_thm] 
  val th = MATCH_MP (h xMEMORY_INTRO) (h th)
  val th = SIMP_RULE bool_ss [GSYM ALIGNED_def,SEP_CLAUSES] th
  val th = REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND,ALIGNED_def,
             STAR_ASSOC,bit_listTheory.bytes2word_thm] th
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

fun introduce_xBYTE_MEMORY th = let
  val (_,p,c,q) = dest_spec(concl th)
  val tm0 = find_term (can (match_term ``xM1 x y``)) p
  val c = MOVE_OUT_CONV (car tm0) THENC STAR_REVERSE_CONV
  val th = CONV_RULE (POST_CONV c THENC PRE_CONV c) th
  val f = cdr o cdr
  val h = REWRITE_RULE [GSYM STAR_ASSOC,x86_seq_monadTheory.word2bytes_thm,x86_seq_monadTheory.EL_thm] 
  val th = MATCH_MP (h xBYTE_MEMORY_INTRO) (h th)
  val th = RW [wordsTheory.WORD_ADD_0,GSYM progTheory.SPEC_MOVE_COND] th
  fun replace_access_in_pre th = let
    val (_,p,c,q) = dest_spec(concl th)
    val tm = find_term (can (match_term ``(a:'a =+ w:'b) f``)) p
    val (tm,y) = dest_comb tm
    val (tm,x) = dest_comb tm  
    val a = snd (dest_comb tm)
    val th = REWRITE_RULE [APPLY_UPDATE_ID] (INST [x |-> mk_comb(y,a)] th)
    in th end handle e => th
  val th = replace_access_in_pre th
  val th = RW [STAR_ASSOC] th
  in th end handle e => th;

fun calculate_length_and_jump th = let 
  val (_,_,c,q) = dest_spec (concl th)
  val l = (length o fst o listSyntax.dest_list o cdr o cdr o car) c
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
  val th = introduce_xMEMORY th
  val th = introduce_xBYTE_MEMORY th
  val th = SIMP_RULE (std_ss++sw2sw_ss++w2w_ss) [GSYM wordsTheory.WORD_ADD_ASSOC,
    word_arith_lemma1,word_arith_lemma2,word_arith_lemma3,word_arith_lemma4] th
  val th = CONV_RULE FIX_WORD32_ARITH_CONV th
  val th = RW [wordsTheory.WORD_ADD_ASSOC,wordsTheory.WORD_ADD_0] th
  in calculate_length_and_jump th end;

fun calc_code s = let
  fun space n [] zs = [implode zs]
    | space n (x::xs) zs = 
        if n = 0 then (implode zs) :: space 2 (x::xs) [] else space (n-1) xs (zs @ [x])
  fun get_rewrite c = GSYM (EVAL (subst [``c:string``|->fromMLstring c] ``hex2bits c``))
  val strs = space 2 (explode s) []
  val c = listSyntax.mk_list (map fromMLstring strs,``:string``)
  in (c, map get_rewrite strs) end;  

fun x86_prove_one_spec th c = let
  val g = concl th
  val s = find_term (can (match_term ``X86_NEXT x = SOME y``)) g
  val s = (snd o dest_comb o snd o dest_comb) s    

  val (pre,post) = x86_pre_post g s
  val tm = ``SPEC X86_MODEL pre {(eip,c)} post``
  val tm = subst [mk_var("pre",type_of pre) |-> pre, 
                  mk_var("post",type_of post) |-> post, 
                  mk_var("c",type_of c) |-> c] tm
  val FLIP_TAC = CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ])
  val th1 = SIMP_RULE bool_ss [XWRITE_EIP_def,XWRITE_EFLAG_def,XWRITE_REG_def,XWRITE_MEM_def,
    XREAD_REG_def,XREAD_MEM_def,XREAD_EFLAG_def,XREAD_EIP_def] (Q.INST [`s`|->`(xr,xf,xe,xm)`] th)
  val th = prove(tm,
(*
    set_goal([],tm)
*)
    MATCH_MP_TAC IMP_X86_SPEC \\ REPEAT STRIP_TAC \\ EXISTS_TAC ((cdr o cdr o concl o UNDISCH) th1)
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x86_2set, IN_DELETE, APPLY_UPDATE_THM, Xreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Xeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET, SEP_CLAUSES] 
    \\ ONCE_REWRITE_TAC [CODE_POOL_x86_2set]
    \\ REWRITE_TAC [listTheory.LENGTH,address_list_def]
    \\ SIMP_TAC std_ss [arithmeticTheory.ADD1]
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x86_2set, IN_DELETE, APPLY_UPDATE_THM, Xreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Xeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET,x86_pool_def] 
    \\ NTAC 3 (FLIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO])
    \\ FLIP_TAC \\ REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC] 
    \\ SIMP_TAC std_ss [] \\ FLIP_TAC \\ STRIP_TAC \\ STRIP_TAC 
    THEN1 (FLIP_TAC \\ MATCH_MP_TAC (REWRITE_RULE [GSYM ALIGNED_def] th1) \\ 
           FULL_SIMP_TAC std_ss [ALIGNED_def,word_arith_lemma1,CONTAINER_def,markerTheory.Abbrev_def])    
    \\ FULL_SIMP_TAC std_ss [UPDATE_x86_2set'',word_arith_lemma1,ALIGNED_CLAUSES])
  in RW [STAR_ASSOC,SEP_CLAUSES,markerTheory.Abbrev_def] th end;

fun x86_prove_specs s = let
  val th = x86_step s
  val th = pre_process_thm th
  val (c,thms) = calc_code s
  val th = RW thms th
  fun replace_conv th tm = if eq ((fst o dest_eq o concl) th) tm then th else ALL_CONV tm
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

val x86_spec = cache x86_prove_specs;
val x86_tools = (x86_spec, x86_jump, x86_status, x86_pc)

(*

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
  val th = x86_spec "E2FD";            (* loop L *)
  val th = x86_spec "751D";            (* jne L1 *)
  val th = x86_spec "740D";            (* je L2 *)
  val th = x86_spec "0F44C1";          (* cmove eax, ecx *)
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
  val th = x86_spec "8A3E";            (* mov_byte edi,[esi] *)

*)

end
