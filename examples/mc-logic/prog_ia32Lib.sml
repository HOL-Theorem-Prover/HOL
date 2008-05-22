structure prog_ia32Lib :> prog_ia32Lib =
struct
 
open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory ia32Theory ia32Lib prog_ia32Theory helperLib;

infix \\ 
val op \\ = op THEN;


val ia32_status = xS_HIDE;
val ia32_pc = ``xPC``;

fun process tm = let
  fun replace_plus c = if c = #"+" then #"_" else c;
  fun name_of_tm tm = 
    "m_" ^ (implode o filter is_normal_char o map replace_plus o explode o term_to_string) tm;
  val to_lower_drop_two = implode o tl o tl o explode o to_lower
  in if type_of tm = ``:Xreg`` then 
       (mk_comb(``xR1``,tm),mk_var((to_lower o fst o dest_const) tm,``:word32``))
     else if type_of tm = ``:Xeflags`` then 
       (mk_comb(``xS1``,tm),mk_var((to_lower_drop_two o fst o dest_const) tm,``:bool option``))
     else if type_of tm = ``:word32`` then
       (mk_comb(``xM1``,tm),
        mk_comb(``SOME:word8->word8 option``,mk_var(name_of_tm tm,``:word8``)))
     else hd [] end;

val rewrite_reg_names = let
  fun aux v = let val m = match_term ``xr:Xreg->word32 r`` v
              in (snd o process o snd o dest_comb) v end
  in replace_terml aux end;
  
val rewrite_bit_names = let
  fun aux v = let val m = match_term ``fr:Xeflags->bool option r`` v
              in (snd o process o snd o dest_comb) v end
  in replace_terml aux end;
  
val rewrite_reg_and_bit_names = rewrite_bit_names o rewrite_reg_names

fun pre_process_thm th = let
  val th = Q.INST [`r`|->`xr`,`f`|->`xf`,`e`|->`xe`,`m`|->`xm`] th
  val th = SIMP_RULE std_ss [word_arith_lemma1,XREAD_MEM_def] th
  val xs = find_terml (can (match_term ``(THE p):'a``)) (concl th)
  val ys = map (snd o dest_comb) xs
  fun f tm = 
    if type_of tm = ``:bool option`` then 
      let val v = (fst o dest_var o snd o process o snd o dest_comb) tm
          in optionLib.mk_some (mk_var("s"^v,``:bool``)) end
    else (snd o process o snd o dest_comb o rewrite_reg_and_bit_names) tm
  val zs = map f ys  
  val qs = map mk_eq (zip ys zs)
  val th = foldr (uncurry DISCH) th qs
  val th = RW [AND_IMP_INTRO,GSYM CONJ_ASSOC,wordsTheory.WORD_XOR_CLAUSES,
             wordsTheory.WORD_AND_CLAUSES] (SIMP_RULE std_ss [] th)
  in th end;

fun ia32_pre_post g s = let
  val regs = collect_term_of_type ``:Xreg`` g;
  val bits = collect_term_of_type ``:Xeflags`` g;
  val h = rewrite_reg_and_bit_names g
  val mems1 = find_terml (can (match_term ``~(xm:word32->word8 option x = NONE)``)) h
  val mems2 = find_terml (can (match_term ``(xm:word32->word8 option x = SOME y)``)) h
  val select_address1 = snd o dest_comb o fst o dest_eq o snd o dest_comb
  val select_address2 = snd o dest_comb o fst o dest_eq
  val mems3 = map select_address1 mems1 @ map select_address2 mems2
  val mems = filter (fn x => not (``xe:word32`` = (cdr (car x) handle e => x))) mems3
  val assignments = find_terml (can (match_term ``x:'a =+ y:'b``)) h
  val assignments = map ((fn (x,y) => (snd (dest_comb x),y)) o dest_comb) assignments  
  fun get_assigned_value_aux x y [] = y
    | get_assigned_value_aux x y ((q,z)::zs) = 
        if x = q then z else get_assigned_value_aux x y zs
  fun get_assigned_value x y = get_assigned_value_aux x y assignments
  fun mk_pre_post_assertion x = let
    val (y,z) = process x
    val q = get_assigned_value x z
    in (mk_comb(y,z),mk_comb(y,q)) end   
  val pre_post = map mk_pre_post_assertion (regs @ bits @ mems) 
  val pre = list_mk_star (map fst pre_post) ``:ia32_set -> bool``
  val post = list_mk_star (map snd pre_post) ``:ia32_set -> bool``
  fun pass tm = not (can (match_term ``~(xm:word32->word8 option x = NONE)``) tm 
              orelse can (match_term ``xm:word32->word8 option x = SOME y``) tm) 
  val pre_conds = (filter pass o list_dest dest_conj o fst o dest_imp) h
  fun is_bit_cond tm =
    let val (x,y) = dest_eq tm in   
      is_var x andalso type_of x = ``:bool option`` andalso 
      optionLib.is_some y end handle e => false;
  val ss = foldr (fn (x,y) => (fst (dest_eq x) |-> snd (dest_eq x)) :: y) [] 
             (filter is_bit_cond pre_conds) 
  val pre = subst ss pre
  val post = subst ss post
  val pre = mk_star (pre,``xPC eip``)
  val post = mk_star (post,mk_comb(``xPC``,subst [``xe:word32``|->``eip:word32``] ((cdr o car o cdr o cdr) s)))
  val pre_conds = filter (not o is_bit_cond) pre_conds
  val pre = if pre_conds = [] then pre else mk_cond_star(pre,list_mk_conj pre_conds) 
  in (pre,post) end;

fun introduce_xMEMORY th = let
  val (_,p,c,q) = dest_spec(concl th)
  val tm3 = find_term (can (match_term ``xM1 (x + 3w) y``)) p
  val tm = (fst o dest_comb o snd o dest_comb o fst o dest_comb) tm3  
  val vs = FVL [tm] empty_varset
  val tm0 = mk_comb(mk_comb(``xM1``,snd (dest_comb tm)),``yyy : word8 option``)
  val tm0 = find_term (can (match_terml [] vs tm0)) p
  val tm1 = mk_comb(mk_comb(``xM1``,mk_comb(tm,``1w:word32``)),``yyy : word8 option``)
  val tm1 = find_term (can (match_terml [] vs tm1)) p
  val tm2 = mk_comb(mk_comb(``xM1``,mk_comb(tm,``2w:word32``)),``yyy : word8 option``)
  val tm2 = find_term (can (match_terml [] vs tm2)) p
  val c = MOVE_OUT_CONV (fst (dest_comb tm3)) THENC
          MOVE_OUT_CONV (fst (dest_comb tm2)) THENC
          MOVE_OUT_CONV (fst (dest_comb tm1)) THENC
          MOVE_OUT_CONV (fst (dest_comb tm0)) THENC
          STAR_REVERSE_CONV
  val th = CONV_RULE (POST_CONV c THENC PRE_CONV c) th
  val f = snd o dest_comb o snd o dest_comb
  fun g th tm tm' = if is_var tm then INST [ tm |-> tm' ] th else th
  val th = g th (f tm0) ``((7 >< 0) (w:word32)):word8``   
  val th = g th (f tm1) ``((7 >< 0) ((w >> 8):word32)):word8``   
  val th = g th (f tm2) ``((7 >< 0) ((w >> 16):word32)):word8``   
  val th = g th (f tm3) ``((7 >< 0) ((w >> 24):word32)):word8``   
  val h = REWRITE_RULE [GSYM STAR_ASSOC] 
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
  in calculate_length_and_jump th end;

fun calc_code s = let
  fun space n [] zs = [implode zs]
    | space n (x::xs) zs = 
        if n = 0 then (implode zs) :: space 2 (x::xs) [] else space (n-1) xs (zs @ [x])
  fun get_rewrite c = GSYM (EVAL (subst [``c:string``|->fromMLstring c] ``hex2bits c``))
  val strs = space 2 (explode s) []
  val c = listSyntax.mk_list (map fromMLstring strs,``:string``)
  in (c, map get_rewrite strs) end;  

fun ia32_prove_one_spec th c = let
  val g = concl th
  val s = find_term (can (match_term ``X86_NEXT x = SOME y``)) g
  val s = (snd o dest_comb o snd o dest_comb) s    
  val (pre,post) = ia32_pre_post g s
  val tm = ``SPEC IA32_MODEL pre {(eip,c)} post``
  val tm = subst [mk_var("pre",type_of pre) |-> pre, 
                  mk_var("post",type_of post) |-> post, 
                  mk_var("c",type_of c) |-> c] tm
  val FLIP_TAC = CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ])
  val th = prove(tm,
(*
    set_goal([],tm)
*)
    MATCH_MP_TAC IMP_IA32_SPEC \\ REPEAT STRIP_TAC \\ EXISTS_TAC s 
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_ia32_2set, IN_DELETE, APPLY_UPDATE_THM, Xreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Xeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET, SEP_CLAUSES] 
    \\ ONCE_REWRITE_TAC [CODE_POOL_ia32_2set]
    \\ REWRITE_TAC [listTheory.LENGTH,address_list_def]
    \\ SIMP_TAC std_ss [arithmeticTheory.ADD1]
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_ia32_2set, IN_DELETE, APPLY_UPDATE_THM, Xreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Xeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET,ia32_pool_def] 
    \\ NTAC 3 (FLIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO])
    \\ FLIP_TAC \\ REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC] 
    \\ SIMP_TAC std_ss [] \\ FLIP_TAC \\ STRIP_TAC \\ STRIP_TAC 
    THEN1 (FLIP_TAC \\ MATCH_MP_TAC th \\ 
           FULL_SIMP_TAC std_ss [ALIGNED_def,word_arith_lemma1,CONTAINER_def])    
    \\ ASM_SIMP_TAC std_ss [UPDATE_ia32_2set'',ALIGNED_CLAUSES])
  in RW [STAR_ASSOC] th end;

fun ia32_prove_specs s = let
  val th = ia32_step s
  val th = pre_process_thm th
  val (c,thms) = calc_code s
  val th = RW thms th
  fun replace_conv th tm = if (fst o dest_eq o concl) th = tm then th else ALL_CONV tm
  in if can (find_term is_cond) (concl th) then let
       val (x,y,z) = dest_cond (find_term is_cond (concl th))
       fun prove_branch cth th = let
         val tm1 = (fst o dest_imp o concl o ISPECL [x,y,z]) cth
         val th1 = CONV_RULE (DEPTH_CONV (replace_conv (UNDISCH (ISPECL [x,y,z] cth)))) th
         val th1 = (RW [AND_IMP_INTRO,GSYM CONJ_ASSOC] o DISCH_ALL) th1
         val th1 = ia32_prove_one_spec th1 c
         val th1 = SIMP_RULE std_ss [SEP_CLAUSES] (DISCH tm1 th1)
         val th1 = RW [CONTAINER_def] th1
         val th1 = RW [RW [GSYM precond_def] (GSYM progTheory.SPEC_MOVE_COND)] th1
         in post_process_thm th1 end
       in (prove_branch CONTAINER_IF_T th, SOME (prove_branch CONTAINER_IF_F th)) end
     else (post_process_thm (ia32_prove_one_spec th c),NONE) end
       
val ia32_spec = cache ia32_prove_specs;
val ia32_tools = (ia32_spec, ia32_status, ia32_pc)

(*

val res = ia32_spec "813337020000";  (* xor dword [ebx],567 *)
val res = ia32_spec "310B";          (* xor [ebx], ecx *)
val res = ia32_spec "40";            (* inc eax *)
val res = ia32_spec "E2FD";          (* loop L *)
val res = ia32_spec "8B36";          (* mov esi, [esi] *)
val res = ia32_spec "EBF7";          (* jmp L1 *)

*)

end
