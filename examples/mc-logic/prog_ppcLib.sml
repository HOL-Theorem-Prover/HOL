structure prog_ppcLib :> prog_ppcLib =
struct
 
open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory ppcTheory prog_ppcTheory helperLib ppcLib;

infix \\ 
val op \\ = op THEN;


val ppc_status = pS_HIDE
val ppc_pc = ``pPC``;

fun process tm = let
  fun replace_plus c = if c = #"+" then #"_" else c;
  fun name_of_tm tm = 
    "m_" ^ (implode o filter is_normal_char o map replace_plus o explode o term_to_string) tm;
  in if type_of tm = ``:ppc_reg`` then 
       if tm = ``PPC_PC``  then (``pPC`` ,``p:word32``) else
       if tm = ``PPC_LR``  then (``pLR`` ,``lr:word32``) else
       if tm = ``PPC_CTR`` then (``pCTR``,``ctr:word32``) else
         let val tm = snd (dest_comb tm)
             val f = int_to_string o numSyntax.int_of_term o snd o dest_comb in
           (mk_comb(``pR``,tm),mk_var("r" ^ f tm,``:word32``)) end
     else if type_of tm = ``:ppc_bit`` then 
       if tm = ``PPC_CARRY``  then (``pS1 PPC_CARRY`` ,``c:bool option``) else
         let val f = int_to_string o numSyntax.int_of_term o snd o dest_comb o snd o dest_comb in
           (mk_comb(``pS1``,tm),mk_var("s" ^ f tm,``:bool option``)) end        
     else if type_of tm = ``:word32`` then
       (mk_comb(``pM1``,tm),
        mk_comb(``SOME:word8->word8 option``,mk_var(name_of_tm tm,``:word8``)))
     else hd [] end;

val rewrite_reg_names = let
  fun aux v = let val m = match_term ``pr:ppc_reg->word32 r`` v
              in (snd o process o snd o dest_comb) v end
  in replace_terml aux end;
  
val rewrite_bit_names = let
  fun aux v = let val m = match_term ``pr:ppc_bit->bool option r`` v
              in (snd o process o snd o dest_comb) v end
  in replace_terml aux end;
  
val rewrite_reg_and_bit_names = rewrite_bit_names o rewrite_reg_names

fun pre_process_thm th = let
  val th = Q.INST [`r`|->`pr`,`s`|->`ps`,`m`|->`pm`] th
  val th = SIMP_RULE std_ss [word_arith_lemma1] th
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
  val th = RW [AND_IMP_INTRO,GSYM CONJ_ASSOC] (SIMP_RULE std_ss [] th)
  in th end;

fun ppc_pre_post g = let
  val regs = collect_term_of_type ``:ppc_reg`` g;
  val bits = collect_term_of_type ``:ppc_bit`` g;
  val h = rewrite_reg_and_bit_names g
  val mems1 = find_terml (can (match_term ``~(pm:word32->word8 option x = NONE)``)) h
  val mems2 = find_terml (can (match_term ``(pm:word32->word8 option x = SOME y)``)) h
  val select_address1 = snd o dest_comb o fst o dest_eq o snd o dest_comb
  val select_address2 = snd o dest_comb o fst o dest_eq
  val mems3 = map select_address1 mems1 @ map select_address2 mems2
  val mems = filter (fn x => not (mem x [``p:word32``,``p+1w:word32``,``p+2w:word32``,``p+3w:word32``])) mems3
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
  val pre = list_mk_star (map fst pre_post) ((type_of o fst o hd) pre_post)
  val post = list_mk_star (map snd pre_post) ((type_of o fst o hd) pre_post)
  fun pass tm = not (can (match_term ``~(pm:word32->word8 option x = NONE)``) tm 
              orelse can (match_term ``pm:word32->word8 option x = SOME y``) tm
              orelse (tm = ``p && 3w = 0w:word32``)) 
  val pre_conds = (filter pass o list_dest dest_conj o fst o dest_imp) h
  fun is_bit_cond tm =
    let val (x,y) = dest_eq tm in   
      is_var x andalso type_of x = ``:bool option`` andalso 
      optionLib.is_some y end handle e => false;
  val ss = foldr (fn (x,y) => (fst (dest_eq x) |-> snd (dest_eq x)) :: y) [] 
             (filter is_bit_cond pre_conds) 
  val pre = subst ss pre
  val post = subst ss post
  val pre_conds = filter (not o is_bit_cond) pre_conds
  val pre = if pre_conds = [] then pre else mk_cond_star(pre,list_mk_conj pre_conds) 
  in (pre,post) end;

fun introduce_pMEMORY th = let
  val (_,p,c,q) = dest_spec(concl th)
  val tm3 = find_term (can (match_term ``pM1 (x + 3w) y``)) p
  val tm = (fst o dest_comb o snd o dest_comb o fst o dest_comb) tm3  
  val vs = FVL [tm] empty_varset
  val tm0 = mk_comb(mk_comb(``pM1``,snd (dest_comb tm)),``yyy : word8 option``)
  val tm0 = find_term (can (match_terml [] vs tm0)) p
  val tm1 = mk_comb(mk_comb(``pM1``,mk_comb(tm,``1w:word32``)),``yyy : word8 option``)
  val tm1 = find_term (can (match_terml [] vs tm1)) p
  val tm2 = mk_comb(mk_comb(``pM1``,mk_comb(tm,``2w:word32``)),``yyy : word8 option``)
  val tm2 = find_term (can (match_terml [] vs tm2)) p
  val c = MOVE_OUT_CONV (fst (dest_comb tm3)) THENC
          MOVE_OUT_CONV (fst (dest_comb tm2)) THENC
          MOVE_OUT_CONV (fst (dest_comb tm1)) THENC
          MOVE_OUT_CONV (fst (dest_comb tm0)) THENC
          STAR_REVERSE_CONV
  val th = CONV_RULE (POST_CONV c THENC PRE_CONV c) th
  val f = snd o dest_comb o snd o dest_comb
  fun g th tm tm' = if is_var tm then INST [ tm |-> tm' ] th else th
  val th = g th (f tm0) ``((7 >< 0) ((w >> 24):word32)):word8``   
  val th = g th (f tm1) ``((7 >< 0) ((w >> 16):word32)):word8``   
  val th = g th (f tm2) ``((7 >< 0) ((w >> 8):word32)):word8``   
  val th = g th (f tm3) ``((7 >< 0) (w:word32)):word8``   
  val h = REWRITE_RULE [GSYM STAR_ASSOC] 
  val th = MATCH_MP (h pMEMORY_INTRO) (h th)
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

fun calculate_length_and_jump th = 
  let val (_,_,_,q) = dest_spec(concl th) in
    let val v = find_term (fn t => t = ``pPC (p + 4w)``) q in (th,4,SOME 4) end
  handle e =>
    let val v = find_term (can (match_term ``pPC (p + n2w n)``)) q
    in (th,4,SOME (0 + (numSyntax.int_of_term o cdr o cdr o cdr) v)) end 
  handle e =>
    let val v = find_term (can (match_term ``pPC (p - n2w n)``)) q
    in (th,4,SOME (0 - (numSyntax.int_of_term o cdr o cdr o cdr) v)) end
  handle e => 
    (th,4,NONE) end 

fun post_process_thm th = let
  val th = SIMP_RULE (std_ss++sw2sw_ss++w2w_ss) 
             [wordsTheory.word_mul_n2w,wordsTheory.WORD_ADD_0] th
  val th = CONV_RULE FIX_WORD32_ARITH_CONV th
  val th = introduce_pMEMORY th
  in calculate_length_and_jump th end;

fun ppc_prove_one_spec th = let
  val g = concl th
  val c = find_term (fn tm => type_of tm = ``:string``) g
  val s = find_term (can (match_term ``PPC_NEXT x = SOME y``)) g
  val s = (snd o dest_comb o snd o dest_comb) s    
  val (pre,post) = ppc_pre_post g
  val tm = ``SPEC PPC_MODEL pre {(p,c)} post``
  val tm = subst [mk_var("pre",type_of pre) |-> pre, 
                  mk_var("post",type_of post) |-> post, 
                  mk_var("c",type_of c) |-> c] tm
  val FLIP_TAC = CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ])
  val result = prove(tm,
    MATCH_MP_TAC IMP_PPC_SPEC \\ REPEAT STRIP_TAC \\ EXISTS_TAC s 
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_ppc2set, CODE_POOL_ppc2set, pR_def, pPC_def, IN_DELETE,
         APPLY_UPDATE_THM, ppc_reg_distinct, ppc_reg_11, GSYM ALIGNED_def,
         wordsTheory.n2w_11, ppc_bit_11, ppc_bit_distinct, Q.SPECL [`s`,`x
         INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET, EMPTY_SUBSET]
    \\ NTAC 3 (FLIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO])
    \\ FLIP_TAC \\ REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC] 
    \\ SIMP_TAC std_ss [] \\ FLIP_TAC \\ STRIP_TAC \\ STRIP_TAC 
    THEN1 (FLIP_TAC \\ MATCH_MP_TAC th \\ FULL_SIMP_TAC std_ss [ALIGNED_def])    
    \\ ASM_SIMP_TAC std_ss [UPDATE_ppc2set'',ALIGNED_CLAUSES])
  in RW [STAR_ASSOC] result end;

fun ppc_prove_specs s = let
  val th = ppc_step s
  val th = pre_process_thm th
  fun replace_conv th tm = if (fst o dest_eq o concl) th = tm then th else ALL_CONV tm
  in if can (find_term is_cond) (concl th) then let
       val (x,y,z) = dest_cond (find_term is_cond (concl th))
       fun prove_branch cth th = let
         val tm1 = (fst o dest_imp o concl o ISPECL [x,y,z]) cth
         val th1 = CONV_RULE (DEPTH_CONV (replace_conv (UNDISCH (ISPECL [x,y,z] cth)))) th
         val th1 = (RW [AND_IMP_INTRO,GSYM CONJ_ASSOC] o DISCH_ALL) th1
         val th1 = ppc_prove_one_spec th1
         val th1 = SIMP_RULE std_ss [SEP_CLAUSES] (DISCH tm1 th1)
         val th1 = RW [CONTAINER_def] th1
         val th1 = RW [RW [GSYM precond_def] (GSYM progTheory.SPEC_MOVE_COND)] th1
         in post_process_thm th1 end
       in (prove_branch CONTAINER_IF_T th, SOME (prove_branch CONTAINER_IF_F th)) end
     else (post_process_thm (ppc_prove_one_spec th),NONE) end
       
val ppc_spec = cache ppc_prove_specs;
val ppc_tools  = (ppc_spec, ppc_status, ppc_pc)



(*

  val th = ppc_spec "7C119000";  (* cmpw 17,18 *)
  val th = ppc_spec "7C812839";  (* and. 1,4,5 *)
  val th = ppc_spec "7C5A2278";  (* xor 26, 2, 4 *)
  val th = ppc_spec "7C5A1378";  (* mr 26, 2 *)
  val th = ppc_spec "7C5A212E";  (* stwx 2, 26, 4 *)
  val th = ppc_spec "80450004";  (* lwz 2, 4(5) *)
  val th = ppc_spec "7C221A14";  (* add 1,2,3   *)
  val th = ppc_spec "4BFFFFFC";  (* b L1        *)
  val th = ppc_spec "4181FFF4";  (* bc 12,1,L1 *)
  val th = ppc_spec "4082FFF0";  (* bc 4,2,L1 *)
  val th = ppc_spec "4083FFEC";  (* bc 4,3,L1 *)

  val s = "7C4219D6";

  val th = ppc_spec "7C4219D6";  
  val th = ppc_spec "7C611810";  
  val th = ppc_spec "28030000";  
  val th = ppc_spec "4082FFF4";  

  (* pMEMORY is not properly introduced for half-words or bytes,
     also fails if more than one memory location is accessed. *)

  val th = ppc_spec "7E7A222E";  (* lhzx 19, 26, 4 *)
  val th = ppc_spec "7E7A22AE";  (* lhax 19, 26, 4 *)

*)


end
