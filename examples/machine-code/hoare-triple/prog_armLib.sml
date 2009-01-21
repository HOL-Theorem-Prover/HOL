structure prog_armLib :> prog_armLib =
struct
 
open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory arm_auxTheory prog_armTheory helperLib wordsTheory;
open arm_Lib;

infix \\ 
val op \\ = op THEN;


val arm_status = aS_HIDE;
val arm_pc = ``aPC``;

fun process tm = let
  fun replace_plus c = if c = #"+" then #"_" else c;
  fun name_of_tm tm = 
    "m_" ^ (implode o filter is_normal_char o map replace_plus o explode o term_to_string) tm;
  in if type_of tm = ``:word4`` then let
       val f = int_to_string o numSyntax.int_of_term o snd o dest_comb
       in (mk_comb(``aR``,tm),mk_var("r" ^ f tm,``:word32``)) end
     else if tm = ``sN:arm_bit`` then (mk_comb(``aS1``,tm),mk_var("sn",``:bool``))
     else if tm = ``sZ:arm_bit`` then (mk_comb(``aS1``,tm),mk_var("sz",``:bool``))
     else if tm = ``sC:arm_bit`` then (mk_comb(``aS1``,tm),mk_var("sc",``:bool``))
     else if tm = ``sV:arm_bit`` then (mk_comb(``aS1``,tm),mk_var("sv",``:bool``))
     else if type_of tm = ``:word30`` then
       (mk_comb(``aM``,tm),mk_var(name_of_tm tm,``:word32``))
     else hd [] end;

val state = ``s:unit arm_sys_state``

fun rewrite_names tm = let
  fun aux v = let val m = match_term tm (car (car v)) in (snd o process o cdr o car) v end
  in replace_terml aux end;

fun arm_pre_post g = let
  val regs = collect_term_of_type ``:word4`` g
  val bits = if can (find_term (can (match_term ``ARM_WRITE_STATUS x ^state``))) g
             then [``sN``,``sZ``,``sC``,``sV``] else collect_term_of_type ``:arm_bit`` g
  val h =  rewrite_names (car (car ``ARM_READ_STATUS a ^state``))
          (rewrite_names (car (car ``ARM_READ_REG a ^state``)) g)
  val mems1 = find_terml (can (match_term ``ARM_READ_MEM a ^state``)) h
  val mems2 = find_terms (can (match_term ``ARM_WRITE_MEM a x ^state``)) h
  val mems = map (cdr o car) mems1 @ map (cdr o car o car) mems2
  val mems = filter (fn tm => not (fst (dest_var (cdr tm)) = "r15") handle e => true) mems
  val h2 = rewrite_names (car (car ``ARM_READ_MEM a ^state``)) h
  val reg_assign = find_terml_all (can (match_term ``ARM_WRITE_REG r x ^state``)) h2
  val mem_assign = find_terml_all (can (match_term ``ARM_WRITE_MEM a x ^state``)) h2
  val sts_assign = find_terml_all (can (match_term ``ARM_WRITE_STATUS x ^state``)) h2
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) reg_assign  
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) mem_assign @ assignments 
  val assignments = assignments @ (if 0 = length sts_assign then [] else
    (Lib.zip [``sN``,``sZ``,``sC``,``sV``] ((list_dest pairSyntax.dest_pair o cdr o car o hd) sts_assign)))
  fun all_distinct [] = []
    | all_distinct (x::xs) = x :: filter (fn y => not (x = y)) (all_distinct xs)
  val mems = all_distinct mems
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
  fun pass tm = 
    not (can (match_term ``~(^state).undefined``) tm) andalso
    not (can (match_term ``ARM_READ_MEM (addr30 (r:word32)) ^state = n2w n``) tm)
  val pre_conds = (filter pass o list_dest dest_conj o fst o dest_imp) h
  val pc_post = snd (hd (filter (fn x => (fst x = ``15w:word4``)) assignments))
  val pc = mk_var("r15",``:word32``)
  val pre_conds = if mem pc (free_vars pc_post) then pre_conds else mk_comb(``ALIGNED``,pc_post) :: pre_conds
  val pre = if pre_conds = [] then pre else mk_cond_star(pre,mk_comb(``CONTAINER``,list_mk_conj pre_conds)) 
  val ss = subst [``aR 15w``|->``aPC``,pc|->``p:word32``]
  in (ss pre,ss post) end;

fun introduce_aBYTE_MEMORY th = let
  val th = REWRITE_RULE [systemTheory.addr30_def,GSYM ADDR30_def] th
  val (_,p,c,q) = dest_spec(concl th)
  val tm3 = find_term (can (match_term ``FORMAT UnsignedByte``)) q handle e =>
            find_term (can (match_term ``SET_BYTE``)) q
  val tm3 = find_term (can (match_term ``aM x y``)) p
  val c = MOVE_OUT_CONV (car tm3)
  val th = CONV_RULE (POST_CONV c THENC PRE_CONV c) th
  val i = INST [``a:word32`` |-> (cdr o cdr o car) tm3] aBYTE_MEMORY_INTRO
  val i2 = INST [``a:word32`` |-> (cdr o cdr o car) tm3] aBYTE_MEMORY_INTRO2
  val tm = find_term (can (match_term ``FORMAT x y w``)) (concl i)
  val th = INST [cdr tm3 |-> cdr tm ] th
  val th = CONV_RULE ((RAND_CONV o RATOR_CONV o RAND_CONV) (UNBETA_CONV tm)) th
  val th = CONV_RULE (DEPTH_CONV BETA_CONV) (MATCH_MP i th handle e => MATCH_MP i2 th)
  val th = REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND,ALIGNED_def,STAR_ASSOC,EXTRACT_BYTE] th
  in th end handle e => th;

fun remove_primes th = let
  fun last s = substring(s,size s-1,1)
  fun delete_last_prime s = if last s = "'" then substring(s,0,size(s)-1) else hd []
  fun foo [] ys i = i
    | foo (x::xs) ys i = let 
      val name = (fst o dest_var) x 
      val new_name = repeat delete_last_prime name
      in if name = new_name then foo xs (x::ys) i else let 
        val new_var = mk_var(new_name,type_of x)
        in foo xs (new_var::ys) ((x |-> new_var) :: i) end end
  val i = foo (free_varsl (concl th :: hyp th)) [] []
  in INST i th end

val SING_SUBSET = prove(
  ``!x:'a y. {x} SUBSET y = x IN y``,
  REWRITE_TAC [INSERT_SUBSET,EMPTY_SUBSET]);

fun introduce_aMEMORY th = if
  not (can (find_term (can (match_term ``aM``))) (concl th)) 
  then th else let
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val (_,p,_,q) = dest_spec(concl th)
  val xs = (rev o list_dest dest_star) p
  val tm = (fst o dest_eq o concl o SPEC_ALL) aM_def
  val xs = filter (can (match_term tm)) xs
  fun foo tm = cdr tm |-> mk_comb(mk_var("f",``:word32->word32``),(cdr o cdr o car) tm) 
  val th = INST (map foo xs) th
  in if xs = [] then th else let
    val (_,p,_,q) = dest_spec(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = (fst o dest_eq o concl o SPEC_ALL) aM_def
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o cdr o car) xs)
    fun foo [] = mk_var("df",``:word32 set``) 
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``aMEMORY``,foo ys),mk_var("f",``:word32->word32``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
    val th = RW [GSYM STAR_ASSOC] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) aMEMORY_INSERT  
    val th = RW [GSYM ADDR30_def,systemTheory.addr30_def] th
    fun compact th = let
      val x = find_term (can (match_term fff)) ((car o car o concl o UNDISCH_ALL) th)
      val rw = (INST (fst (match_term fff x)) o SPEC_ALL) aMEMORY_INSERT
      val th = DISCH ((fst o dest_imp o concl) rw) th
      val th = SIMP_RULE bool_ss [aMEMORY_INSERT] th
      in th end
    val th = repeat compact th
    val th = RW [STAR_ASSOC,AND_IMP_INTRO,GSYM CONJ_ASSOC] th 
    val th = RW [APPLY_UPDATE_ID] th 
    val te = (cdr o car o find_term (can (match_term (cdr fff))) o concl) th
    val t1 = repeat (snd o pred_setSyntax.dest_insert) te
    val t2 = repeat (fst o pred_setSyntax.dest_delete) t1
    val th = SIMP_RULE bool_ss [] (DISCH (mk_eq(te,t2)) th)
    val th = RW [AND_IMP_INTRO] th
    val v = hd (filter (is_var) ys @ ys)
    fun ss [] = ``{}:word32 set``
      | ss (v::vs) = pred_setSyntax.mk_insert(v,ss vs)
    val u1 = pred_setSyntax.mk_subset(ss (rev ys),mk_var("df",``:word32 set``))    
    val u2 = mk_conj(mk_comb(``ALIGNED``,v),u1)
    val u3 = (fst o dest_imp o concl) th
    val goal = mk_imp(u2,u3)
    val imp = prove(goal,
      ONCE_REWRITE_TAC [ALIGNED_MOD_4]
      THEN SIMP_TAC std_ss [WORD_ADD_0,WORD_SUB_RZERO]
      THEN SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL,word_sub_def]
      THEN SIMP_TAC (std_ss++SIZES_ss) [n2w_11,word_2comp_n2w]
      THEN SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_DELETE,INSERT_SUBSET]
      THEN SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL,word_sub_def]
      THEN SIMP_TAC (std_ss++SIZES_ss) [n2w_11,word_2comp_n2w]
      THEN REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
      THEN ASM_SIMP_TAC std_ss []
      THEN CCONTR_TAC
      THEN FULL_SIMP_TAC std_ss []
      THEN FULL_SIMP_TAC std_ss [])
    val th = DISCH_ALL (MATCH_MP th (UNDISCH imp))
    val th = RW [GSYM progTheory.SPEC_MOVE_COND] th
    val th = remove_primes th
    val th = REWRITE_RULE [SING_SUBSET] th
    val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th 
    in th end end

fun calculate_length_and_jump th = 
  let val (_,_,_,q) = dest_spec(concl th) in
  let val v = find_term (fn t => t = ``aPC (p + 4w)``) q in (th,4,SOME 4) end
  handle e =>
  let val v = find_term (can (match_term ``aPC (p + n2w n)``)) q
  in (th,4,SOME (0 + (numSyntax.int_of_term o cdr o cdr o cdr) v)) end 
  handle e =>
  let val v = find_term (can (match_term ``aPC (p - n2w n)``)) q
  in (th,4,SOME (0 - (numSyntax.int_of_term o cdr o cdr o cdr) v)) end
  handle e => (th,4,NONE) end 

fun post_process_thm th = let
  val th = SIMP_RULE (std_ss++sw2sw_ss++w2w_ss) [wordsTheory.word_mul_n2w] th
  val th = CONV_RULE FIX_WORD32_ARITH_CONV th
  val th = introduce_aBYTE_MEMORY th
  val th = introduce_aMEMORY th
  val th = RW [WORD_EQ_XOR_ZERO,wordsTheory.WORD_EQ_SUB_ZERO,ALIGNED_def] th
  in calculate_length_and_jump th end;

fun arm_prove_one_spec th = let
  val g = concl th
  val c = cdr (find_term (can (match_term ``(ARM_READ_MEM ((addr30 (ARM_READ_REG (15w:word4) s)):word30) (s:unit arm_sys_state) = (n2w n):word32)``)) g)
  val s = cdr (find_term (can (match_term ``NEXT_ARM_MMU (cp :unit coproc) s = s'``)) g)
  val (pre,post) = arm_pre_post g
  val tm = ``SPEC ARM_MODEL pre {(p,c)} post``
  val tm = subst [mk_var("pre",type_of pre) |-> pre, 
                  mk_var("post",type_of post) |-> post, 
                  mk_var("c",type_of c) |-> c] tm
  val FLIP_TAC = CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ])
(*
  set_goal([],tm)
*)
  val result = prove(tm,
    MATCH_MP_TAC IMP_ARM_SPEC \\ REPEAT STRIP_TAC \\ EXISTS_TAC s 
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_arm2set, CODE_POOL_arm2set, aPC_def, IN_DELETE,
         APPLY_UPDATE_THM, GSYM ALIGNED_def, wordsTheory.n2w_11,
         arm_bit_distinct, Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET,
         INSERT_SUBSET, EMPTY_SUBSET,ARM_READ_WRITE, GSYM
         systemTheory.addr30_def,ADDR30_def]
    \\ NTAC 3 (FLIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO])
    \\ FLIP_TAC \\ REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC] 
    \\ SIMP_TAC std_ss [] \\ FLIP_TAC \\ STRIP_TAC \\ STRIP_TAC 
    THEN1 (FLIP_TAC \\ MATCH_MP_TAC th 
           \\ FULL_SIMP_TAC std_ss [ALIGNED_def,ARM_READ_UNDEF_def,markerTheory.Abbrev_def,CONTAINER_def])    
    \\ ASM_SIMP_TAC std_ss [UPDATE_arm2set'',ALIGNED_CLAUSES]
    \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
    \\ ASM_SIMP_TAC std_ss [wordsTheory.WORD_ADD_0]
    \\ FULL_SIMP_TAC bool_ss [markerTheory.Abbrev_def,CONTAINER_def])
  in RW [STAR_ASSOC,CONTAINER_def] result end;

val cond_STAR_cond = prove(
  ``!x y. cond (x /\ y) = cond x * (cond y):'a set -> bool``,
  SIMP_TAC (std_ss) [SEP_CLAUSES]);

val precond_INTRO = prove(
  ``!x. cond (Abbrev x) = precond x:'a set -> bool``,
  SIMP_TAC (std_ss) [SEP_CLAUSES,precond_def,markerTheory.Abbrev_def]);

fun arm_prove_specs s = let
  val thms = arm_step s
(*
  val th = hd thms
*)
  fun derive_spec th = let
    val th = INST_TYPE [``:'a``|->``:unit``] th
    val th = Q.INST [`state`|->`s`,`cp`|->`NO_CP`] th
    val xs = find_terml (can (match_term ``FORMAT UnsignedWord ((1 >< 0) (a:'a word)) x``)) (concl th)
    val ys = map ((fn x => mk_comb(``ALIGNED``,x)) o cdr o cdr o car) xs
    val th = foldr (uncurry DISCH) th ys
    val th = SIMP_RULE bool_ss [FORMAT_ALIGNED,AND_IMP_INTRO,GSYM systemTheory.addr30_def] th
    val th = arm_prove_one_spec th
    in post_process_thm th end
  val result = map derive_spec thms
  in if length result < 2 then let
    val (th1,i1,j1) = hd result
    val th1 = REWRITE_RULE [markerTheory.Abbrev_def,SEP_CLAUSES] th1
    in ((th1,i1,j1), NONE) end 
  else let
    val (th1,i1,j1) = hd result
    val (th2,i2,j2) = hd (tl result)
    val th2 = PURE_REWRITE_RULE [GSYM precond_def,markerTheory.Abbrev_def] th2
    val th1 = RW [cond_STAR_cond] th1
    val th1 = RW [precond_INTRO] th1
    val th1 = SIMP_RULE (std_ss++sep_cond_ss) [] th1
    in ((th1,i1,j1), SOME (th2,i2,j2)) end end

fun arm_jump tm1 tm2 jump_length forward = let
  fun arm_mk_jump cond jump_length = let
    val s = "b" ^ cond ^ " " ^ (int_to_string jump_length)
    val th1 = EVAL(mk_comb(``enc``,instructionSyntax.mk_instruction s))
    val s = (Arbnum.toHexString o numSyntax.dest_numeral o cdr o snd o dest_eq o concl) th1
    fun prefix_zero s = if length (explode s) < 8 then prefix_zero ("0"^s) else s
    in prefix_zero s end;
  val (x,y) = if tm2 = ``aS1 sN`` then ("mi","pl") else
              if tm2 = ``aS1 sZ`` then ("eq","ne") else
              if tm2 = ``aS1 sC`` then ("cs","cc") else
              if tm2 = ``aS1 sV`` then ("vs","vc") else ("","")
  val z = if is_neg tm1 then y else x
  val jump_length = if forward then jump_length + 4 else 0 - jump_length
  in (arm_mk_jump z jump_length,4) end
       
val arm_spec = cache arm_prove_specs;
val arm_tools  = (arm_spec, arm_jump, arm_status, arm_pc)

(*

fun enc s = 
  (Arbnum.toHexString o numSyntax.dest_numeral o cdr o snd o dest_eq o concl o EVAL)
  (mk_comb(``enc``,instructionSyntax.mk_instruction s))

fun from_hex s = instructionSyntax.dest_instruction NONE 
              (instructionSyntax.decode_instruction_hex s);

  val thms = arm_spec (enc "CMP r1, #10");
  val thms = arm_spec (enc "TST r2, #6");
  val thms = arm_spec (enc "SUBCS r1, r1, #10");
  val thms = arm_spec (enc "MOV r0, #0");
  val thms = arm_spec (enc "CMP r1, #0");
  val thms = arm_spec (enc "ADDNE r0, r0, #1");
  val thms = arm_spec (enc "LDRNE r1, [r1]");
  val thms = arm_spec (enc "BNE -12; relative");
  val thms = arm_spec (enc "MOVGT r2, #5");
  val thms = arm_spec (enc "LDRB r2, [r3]");
  val thms = arm_spec (enc "STRB r2, [r3]");
  val thms = arm_spec (enc "SWPB r2, r4, [r3]");
  val thms = arm_spec (enc "LDRB r2, [r3]");
  val thms = arm_spec (enc "LDRNEB r2, [r3]");
  val thms = arm_spec (enc "LDR r1, [pc, #1020]");
  val thms = arm_spec (enc "LDRLS pc, [r8], #-4");
  val thms = arm_spec (enc "BLS 420; relative");
  val thms = arm_spec (enc "LDRLS r2, [r11, #-40]");
  val thms = arm_spec (enc "SUBLS r2, r2, #1");
  val thms = arm_spec (enc "SUBLS r11, r11, #4");
  val thms = arm_spec (enc "MOVGT r12, r0");
  val thms = arm_spec (enc "STRB r2, [r3]");
  val thms = arm_spec (enc "STMIA r4, {r5-r10}");
  val thms = arm_spec (enc "LDMIA r4, {r5-r10}");
  val thms = arm_spec (enc "STMDB sp!, {r0-r2, r15}");
  val thms = arm_spec (enc "LDMIA sp!, {r0-r2, r15}");
  val thms = arm_spec (enc "ADD r0, pc, #16");
  val thms = arm_spec (enc "SUB r0, pc, #60");
  val thms = arm_spec (enc "LDR r0, [pc, #4056]");
  val thms = arm_spec (enc "LDR r8, [pc, #3988]");
  val thms = arm_spec (enc "LDR r2, [pc, #3984]");
  val thms = arm_spec (enc "LDR r12, [pc, #3880]");
  val thms = arm_spec (enc "LDR r12, [pc, #3856]");
  val thms = arm_spec (enc "LDRLS r2, [r11, #-40]");
  val thms = arm_spec (enc "LDRLS pc, [r8], #-4");
  val thms = arm_spec (enc "SUBLS r2, r2, #1");
  val thms = arm_spec (enc "SUBLS r11, r11, #4");
  val thms = arm_spec (enc "BLS 4020; relative");
  val thms = arm_spec (enc "BLS 8084; relative");
  val thms = arm_spec (enc "BLE 420; relative");
  val thms = arm_spec (enc "BLE 40; relative");
  val thms = arm_spec (enc "BGT -96; relative");
  val thms = arm_spec (enc "BHI 72; relative");
  val thms = arm_spec (enc "BHI 680; relative");
  val thms = arm_spec (enc "BHI 616; relative");
  val thms = arm_spec (enc "LDRGT r0, [r11, #-44]");
  val thms = arm_spec (enc "MOVGT r1, r3");
  val thms = arm_spec (enc "MOVGT r12, r5");
  val thms = arm_spec (enc "MOVGT r1, r6");
  val thms = arm_spec (enc "MOVGT r0, r6");
  val thms = arm_spec (enc "ADD r5, pc, #4096");
  val thms = arm_spec (enc "ADD r6, pc, #4096");
  val thms = arm_spec (enc "STRB r2, [r1], #1");
  val thms = arm_spec (enc "STRB r3, [r1], #1");
  val thms = arm_spec (enc "STMIB r8!, {r14}");
  val thms = arm_spec (enc "STMIB r8!, {r0, r14}");
  val thms = arm_spec (enc "LDR r0, [pc, #308]");

  (* handle later *)
  val s = "MSR CPSR_c, #219" 
  val s = "MRS r6, CPSR" 

*)

end
