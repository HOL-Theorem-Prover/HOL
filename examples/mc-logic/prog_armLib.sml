structure prog_armLib :> prog_armLib =
struct
 
open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory arm_auxTheory prog_armTheory helperLib;
open armLib;

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
  val mems2 = find_terml (can (match_term ``ARM_WRITE_MEM a x ^state``)) h
  val mems = map (cdr o car) mems1 @ map (cdr o car o car) mems2
  val mems = filter (fn tm => not (fst (dest_var (cdr tm)) = "r15") handle e => true) mems
  val h2 = rewrite_names (car (car ``ARM_READ_MEM a ^state``)) h
  val reg_assign = find_terml_all (can (match_term ``ARM_WRITE_REG r x ^state``)) h2
  val mem_assign = find_terml_all (can (match_term ``ARM_WRITE_MEM a x ^state``)) h2
  val sts_assign = find_terml_all (can (match_term ``ARM_WRITE_STATUS x ^state``)) h2
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) reg_assign  
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) mem_assign @ assignments 
  val assignments = assignments @ (if 0 = length sts_assign then [] else
    (zip [``sN``,``sZ``,``sC``,``sV``] ((list_dest pairSyntax.dest_pair o cdr o car o hd) sts_assign)))
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
  val pre = if pre_conds = [] then pre else mk_cond_star(pre,list_mk_conj pre_conds) 
  val ss = subst [``aR 15w``|->``aPC``,mk_var("r15",``:word32``)|->``p:word32``]
  in (ss pre,ss post) end;

fun introduce_aMEMORY th = let
  val (_,p,c,q) = dest_spec(concl th)
  val tm3 = find_term (can (match_term ``aM x y``)) p
  val c = MOVE_OUT_CONV (car tm3) THENC STAR_REVERSE_CONV
  val th = CONV_RULE (POST_CONV c THENC PRE_CONV c) th
  val h = REWRITE_RULE [GSYM STAR_ASSOC,GSYM systemTheory.addr30_def,ADDR30_def] 
  val th = MATCH_MP (h aMEMORY_INTRO) (h th)
  val th = SIMP_RULE bool_ss [GSYM ALIGNED_def,SEP_CLAUSES] th
  val th = REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND,ALIGNED_def,STAR_ASSOC] th
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
  val th = introduce_aMEMORY th
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
           \\ FULL_SIMP_TAC std_ss [ALIGNED_def,ARM_READ_UNDEF_def])    
    \\ ASM_SIMP_TAC std_ss [UPDATE_arm2set'',ALIGNED_CLAUSES])
  in RW [STAR_ASSOC] result end;

val cond_CONTAINER = prove(
  ``!x. (cond x):'a set -> bool = cond (CONTAINER x)``,
  REWRITE_TAC [CONTAINER_def]);

fun arm_prove_specs s = let
  val thms = arm_step s
  val _ = print ", deriving"
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
  in if length result < 2 then (hd result, NONE) else let
    val (th1,i1,j1) = hd result
    val (th2,i2,j2) = hd (tl result)
    val (x,y) = dest_comb (find_term (can (match_term ``(cond p):'a set set``)) (concl th2))
    val th1 = ONCE_REWRITE_RULE [cond_CONTAINER] th1
    val th1 = DISCH (mk_comb(``CONTAINER``,mk_neg y)) th1
    val th1 = SIMP_RULE bool_ss [SEP_CLAUSES] th1
    val rw = REWRITE_RULE [GSYM precond_def] (GSYM progTheory.SPEC_MOVE_COND)
    val th1 = REWRITE_RULE [CONTAINER_def] (REWRITE_RULE [rw] th1)
    in ((th1,i1,j1), SOME (REWRITE_RULE [GSYM precond_def] th2,i2,j2)) end end
       
val arm_spec = cache arm_prove_specs;
val arm_tools  = (arm_spec, arm_status, arm_pc)

(*

  val th = hd thms

  val thms = arm_spec "E351000A"; (* cmp r1,#10 *)
  val thms = arm_spec "060012E3"; (* tst r2,#6 *)
  val thms = arm_spec "2241100A"; (* subcs r1,r1,#10 *)

  val thms = arm_spec "E3A00000";  (*    mov r0,#0       *)
  val thms = arm_spec "E3510000";  (* L: cmp r1,#0       *)
  val thms = arm_spec "12800001";  (*    addne r0,r0,#1  *)
  val thms = arm_spec "15911000";  (*    ldrne r1,[r1]   *)
  val thms = arm_spec "1AFFFFFB";  (*    bne L           *)

*)

end
