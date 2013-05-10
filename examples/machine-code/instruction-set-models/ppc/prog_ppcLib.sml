structure prog_ppcLib :> prog_ppcLib =
struct

open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory ppc_Theory prog_ppcTheory helperLib ppc_Lib;
open ppc_coretypesTheory ppc_seq_monadTheory;

infix \\
val op \\ = op THEN;


val ppc_status = pS_HIDE
val ppc_pc = ``pPC``;

fun process v tm =
  if type_of tm = ``:ppc_reg`` then
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
     (mk_comb(``pM1``,tm),v)
   else fail();

fun pre_process_thm th = let
  val rs = find_terml (can (match_term ``PREAD_R x s``)) (concl th)
  val fs = find_terml (can (match_term ``PREAD_S x s``)) (concl th)
  val regs = map (fn tm => mk_eq(tm,(snd o process T o cdr o car) tm)) rs
  fun f t = optionSyntax.mk_some o (fn x => mk_var(x,t)) o fst o dest_var
  val flags = map (fn tm => mk_eq(tm,(f ``:bool`` o snd o process T o cdr o car) tm)) fs
  val th = foldr (uncurry DISCH) th (regs @ flags)
  val th = SIMP_RULE bool_ss [optionTheory.option_CLAUSES] th
  val ms = find_terml (can (match_term ``~(PREAD_M x s = NONE)``)) (concl th)
  val ms = map (fst o dest_eq o dest_neg) ms
  val mems = map (fn tm => mk_eq(tm,f ``:word8`` (genvar(``:bool``)))) ms
  val th = foldr (uncurry DISCH) th mems
  val th = RW [AND_IMP_INTRO,GSYM CONJ_ASSOC,wordsTheory.WORD_XOR_CLAUSES,
             wordsTheory.WORD_AND_CLAUSES] (SIMP_RULE std_ss [] th)
  in th end;

fun ppc_pre_post g = let
  val regs = collect_term_of_type ``:ppc_reg`` g;
  val bits = collect_term_of_type ``:ppc_bit`` g;
  val mems = find_terml (can (match_term ``(PREAD_M x s = SOME y)``)) g
  val mems = filter (is_var o cdr o cdr) mems
  val mems = map (fn tm => ((cdr o car o fst o dest_eq) tm, cdr tm)) mems
  val assignments = find_terml (can (match_term ``PWRITE_S a x``)) g
                  @ find_terml (can (match_term ``PWRITE_R a x``)) g
                  @ find_terml (can (match_term ``PWRITE_M a x``)) g
  val assignments = map (fn tm => (cdr (car tm), cdr tm)) assignments
  fun assigned_aux x y [] = y
    | assigned_aux x y ((q,z)::zs) = if x = q then z else assigned_aux x y zs
  fun get_assigned_value x y = assigned_aux x y assignments
  fun mk_pre_post_assertion (x,v) = let
    val (y,z) = process v x
    val q = get_assigned_value x z
    in (mk_comb(y,z),mk_comb(y,q)) end
  val pre_post = map mk_pre_post_assertion (map (fn tm => (tm,T)) (regs @ bits) @ mems)
  val pre = list_mk_star (map fst pre_post) ``:ppc_set -> bool``
  val post = list_mk_star (map snd pre_post) ``:ppc_set -> bool``
  fun is_precond tm =
   (not (can (match_term ``PREAD_R r s = v``) tm) andalso
    not (can (match_term ``PREAD_M r s = v``) tm) andalso
    not (can (match_term ``PREAD_S r s = v``) tm)) handle e => true
  val all_conds = (list_dest dest_conj o fst o dest_imp) g
  val pre_conds = (filter is_precond) all_conds
  val pre_conds = (filter (fn tm => not (tm = ``p && 3w = 0w:word32``))) pre_conds
  val ss = foldr (fn (x,y) => (fst (dest_eq x) |-> snd (dest_eq x)) :: y handle e => y) []
             (filter is_precond pre_conds)
  val ss = ss @ map ((fn tm => mk_var((fst o dest_var o cdr) tm,``:bool option``) |-> tm) o cdr)
    (filter (can (match_term ``PREAD_S x s = SOME y``)) all_conds)
  val pre = subst ss pre
  val post = subst ss post
  val pre = if pre_conds = [] then pre else mk_cond_star(pre,mk_comb(``Abbrev``,list_mk_conj pre_conds))
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

fun introduce_pBYTE_MEMORY th = let
  val (_,p,c,q) = dest_spec(concl th)
  val tm0 = find_term (can (match_term ``pM1 x y``)) p
  val c = MOVE_OUT_CONV (car tm0) THENC STAR_REVERSE_CONV
  val th = CONV_RULE (POST_CONV c THENC PRE_CONV c) th
  val f = cdr o cdr
  val h = REWRITE_RULE [GSYM STAR_ASSOC,bit_listTheory.bytes2word_thm]
  val th = MATCH_MP (h pBYTE_MEMORY_INTRO) (h th)
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
             [wordsTheory.word_mul_n2w,wordsTheory.WORD_ADD_0,wordsTheory.WORD_OR_IDEM] th
  val th = CONV_RULE FIX_WORD32_ARITH_CONV th
  val th = introduce_pMEMORY th
  val th = introduce_pBYTE_MEMORY th
  val th = RW [bit_listTheory.bytes2word_thm,extract_byte] th
  in calculate_length_and_jump th end;

fun ppc_prove_one_spec th c = let
  val g = concl th
  val th = Q.INST [`s`|->`(pr,ps,pm)`] th
  val s = find_term (can (match_term ``PPC_NEXT x = SOME y``)) (concl th)
  val s = (snd o dest_comb o snd o dest_comb) s
  val (pre,post) = ppc_pre_post g
  val tm = ``SPEC PPC_MODEL pre {(p,c)} post``
  val tm = subst [mk_var("pre",type_of pre) |-> pre,
                  mk_var("post",type_of post) |-> post,
                  mk_var("c",type_of c) |-> c] tm
  val FLIP_TAC = CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ])
  val th = RW [PREAD_R_def,PREAD_S_def,PREAD_M_def,PWRITE_R_def,PWRITE_S_def,PWRITE_M_def] th
  val result = prove(tm,
    MATCH_MP_TAC IMP_PPC_SPEC \\ REPEAT STRIP_TAC \\ EXISTS_TAC s
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_ppc2set, CODE_POOL_ppc2set, pR_def, pPC_def, IN_DELETE,
         APPLY_UPDATE_THM, ppc_reg_distinct, ppc_reg_11, ALIGNED_INTRO,
         wordsTheory.n2w_11, ppc_bit_11, ppc_bit_distinct, Q.SPECL [`s`,`x
         INSERT aaa`] SET_EQ_SUBSET, INSERT_SUBSET, EMPTY_SUBSET,
         PREAD_R_def,PREAD_S_def,PREAD_M_def,PWRITE_R_def,PWRITE_S_def,PWRITE_M_def]
    \\ NTAC 3 (FLIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO])
    \\ FLIP_TAC \\ REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC]
    \\ SIMP_TAC std_ss [] \\ FLIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    THEN1 (FLIP_TAC \\ MATCH_MP_TAC (RW [ALIGNED_INTRO] th) \\ FULL_SIMP_TAC std_ss
           [ALIGNED_def,wordsTheory.WORD_ADD_0,markerTheory.Abbrev_def] \\ EVAL_TAC)
    \\ ASM_REWRITE_TAC [ALIGNED_INTRO]
    \\ ASM_SIMP_TAC std_ss [UPDATE_ppc2set'',ALIGNED_CLAUSES]
    \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
    \\ ASM_SIMP_TAC std_ss [wordsTheory.WORD_ADD_0])
  in RW [STAR_ASSOC,markerTheory.Abbrev_def] result end;

fun ppc_prove_specs s = let
  val th = ppc_step s
  val th = pre_process_thm th
  val c = mk_comb(``n2w:num->word32``,(numSyntax.mk_numeral o Arbnum.fromHexString) s)
  fun replace_conv th tm = if (fst o dest_eq o concl) th = tm then th else ALL_CONV tm
  in if (is_cond o snd o dest_imp o concl) th then let
       val (x,y,z) = dest_cond (find_term is_cond (concl th))
       fun prove_branch cth th = let
         val tm1 = (fst o dest_imp o concl o ISPECL [x,y,z]) cth
         val th1 = CONV_RULE (DEPTH_CONV (replace_conv (UNDISCH (ISPECL [x,y,z] cth)))) th
         val th1 = (RW [AND_IMP_INTRO,GSYM CONJ_ASSOC] o DISCH_ALL) th1
         val th1 = ppc_prove_one_spec th1 c
         val th1 = SIMP_RULE std_ss [SEP_CLAUSES] (DISCH tm1 th1)
         val th1 = RW [CONTAINER_def] th1
         val th1 = RW [RW [GSYM precond_def] (GSYM progTheory.SPEC_MOVE_COND)] th1
         in post_process_thm th1 end
       in (prove_branch CONTAINER_IF_T th, SOME (prove_branch CONTAINER_IF_F th)) end
     else (post_process_thm (ppc_prove_one_spec th c),NONE) end

fun ppc_jump (tm1:term) (tm2:term) (jump_length:int) (forward:bool) = ("",0)

val ppc_spec = cache ppc_prove_specs;
val ppc_tools = (ppc_spec, ppc_jump, ppc_status, ppc_pc)
val ppc_tools_no_status = (ppc_spec, ppc_jump, TRUTH, ppc_pc);


(*

  val th = ppc_spec "7C119000";  (* cmpw 17,18    *)
  val th = ppc_spec "7C812839";  (* and. 1,4,5    *)
  val th = ppc_spec "7C5A2278";  (* xor 26, 2, 4  *)
  val th = ppc_spec "7C5A1378";  (* mr 26, 2      *)
  val th = ppc_spec "7C5A212E";  (* stwx 2, 26, 4 *)
  val th = ppc_spec "80450004";  (* lwz 2, 4(5)   *)
  val th = ppc_spec "7C221A14";  (* add 1,2,3     *)
  val th = ppc_spec "4BFFFFFC";  (* b L1          *)
  val th = ppc_spec "4181FFF4";  (* bc 12,1,L1    *)
  val th = ppc_spec "4082FFF0";  (* bc 4,2,L1     *)
  val th = ppc_spec "4083FFEC";  (* bc 4,3,L1     *)
  val th = ppc_spec "88830005";  (* lbz 4,5,3     *)
  val th = ppc_spec "98830005";  (* stb 4,5,3     *)
  val th = ppc_spec "7C858396";  (* divwu 4,5,16  *)

  (* pMEMORY is not properly introduced for half-words,
     also fails if more than one memory location is accessed. *)

  val th = ppc_spec "7E7A222E";  (* lhzx 19, 26, 4 *)
  val th = ppc_spec "7E7A22AE";  (* lhax 19, 26, 4 *)

  val s = ppc_encodeLib.ppc_encode "stb 4,5,3"

*)


end
