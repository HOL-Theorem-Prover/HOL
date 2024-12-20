structure prog_x64Lib :> prog_x64Lib =
struct

open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory x64_Theory x64_Lib helperLib;
open x64_seq_monadTheory x64_coretypesTheory x64_astTheory x64_icacheTheory;
open prog_x64Theory wordsTheory x64_encodeLib;

structure Parse = struct
  open Parse
  val (Type,Term) =
      prog_x64Theory.prog_x64_grammars
        |> apsnd ParseExtras.grammar_loose_equality
        |> parse_from_grammars
end
open Parse


val x64_status = zS_HIDE;
val x64_pc = ``zPC``;
val x64_exec_flag = ref true;
val x64_code_write_perm = ref false;
val x64_use_stack = ref false;
fun set_x64_exec_flag b = (x64_exec_flag := b);
fun set_x64_code_write_perm_flag b = (x64_code_write_perm := b);
fun set_x64_use_stack b = (x64_use_stack := b);
val Zreg_distinct = x64_decoderTheory.Zreg_distinct;

datatype mpred_type = zMEM_AUTO | zMEM_BYTE_MEMORY | zMEM_MEMORY64;

fun name_for_resource counter tm = let
  val to_lower_drop_two = implode o tl o tl o explode o to_lower
  in if type_of tm = ``:Zreg`` then let
       val name = fst (dest_const tm)
       val reg_name = snd (hd (filter (fn (x,y) => x = name)
           [("RAX","r0"), ("RCX","r1"), ("RDX","r2"), ("RBX","r3"),
            ("RSP","r4"), ("RBP","r5"), ("RSI","r6"), ("RDI","r7"),
            ("zR8","r8"), ("zR9","r9"), ("zR10","r10"), ("zR11","r11"),
            ("zR12","r12"), ("zR13","r13"), ("zR14","r14"),
            ("zR15","r15")]))
       in reg_name end
     else if type_of tm = ``:Zeflags``
          then "z_" ^ (to_lower_drop_two o fst o dest_const) tm else
     (counter := 1 + !counter; ("x" ^ int_to_string (!counter))) end;

val word2bytes_lemma = CONJ (EVAL ``word2bytes 2 (w:'a word)``)
                            (EVAL ``word2bytes 4 (w:'a word)``)

val w2n_MOD = prove(
  ``!imm32. w2n (imm32:word32) MOD 4294967296 = w2n imm32``,
  Cases THEN FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]);

fun pre_process_thm th = let
  val th = RW [ZREAD_MEM2_WORD64_THM,ZWRITE_MEM2_WORD64_THM,wordsTheory.WORD_ADD_0,
               ZREAD_MEM2_WORD16_def,ZWRITE_MEM2_WORD16_def,bit_listTheory.bytes2word_def,
               wordsTheory.ZERO_SHIFT,wordsTheory.WORD_OR_CLAUSES,word2bytes_lemma,EL_thm] th
  val x = ref 0
  fun all_distinct [] = []
    | all_distinct (x::xs) = x :: all_distinct (filter (fn y => x !~ y) xs)
  val rs = find_terml (fn tm => type_of tm = ``:Zreg``) (concl th)
  val fs = find_terml (fn tm => type_of tm = ``:Zeflags``) (concl th)
  val ws = find_terml (can (match_term ``ZREAD_MEM2_WORD32 a``)) (concl th)
  val ws = ws @ find_terml (can (match_term ``ZWRITE_MEM2_WORD32 a``)) (concl th)
  val ws = all_distinct (map cdr ws)
  val bs = find_terml (can (match_term ``ZREAD_MEM2 a``)) (concl th)
  val bs = bs @ find_terml (can (match_term ``ZWRITE_MEM2 a``)) (concl th)
  val bs = all_distinct (map cdr bs)
  fun make_eq_tm pattern lhs name = let
    val var = mk_var(name_for_resource x name, type_of pattern)
    in mk_eq(subst [lhs |-> name] pattern,var) end
  val rs2 = map (make_eq_tm ``ZREAD_REG r s`` ``r:Zreg``) rs
  val fs2 = map (make_eq_tm ``ZREAD_EFLAG f s`` ``f:Zeflags``) fs
  val ws2 = map (make_eq_tm ``ZREAD_MEM2_WORD32 a s`` ``a:word64``) ws
  val bs2 = map (make_eq_tm ``ZREAD_MEM2 a s`` ``a:word64``) bs
  val result = rs2 @ fs2 @ ws2 @ bs2 @ [``ZREAD_RIP s = rip``]
  val th = foldr (uncurry DISCH) th result
  val th = RW [AND_IMP_INTRO,GSYM CONJ_ASSOC,wordsTheory.WORD_XOR_CLAUSES,
             wordsTheory.WORD_AND_CLAUSES,w2n_MOD] (SIMP_RULE std_ss [] th)
  in th end;

fun x64_pre_post g s = let
  fun get_arg tm = (cdr o car) tm
  val h = g
  val xs = find_terml (can (match_term ``(ZREAD_REG x s = y)``)) h
         @ find_terml (can (match_term ``(ZREAD_EFLAG x s = y)``)) h
         @ find_terml (can (match_term ``(ZREAD_MEM2_WORD32 x s = y)``)) h
         @ find_terml (can (match_term ``(ZREAD_MEM2 x s = y)``)) h
  val xs = map (fn tm => ((get_arg o cdr o car) tm, cdr tm)) xs
  val ys = find_terml (can (match_term ``ZWRITE_MEM2 a x``)) h
         @ find_terml (can (match_term ``ZWRITE_MEM2_WORD32 a x``)) h
         @ find_terml (can (match_term ``ZWRITE_EFLAG a x``)) h
         @ find_terml (can (match_term ``ZWRITE_REG a x``)) h
  val ys = map (fn tm => (get_arg tm, cdr tm)) ys
  val new_rip = (cdr o hd) (find_terml (can (match_term ``ZWRITE_RIP e``)) h)
  fun assigned_aux x y [] = y
    | assigned_aux x y ((q,z)::zs) = if aconv x q then z else assigned_aux x y zs
  fun get_assigned_value x y = assigned_aux x y ys
  fun mk_pre_post_assertion (name,var) = let
    val (pattern,name_tm,var_tm) =
          if type_of name = ``:Zreg`` then
            (``zR1 a w``,``a:Zreg``,``w:word64``)
          else if type_of name = ``:Zeflags`` then
            (``zS1 a w``,``a:Zeflags``,``w:bool option``)
          else if type_of var = ``:word8`` then
            (``~(zM1 a (SOME (w,zDATA_PERM ex)))``,``a:word64``,``w:word8``)
          else if type_of var = ``:word32`` then
            (``zM a w``,``a:word64``,``w:word32``)
          else fail()
    in (subst [name_tm|->name,var_tm|->var] pattern,
        subst [name_tm|->name,var_tm|->get_assigned_value name var] pattern) end
  val pre_post = map mk_pre_post_assertion xs
  val pre = list_mk_star (map fst pre_post) ``:x64_set -> bool``
  val post = list_mk_star (map snd pre_post) ``:x64_set -> bool``
  fun is_precond tm =
   (not (can (match_term ``ZREAD_REG r s = v``) tm) andalso
    not (can (match_term ``ZREAD_MEM2 r s = v``) tm) andalso
    not (can (match_term ``ZREAD_MEM2_WORD32 r s = v``) tm) andalso
    not (can (match_term ``CAN_ZWRITE_MEM r s``) tm) andalso
    not (can (match_term ``CAN_ZREAD_MEM r s``) tm) andalso
    not (can (match_term ``ZREAD_INSTR r s = v``) tm) andalso
    not (can (match_term ``ZREAD_EFLAG r s = v``) tm) andalso
    not (can (match_term ``ZREAD_RIP s = v``) tm)) handle e => true
  val all_conds = (list_dest dest_conj o fst o dest_imp) h
  val pre_conds = (filter is_precond) all_conds
  val ss = foldr (fn (x,y) => (fst (dest_eq x) |-> snd (dest_eq x)) :: y handle e => y) []
             (filter is_precond pre_conds)
  val ss = ss @ map ((fn tm => mk_var((fst o dest_var o cdr) tm,``:bool option``) |-> tm) o cdr)
    (filter (can (match_term ``ZREAD_EFLAG x s = SOME y``)) all_conds)
  val pre = subst ss pre
  val post = subst ss post
  val pre = mk_star (``zPC rip``,pre)
  val post = mk_star (mk_comb(``zPC``,new_rip),post)
  val pre = if null pre_conds then pre
            else mk_cond_star(pre,mk_comb(``Abbrev``,list_mk_conj pre_conds))
  in (pre,post) end;

val SING_SUBSET = prove(
  ``!x:'a y. {x} SUBSET y = x IN y``,
  REWRITE_TAC [INSERT_SUBSET,EMPTY_SUBSET]);

fun introduce_zBYTE_MEMORY_ANY th = if
  not (can (find_term (can (match_term ``zM1``))) (concl th))
  then th else let
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val (_,p,_,q) = dest_spec(concl th)
  val xs = (rev o list_dest dest_star) p
  val tm = ``~(zM1 a x)``
  val xs = filter (can (match_term tm)) xs
  fun foo tm = (fst o pairSyntax.dest_pair o cdr o cdr o cdr) tm |->
               mk_comb(mk_var("g",``:word64->word8``),(cdr o car o cdr) tm)
  val th = INST (map foo xs) th
  in if null xs then th else let
    val (_,p,_,q) = dest_spec(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = ``~(zM1 a x)``
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o car o cdr) xs)
    fun foo [] = mk_var("dg",``:word64 set``)
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``zBYTE_MEMORY_ANY ex``,foo ys),mk_var("g",``:word64->word8``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
    val th = RW [GSYM STAR_ASSOC] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL o GSYM) zBYTE_MEMORY_ANY_INSERT
    fun compact th = let
      val x = find_term (can (match_term fff)) ((car o car o concl o UNDISCH_ALL) th)
      val rw = (INST (fst (match_term fff x)) o SPEC_ALL o GSYM) zBYTE_MEMORY_ANY_INSERT
      val th = DISCH ((fst o dest_imp o concl) rw) th
      val th = SIMP_RULE bool_ss [GSYM zBYTE_MEMORY_ANY_INSERT] th
      in th end
    val th = repeat compact th
    val th = RW [STAR_ASSOC,AND_IMP_INTRO,GSYM CONJ_ASSOC] th
    val th = RW [APPLY_UPDATE_ID] th
    val v = hd (filter (is_var) ys @ ys)
    fun ss [] = ``{}:word64 set``
      | ss (v::vs) = pred_setSyntax.mk_insert(v,ss vs)
    val u1 = pred_setSyntax.mk_subset(ss (rev ys),mk_var("dg",``:word64 set``))
    val u2 = u1
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

fun introduce_zMEMORY th = if
  not (can (find_term (can (match_term ``zM``))) (concl th))
  then th else let
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val (_,p,_,q) = dest_spec(concl th)
  val xs = (rev o list_dest dest_star) p
  val tm = ``zM a x``
  val xs = filter (can (match_term tm)) xs
  fun foo tm = cdr tm |->
               mk_comb(mk_var("f",``:word64->word32``),(cdr o car) tm)
  val th = INST (map foo xs) th
  in if null xs then th else let
    val (_,p,_,q) = dest_spec(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = ``zM a x``
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o car) xs)
    fun foo [] = mk_var("df",``:word64 set``)
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``zMEMORY``,foo ys),mk_var("f",``:word64->word32``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
    val th = RW [GSYM STAR_ASSOC] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL o GSYM) zMEMORY_INSERT
    fun compact th = let
      val x = find_term (can (match_term fff)) ((car o car o concl o UNDISCH_ALL) th)
      val rw = (INST (fst (match_term fff x)) o SPEC_ALL o DISCH_ALL o GSYM o UNDISCH) zMEMORY_INSERT
      val th = DISCH ((fst o dest_imp o concl) rw) th
      val th = SIMP_RULE bool_ss [GSYM zMEMORY_INSERT] th
      in th end
    val th = repeat compact th
    val th = RW [STAR_ASSOC,AND_IMP_INTRO,GSYM CONJ_ASSOC] th
    val th = RW [APPLY_UPDATE_ID] th
    val v = hd (filter (is_var) ys @ ys)
    fun ss [] = ``{}:word64 set``
      | ss (v::vs) = pred_setSyntax.mk_insert(v,ss vs)
    val u1 = pred_setSyntax.mk_subset(ss (rev ys),mk_var("df",``:word64 set``))
    val u3 = (fst o dest_imp o concl) th
    val u2 = list_mk_conj (u1::filter is_eq (list_dest dest_conj u3))
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

fun introduce_zM64 th = if
  not (can (find_term (can (match_term ``zM``))) (concl th))
  then th else let
  val pattern = ``zM (a + 4w) x1 * zM a x2``
  val tag = (RW [GSYM STAR_ASSOC] th) |> concl |> car
            |> find_term (can (match_term pattern))
  val x1 = (cdr o cdr o car) tag
  val x2 = (cdr o cdr) tag
  val a = (cdr o car o cdr) tag
  val res = SPECL [a,mk_var("xx",``:word64``)] (RW1[STAR_COMM]zM64_def)
  val y1 = (cdr o cdr o car) ((snd o dest_eq o concl) res)
  val y2 = (cdr o cdr) ((snd o dest_eq o concl) res)
  val th = RW [GSYM res,GSYM STAR_ASSOC] (INST [x1|->y1,x2|->y2] th)
  val th = RW [STAR_ASSOC,LOAD64] th
  in th end handle HOL_ERR _ => th;

val is_spec_1 = true
val is_spec_1 = false

val SPEC_1_pat = temporalTheory.SPEC_1_def |> SPEC_ALL |> concl |> dest_eq |> fst
fun dest_spec_1 tm =
  if can (match_term SPEC_1_pat) tm then let
    val (x1234,x5) = dest_comb tm
    val (x123,x4) = dest_comb x1234
    val (x12,x3) = dest_comb x123
    val (x1,x2) = dest_comb x12
    val (x0,x1) = dest_comb x1
    in (x1,x2,x3,x4) end
  else failwith("not a SPEC_1")

fun introduce_zMEMORY64_spec_or_spec_1 th is_spec_1 =
  let val th = introduce_zM64 th in
  if not (can (find_term (can (match_term ``zM64``))) (concl th))
  then th else let
  val pre_conv = if is_spec_1 then RATOR_CONV o PRE_CONV else PRE_CONV
  val th = CONV_RULE (pre_conv STAR_REVERSE_CONV) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val th = CONV_RULE (pre_conv STAR_REVERSE_CONV) th
  val (_,p,_,q) = dest_spec(concl th) handle HOL_ERR _ => dest_spec_1(concl th)
  val xs = (rev o list_dest dest_star) p
  val tm = ``zM64 a x``
  val xs = filter (can (match_term tm)) xs
  fun foo tm = cdr tm |->
               mk_comb(mk_var("f",``:word64->word64``),(cdr o car) tm)
  val th = INST (map foo xs) th
  in if null xs then th else let
    val (_,p,_,q) = dest_spec(concl th) handle HOL_ERR _ => dest_spec_1(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = ``zM64 a x``
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o car) xs)
    fun foo [] = mk_var("df",``:word64 set``)
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``zMEMORY64``,foo ys),mk_var("f",``:word64->word64``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
             handle HOL_ERR _ =>
             SPEC frame (MATCH_MP temporalTheory.SPEC_1_FRAME th)
    val th = RW [GSYM STAR_ASSOC,SEP_CLAUSES] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL o GSYM) zMEMORY64_INSERT
    fun compact th = let
      val x = find_term (can (match_term fff)) ((car o car o concl o UNDISCH_ALL) th)
      val rw = (INST (fst (match_term fff x)) o SPEC_ALL o DISCH_ALL o GSYM o UNDISCH) zMEMORY64_INSERT
      val th = DISCH ((fst o dest_imp o concl) rw) th
      val th = SIMP_RULE bool_ss [GSYM zMEMORY64_INSERT] th
      in th end
    val th = repeat compact th
    val th = RW [STAR_ASSOC,AND_IMP_INTRO,GSYM CONJ_ASSOC] th
    val th = RW [APPLY_UPDATE_ID] th
    val v = hd (filter (is_var) ys @ ys)
    fun ss [] = ``{}:word64 set``
      | ss (v::vs) = pred_setSyntax.mk_insert(v,ss vs)
    val u1 = pred_setSyntax.mk_subset(ss (rev ys),mk_var("df",``:word64 set``))
    val u3 = (fst o dest_imp o concl) th
    val u2 = list_mk_conj (u1::filter is_eq (list_dest dest_conj u3))
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
    val th = RW [GSYM progTheory.SPEC_MOVE_COND,
                 GSYM temporalTheory.SPEC_MOVE_1_COND] th
    val th = remove_primes th
    val th = REWRITE_RULE [SING_SUBSET] th
    val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
    in th end end end

fun introduce_zMEMORY64 th = introduce_zMEMORY64_spec_or_spec_1 th false;
fun introduce_zMEMORY64_1 th = introduce_zMEMORY64_spec_or_spec_1 th true;

(*
fun introduce_zSTACK th =
  if not (can (find_term (fn x => x = ``RSP``)) (concl th)) then th else let
  val pattern = ``zM (a + 4w) x1 * zM a x2``
  val tag = (RW [GSYM STAR_ASSOC] th) |> concl |> car
            |> find_term (can (match_term pattern))
  val x1 = (cdr o cdr o car) tag
  val x2 = (cdr o cdr) tag
  val a = (cdr o car o cdr) tag
  val _ = mem (mk_var("r4",``:word64``)) (free_vars a) orelse fail()
  val res = SPECL [a,mk_var("xx",``:word64``)] (RW1[STAR_COMM]zM64_def)
  val y1 = (cdr o cdr o car) ((snd o dest_eq o concl) res)
  val y2 = (cdr o cdr) ((snd o dest_eq o concl) res)
  val th = RW [GSYM res,GSYM STAR_ASSOC] (INST [x1|->y1,x2|->y2] th)
  val th = RW [STAR_ASSOC,LOAD64] th
  in th end handle HOL_ERR _ => th;
*)

fun calculate_length_and_jump th = let
  val (_,_,c,q) = dest_spec (concl th)
  val l = c |> car |> cdr |> cdr |> listSyntax.dest_list |> fst |> length
  in
    let val v = find_term (can (match_term ``zPC (p + n2w n)``)) q
    in (th,l,SOME (0 + (numSyntax.int_of_term o cdr o cdr o cdr) v)) end
  handle e =>
    let val v = find_term (can (match_term ``zPC (p - n2w n)``)) q
    in (th,l,SOME (0 - (numSyntax.int_of_term o cdr o cdr o cdr) v)) end
  handle e =>
    (th,l,NONE) end

fun post_process_thm mpred no_status th = let
  val th = if mpred = zMEM_MEMORY64 then introduce_zMEMORY64 th else th
  (* val th = if mpred = zMEM_AUTO then introduce_zSTACK th else th *)
  val th = RW [GSYM zR_def] th
  val th = SIMP_RULE (std_ss++sw2sw_ss++w2w_ss) [wordsTheory.word_mul_n2w,SEP_CLAUSES] th
  val th = CONV_RULE FIX_WORD32_ARITH_CONV th
  val th = if mpred = zMEM_AUTO then introduce_zMEMORY th else th
  val th = introduce_zBYTE_MEMORY_ANY th
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
  val th = if no_status then th else repeat f th
  val th = RW [ALIGNED_def] th
  val th = SIMP_RULE std_ss [wordsTheory.WORD_EQ_SUB_ZERO,w2w_eq_n2w,w2w_CLAUSES] th
  val th = th |> SIMP_RULE (std_ss++wordsLib.SIZES_ss) [WORD_w2w_OVER_BITWISE,
                   WORD_w2w_n2w_OVER_BITWISE,w2w_OVER_ARITH,w2w_OVER_ARITH_n2w]
              |> SIMP_RULE (std_ss++wordsLib.SIZES_ss) [w2w_w2w,w2w_id,w2n_n2w,
                   WORD_ALL_BITS,WORD_BITS_BITS_ZERO,WORD_BITS_NOT_BITS_ZERO]
  in calculate_length_and_jump th end;

fun calc_code th = let
  val tms = find_terml (can (match_term ``ZREAD_INSTR a s = SOME x``)) (concl th)
  val tms = map dest_eq tms
  fun addr tm = (Arbnum.toInt o numSyntax.dest_numeral o cdr o cdr o cdr o car) tm
                handle e => 0
  val tms = map (fn (x,y) => (addr x, cdr y)) tms
  val code = map snd (sort (fn (x,_) => fn (y,_) => x <= y) tms)
  in listSyntax.mk_list (code, ``:word8``) end;

fun x64_prove_one_spec_or_spec_1 th c is_spec_1 = let
  val g = concl th
  val s = find_term (can (match_term ``X64_NEXT x = SOME y``)) g
  val s = (snd o dest_comb o snd o dest_comb) s
  val (pre,post) = x64_pre_post g s
  val tm = if is_spec_1
           then ``SPEC_1 X64_MODEL pre {(rip,c)} post SEP_F``
           else ``SPEC X64_MODEL pre {(rip,c)} post``
  val tm = subst [mk_var("pre",type_of pre) |-> pre,
                  mk_var("post",type_of post) |-> post,
                  mk_var("c",type_of c) |-> c] tm
  val FLIP_TAC = CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ])
  val th1 = Q.INST [`s`|->`X64_ICACHE_UPDATE x (r,e,t,m,i)`] th
  val th1 = RW [ZREAD_CLAUSES,ZWRITE_MEM2_WORD32_def] th1
  val th1 = RW [ZWRITE_EFLAG_def,X64_ICACHE_UPDATE_def,ZWRITE_MEM2_def,
        ZWRITE_REG_def,
        APPLY_UPDATE_THM,WORD_EQ_ADD_CANCEL,x64_address_lemma,ZWRITE_RIP_def] th1
  val th = prove(tm,
(*
    set_goal([],tm)
*)
    MATCH_MP_TAC (if is_spec_1 then IMP_X64_SPEC_1 else IMP_X64_SPEC)
    \\ REPEAT STRIP_TAC
    \\ EXISTS_TAC ((cdr o cdr o concl o UNDISCH) th1)
    \\ STRIP_TAC \\ REWRITE_TAC [X64_ICACHE_UPDATE_def]
    THENL [MATCH_MP_TAC th1,ALL_TAC]
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x64_2set, IN_DELETE, APPLY_UPDATE_THM, Zreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Zeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET, SEP_CLAUSES,X64_ICACHE_UPDATE_def,ZCLEAR_ICACHE_def,
         X64_ICACHE_REVERT_def,zM_def,WORD_EQ_ADD_CANCEL,x64_address_lemma]
    \\ ONCE_REWRITE_TAC [CODE_POOL_x64_2set]
    \\ REWRITE_TAC [listTheory.LENGTH,address_list_def]
    \\ SIMP_TAC std_ss [arithmeticTheory.ADD1,X64_ICACHE_EXTRACT_def]
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_x64_2set, IN_DELETE, APPLY_UPDATE_THM, Zreg_distinct,
         GSYM ALIGNED_def, wordsTheory.n2w_11, Zeflags_distinct,
         Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET, INSERT_SUBSET,
         EMPTY_SUBSET,x64_pool_def,X64_ACCURATE_CLAUSES]
    \\ SIMP_TAC std_ss [ZREAD_REG_def,ZREAD_EFLAG_def,ZREAD_RIP_def]
    \\ NTAC 3 (FLIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO])
    \\ SIMP_TAC std_ss [CAN_ZREAD_MEM,CAN_ZWRITE_MEM,IN_INSERT,word_arith_lemma1]
    \\ SIMP_TAC std_ss [ZREAD_MEM2_WORD32_def,ZREAD_MEM2_WORD64_def,
         ZREAD_MEM2_def,wordsTheory.WORD_ADD_0]
    \\ SIMP_TAC std_ss [bit_listTheory.bytes2word_thm,IN_zDATA_PERM]
    \\ SIMP_TAC std_ss [CAN_ZREAD_MEM,CAN_ZWRITE_MEM,IN_INSERT,word_arith_lemma1]
    \\ SIMP_TAC std_ss [bit_listTheory.bytes2word_thm,IN_zDATA_PERM]
    THEN1 (SIMP_TAC std_ss [GSYM arithmeticTheory.ADD_ASSOC]
           \\ SIMP_TAC std_ss [bit_listTheory.bytes2word_thm,IN_zDATA_PERM]
           \\ SIMP_TAC std_ss [arithmeticTheory.ADD_ASSOC]
           \\ SIMP_TAC std_ss [markerTheory.Abbrev_def]
           \\ REPEAT STRIP_TAC \\ FLIP_TAC \\ MATCH_MP_TAC (GEN_ALL ZREAD_INSTR_IMP)
           \\ Q.EXISTS_TAC `T` \\ ASM_SIMP_TAC std_ss []
           \\ FULL_SIMP_TAC std_ss [wordsTheory.word_add_n2w,GSYM wordsTheory.WORD_ADD_ASSOC])
    \\ SIMP_TAC std_ss [word2bytes_thm,EL_thm,INSERT_SUBSET,IN_INSERT,EMPTY_SUBSET]
    \\ FULL_SIMP_TAC std_ss [UPDATE_x64_2set'',word_arith_lemma1,
         ALIGNED_CLAUSES,icache_revert_ID,X64_ACCURATE_UPDATE]
    \\ SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ STRIP_TAC \\ IMP_RES_TAC X64_ACCURATE_IMP
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,GSYM word_add_n2w]
    \\ SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11,INSERT_SUBSET,IN_INSERT,EMPTY_SUBSET])
  val th = INST [``w:bool``|-> (if !x64_code_write_perm then T else F)] th
  in RW [STAR_ASSOC,SEP_CLAUSES,markerTheory.Abbrev_def] th end;

fun x64_prove_one_spec th c =
  x64_prove_one_spec_or_spec_1 th c false;

fun x64_prove_one_spec_1 th c =
  x64_prove_one_spec_or_spec_1 th c true;

fun x64_prove_specs mpred no_status s = let
  val th = x64_step s
  val th = if mpred = zMEM_BYTE_MEMORY then
             RW [ZWRITE_MEM2_WORD32_def,ZREAD_MEM2_WORD32_def] th else th
  val c = calc_code th
  val th = pre_process_thm th
  val th = RW [w2n_MOD] th
(* val th = x64_prove_one_spec th c *)
  in if (is_cond o cdr o cdr o snd o dest_imp o concl) th then let
       val (x,y,z) = dest_cond (find_term is_cond (concl th))
       fun replace_conv th tm =
         if (fst o dest_eq o concl) th ~~ tm then th else ALL_CONV tm
       fun prove_branch cth th = let
         val tm1 = (fst o dest_imp o concl o ISPECL [x,y,z]) cth
         val th1 = CONV_RULE (DEPTH_CONV (replace_conv (UNDISCH (ISPECL [x,y,z] cth)))) th
         val th1 = (RW [AND_IMP_INTRO,GSYM CONJ_ASSOC] o DISCH_ALL) th1
         val th1 = x64_prove_one_spec th1 c
         val th1 = SIMP_RULE std_ss [SEP_CLAUSES] (DISCH tm1 th1)
         val th1 = RW [CONTAINER_def] th1
         val th1 = RW [RW [GSYM precond_def] (GSYM progTheory.SPEC_MOVE_COND)] th1
         in post_process_thm mpred no_status th1 end
       in (prove_branch CONTAINER_IF_T th, SOME (prove_branch CONTAINER_IF_F th)) end
     else (post_process_thm mpred no_status (x64_prove_one_spec th c),NONE) end

fun x64_jump (tm1:term) (tm2:term) (jump_length:int) (forward:bool) = ("",0)

fun x64_spec_aux mpred = cache (x64_prove_specs mpred false);

val x64_spec_aux_auto = cache (x64_prove_specs zMEM_AUTO false);
val x64_spec_aux_byte = cache (x64_prove_specs zMEM_BYTE_MEMORY false);
val x64_spec_aux_memory64 = cache (x64_prove_specs zMEM_MEMORY64 false);
val x64_spec_aux_memory64_no_status = cache (x64_prove_specs zMEM_MEMORY64 true);

fun apply_to_thm f ((th1,i1,j1),NONE) = ((f th1,i1,j1),NONE)
  | apply_to_thm f ((th1,i1,j1),SOME (th2,i2,j2)) = ((f th1,i1,j1),SOME (f th2,i2,j2))

fun x64_spec s = let
  val (s,rename,_) = parse_renamer s
  val ((th,i,j),other) = x64_spec_aux_auto s
  val b = if !x64_exec_flag then T else F
  val th = INST [``ex:bool``|->b] th
  val th = RW [GSYM zBYTE_MEMORY_def,GSYM zBYTE_MEMORY_Z_def] th
  in apply_to_thm rename ((th,i,j),other) end

fun x64_spec_byte_memory s = let
  val (s,rename,_) = parse_renamer s
  val ((th,i,j),other) = x64_spec_aux_byte s
  val b = if !x64_exec_flag then T else F
  val th = INST [``ex:bool``|->b] th
  val th = RW [GSYM zBYTE_MEMORY_def,GSYM zBYTE_MEMORY_Z_def] th
  in apply_to_thm rename ((th,i,j),other) end

fun x64_spec_memory64 s = let
  val (s,rename,_) = parse_renamer s
  val ((th,i,j),other) = x64_spec_aux_memory64 s
  val b = if !x64_exec_flag then T else F
  val th = INST [``ex:bool``|->b] th
  val th = RW [GSYM zBYTE_MEMORY_def,GSYM zBYTE_MEMORY_Z_def] th
  in apply_to_thm rename ((th,i,j),other) end

fun x64_spec_memory64_no_status s = let
  val (s,rename,_) = parse_renamer s
  val ((th,i,j),other) = x64_spec_aux_memory64_no_status s
  val b = if !x64_exec_flag then T else F
  val th = INST [``ex:bool``|->b] th
  val th = RW [GSYM zBYTE_MEMORY_def,GSYM zBYTE_MEMORY_Z_def] th
  in apply_to_thm rename ((th,i,j),other) end

val x64_tools = (x64_spec, x64_jump, x64_status, x64_pc);
val x64_tools_no_status = (x64_spec, x64_jump, TRUTH, x64_pc);
val x64_tools_64 = (x64_spec_memory64, x64_jump, x64_status, x64_pc);
val x64_tools_64_no_status = (x64_spec_memory64_no_status, x64_jump, TRUTH, x64_pc);


(*

  val mpred = zMEM_AUTO
  val th = x64_spec (x64_encode "add r0,5");
  val th = x64_spec (x64_encode "inc r11");
  val th = x64_spec (x64_encode "je 40");
  val th = x64_spec (x64_encode "loop -40");
  val th = x64_spec "E9"; (* jmp imm32 *)
  val th = x64_spec (x64_encode "add eax,5");
  val th = x64_spec (x64_encode "cmove rax, rcx");
  val th = x64_spec (x64_encode "mov al, [rax+rbx+4]");
  val th = x64_spec (x64_encode "mov [rax+rbx+4], al");
  val th = x64_spec (x64_encode "mov ax, [rax]");
  val th = x64_spec (x64_encode "mov [rax], ax");
  val th = x64_spec (x64_encode "add [rax], ax");
  val th = x64_spec (x64_encode "add [rax], eax");
  val th = x64_spec (x64_encode "add [rax], rax");
  val th = x64_spec (x64_encode "call r2");
  val th = x64_spec (x64_encode "ret");
  val th = x64_spec (x64_encode "add rsp,80");
  val th = x64_spec (x64_encode "push rax");
  val th = x64_spec (x64_encode "pop rax");
  val th = x64_spec (x64_encode "mov BYTE [r11+1],124");

  val ((th,_,_),_) = x64_spec (x64_encode "mov [rax],r1b")
  val th = th |> REWRITE_RULE [SIGN_EXTEND_IGNORE,n2w_w2n,
                   GSYM zBYTE_MEMORY_Z_def,zBYTE_MEMORY_def]
              |> Q.GEN `g` |> Q.GEN `dg`
              |> Q.INST [`r0`|->`a+n2w (LENGTH (xs:word8 list))`]
              |> MATCH_MP zCODE_HEAP_SNOC

  val ((th,_,_),_) = x64_spec "C600"
  val th = th |> REWRITE_RULE [SIGN_EXTEND_IGNORE,n2w_w2n,
                   GSYM zBYTE_MEMORY_Z_def,zBYTE_MEMORY_def]
              |> Q.GEN `g` |> Q.GEN `dg`
              |> Q.INST [`r0`|->`a+n2w (LENGTH (xs:word8 list))`,`imm8`|->`n2w k`]
              |> MATCH_MP zCODE_HEAP_SNOC

  val th = x64_spec_memory64 (x64_encode "add [rax], rax");
  val th = x64_spec_memory64 (x64_encode "mov [rax+40], rbx");
  val th = x64_spec_memory64 (x64_encode "mov rbx,[rax+40]");

  val s = "mov r8d, [r7+4*r3+6000]"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec (String.substring(s,0,size(s)-8))

  val s = "mov [r7+4*r3+6000], r8d"
  val s = x64_encode s
  val (spec,_,sts,_) = x64_tools
  val ((th,_,_),_) = spec (String.substring(s,0,size(s)-8))

  val th = x64_spec_memory64_no_status (x64_encode "adc r8,r9")
  val th = x64_spec_memory64_no_status (x64_encode "je 400")

*)

end
