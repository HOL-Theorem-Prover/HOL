structure prog_armLib :> prog_armLib =
struct

open HolKernel boolLib bossLib;
open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory prog_armTheory helperLib wordsTheory progTheory finite_mapTheory;

open armLib;

structure Parse = struct
  open Parse
  val (Type,Term) =
      prog_armTheory.prog_arm_grammars
        |> apsnd ParseExtras.grammar_loose_equality
        |> parse_from_grammars
end
open Parse

val use_stack = ref false;
fun arm_use_stack b = (use_stack := b);

val arm_enc = armLib.arm_encode_from_string;

local val arm_memory_pred = ref "auto"
in
  fun get_arm_memory_pred () = !arm_memory_pred;
  fun set_arm_memory_pred s =
    if mem s ["auto","aM1","aM","aBYTE_MEMORY","aMEM"]
    then (arm_memory_pred := s) else fail();
end;

val arm_status = aS_HIDE;
val arm_pc = ``aPC``;

fun process tm = let
  fun replace_plus c = if c = #"+" then #"_" else c;
  fun name_of_tm tm =
    "m_" ^ (implode o filter is_normal_char o map replace_plus o explode o term_to_string) tm;
  in if type_of tm = ``:word4`` then let
       val f = int_to_string o numSyntax.int_of_term o snd o dest_comb
       in (mk_comb(``aR``,tm),mk_var("r" ^ f tm,``:word32``)) end
     else if tm ~~ ``psrN:arm_bit`` then (mk_comb(``aS1``,tm),mk_var("psrn",``:bool``))
     else if tm ~~ ``psrZ:arm_bit`` then (mk_comb(``aS1``,tm),mk_var("psrz",``:bool``))
     else if tm ~~ ``psrC:arm_bit`` then (mk_comb(``aS1``,tm),mk_var("psrc",``:bool``))
     else if tm ~~ ``psrV:arm_bit`` then (mk_comb(``aS1``,tm),mk_var("psrv",``:bool``))
     else if tm ~~ ``psrQ:arm_bit`` then (mk_comb(``aS1``,tm),mk_var("psrq",``:bool``))
     else if type_of tm = ``:word32`` then
       (mk_comb(``aM1:word32 -> word8 -> arm_set -> bool``,tm),mk_var(name_of_tm tm,``:word8``))
     else fail() end;

val state = ``s:arm_state``
val r15 = mk_var("r15",``:word32``)

fun rewrite_names tm = let
  fun aux v = let val m = match_term tm (car (car v)) in (snd o process o cdr o car) v end
  in replace_terml aux end;

fun arm_pre_post s g = let
  val cpsr_var = mk_var("cpsr",``:word32``)
  val g = subst [``ARM_READ_MASKED_CPSR s``|->cpsr_var] g
  val regs = collect_term_of_type ``:word4`` g
  val regs = filter wordsSyntax.is_n2w regs
  val bits = collect_term_of_type ``:arm_bit`` g
  val h =  rewrite_names ``ARM_READ_STATUS`` (rewrite_names ``ARM_READ_REG`` g)
  val mems1 = find_terml (can (match_term ``ARM_READ_MEM a ^state``)) h
  val mems2 = find_terms (can (match_term ``ARM_WRITE_MEM a x ^state``)) h
  val mems = map (cdr o car) mems1 @ map (cdr o car o car) mems2
  val mems = filter (fn x => not (tmem x [``r15 + 3w:word32``,
               ``r15 + 2w:word32``,``r15 + 1w:word32``,r15])) mems
  val h2 = rewrite_names ``ARM_READ_MEM`` h
  val reg_assign = find_terml_all (can (match_term ``ARM_WRITE_REG r x ^state``)) h2
  val mem_assign = find_terml_all (can (match_term ``ARM_WRITE_MEM a x ^state``)) h2
  val sts_assign = find_terml_all (can (match_term ``ARM_WRITE_STATUS f x ^state``)) h2
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) reg_assign
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) mem_assign @ assignments
  val assignments = map (fn x => (cdr (car (car x)),cdr (car x))) sts_assign @ assignments
  fun all_distinct [] = []
    | all_distinct (x::xs) = x :: filter (fn y => x !~ y) (all_distinct xs)
  val mems = rev (all_distinct mems)
  val code = subst [mk_var("c",``:num``) |->
                    numSyntax.mk_numeral(Arbnum.fromHexString s)]
                   ``(r15:word32,(n2w (c:num)):word32)``
  fun is_pc_relative tm = tmem (mk_var("r15",``:word32``)) (free_vars tm)
  val mems_pc_rel = filter is_pc_relative mems
  val has_read_from_mem = (tml_eq mems_pc_rel mems) andalso (length mems = 4)
  val (mems,assignments,code) =
    if not has_read_from_mem then
      (mems,assignments,subst [mk_var("x",``:word32#word32``)|->code] ``{x:word32#word32}``)
    else let
      val xx = find_term wordsSyntax.is_word_concat h2
      val v = mk_var("pc_rel",``:word32``)
      val addr = (cdr o fst o process o hd) mems
      val assignments = map (fn (x,y) => (x,subst [xx |-> v]y)) assignments
      val code = subst [mk_var("x",``:word32#word32``)|->code,
                        mk_var("y",``:word32#word32``)|->pairSyntax.mk_pair(addr,v)]
            ``{(x:word32#word32);y}``
      in ([],assignments,code) end
  fun get_assigned_value_aux x y [] = y
    | get_assigned_value_aux x y ((q,z)::zs) =
        if x ~~ q then z else get_assigned_value_aux x y zs
  fun get_assigned_value x y = get_assigned_value_aux x y assignments
  fun mk_pre_post_assertion x = let
    val (y,z) = process x
    val q = get_assigned_value x z
    in (mk_comb(y,z),mk_comb(y,q)) end
  val pre_post = map mk_pre_post_assertion (regs @ bits @ mems)
  val pre = list_mk_star (map fst pre_post) ((type_of o fst o hd) pre_post)
  val post = list_mk_star (map snd pre_post) ((type_of o fst o hd) pre_post)
  val (pre,post) = if not (tmem cpsr_var (free_vars g)) then (pre,post) else let
    val res = (fst o dest_eq o concl o SPEC cpsr_var) aCPSR_def
    in (mk_star(pre,res),mk_star(post,res)) end
  fun match_any [] tm = fail ()
    | match_any (x::xs) tm = match_term x tm handle HOL_ERR _ => match_any xs tm
  fun pass tm = let
    val (s,i) = match_any [``ARM_OK s``,
                           ``ALIGNED r15``,
                           ``ARM_READ_MEM (r15 + 3w) s = n2w n``,
                           ``ARM_READ_MEM (r15 + 2w) s = n2w n``,
                           ``ARM_READ_MEM (r15 + 1w) s = n2w n``,
                           ``ARM_READ_MEM (r15 + 0w) s = n2w n``,
                           ``ARM_READ_MEM r15 s = n2w n``] tm
    in subst s r15 !~ r15 end handle HOL_ERR _ => true
  val pre_conds = (filter pass o list_dest dest_conj o fst o dest_imp) h
  val pre_conds = filter (not o can (find_term (fn x => x ~~ ``ARM_READ_MEM``))) pre_conds
  val pre_conds = filter (fn x => not (is_neg x andalso is_eq (cdr x) andalso tmem r15 (free_vars x))) pre_conds
  fun all_bool tm =
    null (filter (fn x => not (type_of x = ``:bool``)) (free_vars tm))
  val bools = filter all_bool pre_conds
  val pre_conds = if null bools then pre_conds else let
                    val pre_bool = (fst o dest_eq o concl o SPEC (list_mk_conj bools)) markerTheory.Abbrev_def
                    in pre_bool :: filter (not o all_bool) pre_conds end
  val pc_post = snd (hd (filter (fn x => (fst x ~~ ``15w:word4``)) assignments))
  val pc = mk_var("r15",``:word32``)
  val pre_conds = if tmem pc (free_vars pc_post) then pre_conds else mk_comb(``ALIGNED``,pc_post) :: pre_conds
  val pre = if null pre_conds then pre else mk_cond_star(pre,mk_comb(``CONTAINER``,list_mk_conj pre_conds))
  val ss = subst [``aR 15w``|->``aPC``,pc|->``p:word32``]
  in (ss pre,ss code,ss post) end;

fun remove_primes th = let
  fun last s = substring(s,size s-1,1)
  fun delete_last_prime s = if last s = "'" then substring(s,0,size(s)-1) else fail()
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

fun introduce_aBYTE_MEMORY th = if
  not (can (find_term (can (match_term ``aM1``))) (concl th))
  then th else let
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val (_,p,_,q) = dest_spec(concl th)
  val xs = (rev o list_dest dest_star) p
  val tm = (fst o dest_eq o concl o SPEC_ALL) aM1_def
  val xs = filter (can (match_term tm)) xs
  fun foo tm = cdr tm |-> mk_comb(mk_var("f",``:word32->word8``),(cdr o car) tm)
  val th = INST (map foo xs) th
  in if null xs then th else let
    val (_,p,_,q) = dest_spec(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = (fst o dest_eq o concl o SPEC_ALL) aM1_def
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o car) xs)
    fun foo [] = mk_var("df",``:word32 set``)
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``aBYTE_MEMORY``,foo ys),mk_var("f",``:word32->word8``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
    val th = RW [GSYM STAR_ASSOC] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL o GSYM) aBYTE_MEMORY_INSERT
    fun compact th = let
      val x = find_term (can (match_term fff)) ((car o car o concl o UNDISCH_ALL) th)
      val rw = (INST (fst (match_term fff x)) o SPEC_ALL o GSYM) aBYTE_MEMORY_INSERT
      val th = DISCH ((fst o dest_imp o concl) rw) th
      val th = SIMP_RULE bool_ss [GSYM aBYTE_MEMORY_INSERT] th
      in th end
    val th = repeat compact th
    val th = RW [STAR_ASSOC,AND_IMP_INTRO,GSYM CONJ_ASSOC] th
    val th = RW [APPLY_UPDATE_ID] th
    (* val te = (cdr o car o find_term (can (match_term (cdr fff))) o concl) th
    val t1 = repeat (snd o pred_setSyntax.dest_insert) te
    val t2 = repeat (fst o pred_setSyntax.dest_delete) t1
    val th = SIMP_RULE bool_ss [] (DISCH (mk_eq(te,t2)) th)
    val th = RW [AND_IMP_INTRO] th *)
    val v = hd (filter (is_var) ys @ ys)
    fun ss [] = ``{}:word32 set``
      | ss (v::vs) = pred_setSyntax.mk_insert(v,ss vs)
    val u1 = pred_setSyntax.mk_subset(ss (rev ys),mk_var("df",``:word32 set``))
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

fun introduce_aM th = let
  val index = ref 0
  fun next_var () = (index := (!index)+1; mk_var("w" ^ int_to_string (!index),``:word32``))
  val lemma = (el 2 o CONJUNCTS o SPEC_ALL) bit_listTheory.bytes2word_thm
  val f = SIMP_RULE std_ss [WORD_ADD_0] o
          SIMP_RULE std_ss [word_arith_lemma3,word_arith_lemma4] o
          SIMP_RULE std_ss [word_arith_lemma1,word_arith_lemma2]
  val th = f th
  fun foo th = let
    val tm = (fst o dest_eq o concl o SPEC (next_var()) o GEN_ALL) lemma
    val tm2 = find_term (fn t => car t ~~ car tm handle HOL_ERR _ => false) (concl th)
    in RW [lemma] (INST (fst (match_term tm2 tm)) th) end
  fun hoo th = let
    val (_,p,_,_) = dest_spec(concl th)
    fun is_aM1 tm = (``aM1`` ~~ repeat car tm)
    val xs = (filter is_aM1 o list_dest dest_star) p
    val _ = if length xs < 4 then fail() else ()
    val th = RW [f (SPEC ((cdr o car o hd) xs) aM_INTRO),bit_listTheory.bytes2word_INTRO] th
    in repeat foo th end
  in repeat hoo th end;

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
  fun foo tm = cdr tm |-> mk_comb(mk_var("f",``:word32->word32``),(cdr o car) tm)
  val th = INST (map foo xs) th
  in if null xs then th else let
    val (_,p,_,q) = dest_spec(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = (fst o dest_eq o concl o SPEC_ALL) aM_def
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o car) xs)
    fun foo [] = mk_var("df",``:word32 set``)
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``aMEMORY``,foo ys),mk_var("f",``:word32->word32``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
    val th = RW [GSYM STAR_ASSOC] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) aMEMORY_INSERT
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

(*
val th1 = th
val th = th1
*)

val introduce_aMEM_lemma =
  Q.GEN `x` (CONJ (Q.SPEC `x` WRITE32_THM) (Q.SPEC `x` (GSYM READ32_def)));
val introduce_aMEM_pattern = aBYTE_MEMORY_def |> SPEC_ALL |> concl |> dest_eq |> fst;
val introduce_aMEM_pattern2 = ``(w:word8 @@ v:word24):word32``
fun introduce_aMEM_aux th = let
  val th = Q.INST [`df`|->`FDOM (m:word32 |-> word8)`,`f`|->`\x. m ' x`] th
  val xs = map cdr (find_terms (can (match_term ``ALIGNED w``)) (concl th))
  val xs = map (fn x => (cdr o cdr o cdr o cdr) x handle HOL_ERR _ => ``0w:word32``)
             (find_terms (can (match_term introduce_aMEM_pattern2)) (concl th)) @ xs
  fun foo tm = (cdr o car o car o cdr o cdr o cdr) tm ::
               foo ((cdr o cdr o cdr o cdr) tm) handle HOL_ERR _ => []
  val xs = foo (find_term (can (match_term ``(a:word32 =+ w:word8) f``)) (concl th)) @ xs
           handle HOL_ERR _ => xs
  val lemma = LIST_CONJ
    (map (fn x => SIMP_RULE std_ss [word_arith_lemma1,word_arith_lemma3,word_arith_lemma4] (SPEC x introduce_aMEM_lemma)) xs)
    handle HOL_ERR _ => TRUTH
  val th = SIMP_RULE std_ss [GSYM aMEM_def,lemma] th
  val th = SIMP_RULE std_ss [aMEM_WRITE_BYTE] th
  val (_,_,_,q) = dest_spec (concl th)
  in if not (can (find_term (can (match_term introduce_aMEM_pattern))) q) then
       th else let
  val tm = find_term (can (match_term introduce_aMEM_pattern)) q
  val tm2 = tm |> cdr |> dest_abs |> snd |> car |> cdr
  val goal = mk_eq(tm,cdr(car(concl (SPEC tm2 aMEM_def))))
  val assum = th |> SIMP_RULE std_ss [SPEC_MOVE_COND] |> concl |> dest_imp |> fst
  val lemma = prove(mk_imp(assum,goal),
    REPEAT STRIP_TAC THEN REWRITE_TAC [aMEM_def]
    THEN AP_THM_TAC THEN AP_TERM_TAC
    THEN FULL_SIMP_TAC std_ss [INSERT_SUBSET,WRITE32_def,FDOM_FUPDATE,EXTENSION]
    THEN FULL_SIMP_TAC std_ss [word_arith_lemma1,word_arith_lemma3,word_arith_lemma4]
    THEN FULL_SIMP_TAC std_ss [IN_INSERT]
    THEN REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
    THEN FULL_SIMP_TAC std_ss [WORD_ADD_0]
    THEN CCONTR_TAC THEN FULL_SIMP_TAC std_ss [])
  val th = SIMP_RULE std_ss [SPEC_MOVE_COND] th
  val lemma = UNDISCH lemma
  val tt = lemma |> concl |> dest_eq |> fst
  val th = CONV_RULE (DEPTH_CONV (fn tm => if tm ~~ tt then lemma else NO_CONV tm)) (UNDISCH th)
  val th = SIMP_RULE std_ss [GSYM SPEC_MOVE_COND] (DISCH_ALL th)
  in th end end;

fun collect_READ32_WRITE32 th = let
  val xs = map cdr (find_terms (can (match_term ``ALIGNED w``)) (concl th))
  val xs = map (fn x => (cdr o cdr o cdr o cdr) x handle HOL_ERR _ => ``0w:word32``)
             (find_terms (can (match_term introduce_aMEM_pattern2)) (concl th)) @ xs
  fun foo tm = (cdr o car o car o cdr o cdr o cdr) tm ::
               foo ((cdr o cdr o cdr o cdr) tm) handle HOL_ERR _ => []
  val xs = foo (find_term (can (match_term ``(a:word32 =+ w:word8) f``)) (concl th)) @ xs
           handle HOL_ERR _ => xs
  val lemma = LIST_CONJ
    (map (fn x => SIMP_RULE std_ss [word_arith_lemma1,word_arith_lemma3,word_arith_lemma4] (SPEC x introduce_aMEM_lemma)) xs)
    handle HOL_ERR _ => TRUTH
  val th = RW [lemma] th
  in th end

fun introduce_aMEM th = let
  val th = introduce_aBYTE_MEMORY th
  val th = collect_READ32_WRITE32 th
  val th = Q.INST [`df`|->`dm`,`f`|->`m`] th
  val th = RW1 [GSYM WRITE8_def] th
  val m = mk_var("m",``:word32->word8``)
  fun READ8_CONV tm =
    if rator tm ~~ m then REWR_CONV (GSYM READ8_def) tm else NO_CONV tm
  val th = CONV_RULE (DEPTH_CONV READ8_CONV) th
  (* val th = introduce_aMEM_aux th
     val _ = not (can (find_term (fn tm => tm = ``aBYTE_MEMORY``)) (concl th)) orelse fail() *)
  in th end

fun introduce_aSTACK th =
  if not (!use_stack) then th else th (* let
  val (_,p,c,q) = dest_spec(concl th)
  val sp = mk_var("r13",``:word32``)
  fun access_sp tm = (tm = sp) orelse
    (can (match_term ``(v:word32) - n2w n``) tm andalso (sp = (cdr o car) tm))
  val tm1 = find_terms (fn tm =>
              can (match_term ``aM x y``) tm andalso (access_sp o cdr o car) tm) p
  val tm2 = find_terms (fn tm =>
              can (match_term ``aM x y``) tm andalso (access_sp o cdr o car) tm) q
  val tm = cdr (find_term (can (match_term ``aR 13w w``)) q)
  fun genlist 0 f = []
    | genlist n f = f n :: genlist (n-1) f
  val (stack_pre,stack_post) =
    if wordsSyntax.is_word_sub tm then (* this is a push *) let
      val n = numSyntax.int_of_term (cdr (cdr tm)) div 4
      val pre = subst [``n:num``|->numSyntax.term_of_int n] ``aSTACK bp (l+n,ss)``
      val post = ``aSTACK bp (l,ss ++ xs)``
    else if wordsSyntax.is_word_add tm then (* this is a pop *) let
      val n = numSyntax.int_of_term (cdr (cdr tm)) div 4
    else fail()
  val tm2 = find_term (can (match_term (mk_comb(car tm1,genvar(``:word32``))))) q
  val c1 = MOVE_OUT_CONV ``aR 11w`` THENC MOVE_OUT_CONV (car tm1)
  val c2 = MOVE_OUT_CONV ``aR 11w`` THENC MOVE_OUT_CONV (car tm2)
  val th = CONV_RULE (POST_CONV c2 THENC PRE_CONV c1) th
  val th = DISCH ``ALIGNED r11`` th
  val th = SIMP_RULE bool_ss [ALIGNED,SEP_CLAUSES] th
  val th = MATCH_MP aSTACK_INTRO th handle HOL_ERR e =>
           MATCH_MP (RW [WORD_SUB_RZERO] (Q.INST [`n`|->`0`] aSTACK_INTRO)) th
  fun mk_stack_var i = mk_var("s" ^ int_to_string i,``:word32``)
  val index = (Arbnum.toInt o numSyntax.dest_numeral o cdr o cdr o cdr o car) tm1
              handle HOL_ERR _ => 0
  val index = index div 4
  fun mk_slist i = if i = 0 then ``[]:word32 list`` else
                     listSyntax.mk_cons(mk_stack_var (index - i), mk_slist (i-1))
  val th = SPECL [mk_slist index,mk_var("ss",``:word32 list``)] th
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [listTheory.LENGTH]) THENC
                      REWRITE_CONV [listTheory.APPEND]) th
  val th = INST [cdr tm1 |-> mk_stack_var index] th
  in th end handle HOL_ERR _ => th *);

fun calculate_length_and_jump th =
  let val (_,_,_,q) = dest_spec(concl th) in
  let val v = find_term (fn t => t ~~ ``aPC (p + 4w)``) q in (th,4,SOME 4) end
  handle e =>
  let val v = find_term (can (match_term ``aPC (p + n2w n)``)) q
  in (th,4,SOME (0 + (numSyntax.int_of_term o cdr o cdr o cdr) v)) end
  handle e =>
  let val v = find_term (can (match_term ``aPC (p - n2w n)``)) q
  in (th,4,SOME (0 - (numSyntax.int_of_term o cdr o cdr o cdr) v)) end
  handle e => (th,4,NONE) end

val sp_var = mk_var("r13",``:word32``);
val has_stack_access_pattern = aM1_def |> SPEC_ALL |> concl |> dest_eq |> fst
fun has_stack_access th = let
  val xs = find_terms (can (match_term has_stack_access_pattern)) (concl th)
  in exists (tmem sp_var o free_vars) xs end;

fun post_process_thm th = let
  val th = SIMP_RULE (std_ss++sw2sw_ss++w2w_ss) [wordsTheory.word_mul_n2w] th
  val th = CONV_RULE FIX_WORD32_ARITH_CONV th
  val th = if mem (get_arm_memory_pred()) ["auto","aM"] then introduce_aM th else th
  val th = introduce_aSTACK th
  val th = if mem (get_arm_memory_pred()) ["auto","aBYTE_MEMORY"]
           then introduce_aBYTE_MEMORY th else th
  val th = if not (get_arm_memory_pred() = "aMEM") then th else
             if has_stack_access th then (introduce_aM th)
             else introduce_aMEM th
  val th = if get_arm_memory_pred() = "auto" then introduce_aMEMORY th else th
  val th = RW [WORD_EQ_XOR_ZERO,wordsTheory.WORD_EQ_SUB_ZERO,ALIGNED_def,
               WORD_TIMES2,WORD_SUB_INTRO] th
  in calculate_length_and_jump th end;

val pc_rel = mk_var("pc_rel",``:word32``)
fun FIX_PC_REL_CONV tm =
  if is_eq tm andalso tmem pc_rel (free_vars (cdr tm)) then SYM_CONV tm else ALL_CONV tm
fun RESTORE_FIX_PC_REL_CONV tm =
  if is_eq tm andalso tmem pc_rel (free_vars (car tm)) then SYM_CONV tm else ALL_CONV tm

fun arm_prove_one_spec s th = let
  val g = concl th
  val next = cdr (find_term (can (match_term ``ARM_NEXT x s = s'``)) g)
  val (pre,code,post) = arm_pre_post s g
  val tm = ``SPEC ARM_MODEL pre code post``
  val tm = subst [mk_var("pre",type_of pre) |-> pre,
                  mk_var("post",type_of post) |-> post,
                  mk_var("code",type_of code) |-> code] tm
  val FLIP_TAC = CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ])
(*
  set_goal([],tm)
*)
  val result = prove(tm,
    MATCH_MP_TAC IMP_ARM_SPEC \\ REPEAT STRIP_TAC \\ EXISTS_TAC (cdr next)
    \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [GSYM STAR_ASSOC,
         STAR_arm2set, CODE_POOL_arm2set, aPC_def, IN_DELETE,
         APPLY_UPDATE_THM, GSYM ALIGNED_def, wordsTheory.n2w_11,WORD_ADD_0,
         arm_stepTheory.arm_bit_distinct, Q.SPECL [`s`,`x INSERT t`] SET_EQ_SUBSET,
         INSERT_SUBSET, EMPTY_SUBSET, ARM_READ_WRITE, GSYM ADDR30_def]
    \\ NTAC 3 (FLIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO])
    \\ FLIP_TAC \\ REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC]
    \\ SIMP_TAC std_ss [] \\ FLIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    THEN1 (SIMP_TAC std_ss [ALIGNED_def] \\ FLIP_TAC
           \\ REPEAT (Q.PAT_X_ASSUM `xxx = ARM_READ_MEM x s` MP_TAC)
           \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
           \\ REPEAT (Q.PAT_X_ASSUM `ARM_READ_REG x s = xxx` (fn th => ONCE_REWRITE_TAC [GSYM th] THEN MP_TAC th))
           \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC th
           \\ FULL_SIMP_TAC std_ss [ALIGNED_def,ARM_READ_UNDEF_def,
                markerTheory.Abbrev_def,CONTAINER_def,aligned4_thm,WORD_ADD_0]
           \\ REPEAT (POP_ASSUM MP_TAC) \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
           \\ SIMP_TAC std_ss [BYTES_TO_WORD_LEMMA] \\ REPEAT STRIP_TAC \\ EVAL_TAC)
    \\ ASM_SIMP_TAC std_ss [UPDATE_arm2set'',ALIGNED_CLAUSES,
                            ARM_WRITE_STS_INTRO,ARM_READ_WRITE]
    \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
    \\ ASM_SIMP_TAC std_ss [wordsTheory.WORD_ADD_0,ARM_READ_WRITE]
    \\ FULL_SIMP_TAC bool_ss [markerTheory.Abbrev_def,CONTAINER_def]
    \\ REPEAT (POP_ASSUM (MP_TAC o GSYM)) \\ ASM_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,BYTES_TO_WORD_LEMMA])
  in RW [STAR_ASSOC,CONTAINER_def] result end;

val cond_STAR_cond = prove(
  ``!x y. cond (x /\ y) = cond x * (cond y):'a set -> bool``,
  SIMP_TAC (std_ss) [SEP_CLAUSES]);

val precond_INTRO = prove(
  ``!x. cond (Abbrev x) = precond x:'a set -> bool``,
  SIMP_TAC (std_ss) [SEP_CLAUSES,precond_def,markerTheory.Abbrev_def]);

val minus_one = EVAL ``-1w:word32``
val minus_one_mult =
  REWRITE_CONV [GSYM minus_one,GSYM WORD_NEG_MUL,GSYM word_sub_def]
   ``x + (0xFFFFFFFFw:word32) * y``
val minus_one_mult = CONJ (RW1 [WORD_ADD_COMM] minus_one_mult) minus_one_mult
val minus_one_mult = CONJ (RW1 [WORD_MULT_COMM] minus_one_mult) minus_one_mult

val ARM_WRITE_STATUS_T_IGNORE_UPDATE = prove(
  ``(~ARM_READ_STATUS psrT s ==> (ARM_WRITE_STATUS psrT F s = s)) /\
    (ARM_WRITE_STATUS psrT b (ARM_WRITE_REG r w s) =
     ARM_WRITE_REG r w (ARM_WRITE_STATUS psrT b s))``,
  EVAL_TAC \\ SRW_TAC [] [FUN_EQ_THM,APPLY_UPDATE_THM,
    arm_seq_monadTheory.arm_state_component_equality,
    arm_coretypesTheory.ARMpsr_component_equality] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC std_ss []);

val aligned_bx_lemma = prove(
  ``!w:word32. aligned (w,4) ==> aligned_bx w /\ ~(w ' 0)``,
  SIMP_TAC std_ss [aligned4_thm,ALIGNED_BITS,arm_stepTheory.aligned_bx_thm]);

fun remove_aligned_bx th = let
  val tm = cdr (find_term (can (match_term ``aligned_bx (w:word32)``)) (concl th))
  val imp = SPEC tm aligned_bx_lemma
  val th = SIMP_RULE std_ss [imp] (DISCH ((fst o dest_imp o concl) imp) th)
  val th = RW [AND_IMP_INTRO] th
  val th = SIMP_RULE std_ss [ARM_WRITE_STATUS_T_IGNORE_UPDATE] th
  in th end handle HOL_ERR _ => th;

fun arm_prove_specs m_pred s = let
  val (s,rename,_) = parse_renamer s
  val _ = set_arm_memory_pred m_pred
  val thms = [arm_step "v6" s]
  val thms = (thms @ [arm_step "v6,fail" s]) handle HOL_ERR _ => thms
  val thms = map (RW [minus_one,minus_one_mult]) thms
  val th = hd thms
  val ARM_READ_MASKED_CPSR = ARM_READ_MASKED_CPSR_def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat car
  fun derive_spec th = let
    val th = SPEC state th
    val th = RW [ADD_WITH_CARRY_SUB,pairTheory.FST,pairTheory.SND,ADD_WITH_CARRY_SUB_n2w] th
    val th = SIMP_RULE std_ss [] th
    val th = remove_aligned_bx th
    val tm = (fst o dest_eq o concl o SPEC state) ARM_OK_def
    val th = (RW [AND_IMP_INTRO] o RW [GSYM ARM_OK_def] o SIMP_RULE bool_ss [ARM_OK_def] o DISCH tm) th
    val th = SIMP_RULE std_ss [aligned4_thm,aligned2_thm,ARM_READ_MASKED_CPSR_INTRO] th
    val th = if not (can (find_term (fn x => x ~~ ARM_READ_MASKED_CPSR)) (concl th)) then th else let
               val th = SIMP_RULE std_ss [FCP_UPDATE_WORD_AND] th
               val gg = SIMP_RULE (std_ss++SIZES_ss) [bitTheory.BIT_def,bitTheory.BITS_THM] o
                        RW1 [fcpTheory.FCP_APPLY_UPDATE_THM,word_index_n2w]
               fun f th = let
                 val t2 = find_term (can (match_term ``(n :+ F) ((n2w k):word32)``)) (concl th)
                 in RW [EVAL t2] th end
               in repeat f ((gg o gg o gg o gg o gg)th) end
    val th = SIMP_RULE std_ss [word_arith_lemma1] th
    val th = arm_prove_one_spec s th
    in post_process_thm th end
  val result = map derive_spec thms
  in if length result < 2 then let
    val (th1,i1,j1) = hd result
    val th1 = REWRITE_RULE [markerTheory.Abbrev_def,SEP_CLAUSES] th1
    in ((rename th1,i1,j1), NONE) end
  else let
    val (th1,i1,j1) = hd result
    val (th2,i2,j2) = hd (tl result)
    val th2 = PURE_REWRITE_RULE [GSYM precond_def,markerTheory.Abbrev_def] th2
    val th1 = RW [cond_STAR_cond] th1
    val th1 = RW [precond_INTRO] th1
    val th1 = SIMP_RULE (std_ss++sep_cond_ss) [] th1
    in ((rename th1,i1,j1), SOME (rename th2,i2,j2)) end end

fun arm_jump tm1 tm2 jump_length forward = let
  fun arm_mk_jump cond jump_length = let
    val s = "b" ^ cond ^ (if forward then " +#" else " -#") ^ (int_to_string jump_length)
    fun prefix_zero s = if length (explode s) < 8 then prefix_zero ("0"^s) else s
    in prefix_zero (arm_enc s) end;
  val (x,y) = if tm2 ~~ ``aS1 psrN`` then ("mi","pl") else
              if tm2 ~~ ``aS1 psrZ`` then ("eq","ne") else
              if tm2 ~~ ``aS1 psrC`` then ("cs","cc") else
              if tm2 ~~ ``aS1 psrV`` then ("vs","vc") else ("","")
  val z = if is_neg tm1 then y else x
  val jump_length = if forward then jump_length + 4 else 0 - jump_length
  in (arm_mk_jump z jump_length,4) end

val arm_spec = cache (arm_prove_specs "auto");
val arm_spec_m = cache (arm_prove_specs "aM");
val arm_spec_m1 = cache (arm_prove_specs "aM1");
val arm_spec_mem = cache (arm_prove_specs "aMEM");
val arm_spec_byte_memory = cache (arm_prove_specs "aBYTE_MEMORY");

val arm_tools = (arm_spec, arm_jump, arm_status, arm_pc);
val arm_tools_no_status = (arm_spec, arm_jump, TRUTH, arm_pc);
val arm_tools_mem = (arm_spec_mem, arm_jump, arm_status, arm_pc);
val arm_tools_byte = (arm_spec_byte_memory, arm_jump, arm_status, arm_pc);


(*

  val m_pred = "auto"
  fun enc s = let val _ = print ("\n\n"^s^"\n\n") in arm_enc s end

  val thms = arm_spec (enc "TST r5, #3");
  val thms = arm_spec (enc "ADD r1, #10");
  val thms = arm_spec (enc "CMP r1, #10");
  val thms = arm_spec (enc "TST r2, #6");
  val thms = arm_spec (enc "SUBCS r1, r1, #10");
  val thms = arm_spec (enc "MOV r0, #0");
  val thms = arm_spec (enc "CMP r1, #0");
  val thms = arm_spec (enc "ADDNE r0, r0, #1");
  val thms = arm_spec (enc "LDRNE r1, [r1]");
  val thms = arm_spec (enc "BNE -#12");
  val thms = arm_spec (enc "MOVGT r2, #5");
  val thms = arm_spec (enc "LDRBNE r2, [r3]");
  val thms = arm_spec (enc "BNE +#420");
  val thms = arm_spec (enc "LDRLS r2, [r11, #-40]");
  val thms = arm_spec (enc "SUBLS r2, r2, #1");
  val thms = arm_spec (enc "SUBLS r11, r11, #4");
  val thms = arm_spec (enc "MOVGT r12, r0");
  val thms = arm_spec (enc "ADD r0, pc, #16");
  val thms = arm_spec (enc "SUB r0, pc, #60");
  val thms = arm_spec (enc "SUBLS r2, r2, #1");
  val thms = arm_spec (enc "SUBLS r11, r11, #4");
  val thms = arm_spec (enc "LDRGT r0, [r11, #-44]");
  val thms = arm_spec (enc "MOVGT r1, r3");
  val thms = arm_spec (enc "MOVGT r12, r5");
  val thms = arm_spec (enc "MOVGT r1, r6");
  val thms = arm_spec (enc "MOVGT r0, r6");
  val thms = arm_spec (enc "ADD r5, pc, #4096");
  val thms = arm_spec (enc "ADD r6, pc, #4096");
  val thms = arm_spec (enc "STRB r2, [r3]");
  val thms = arm_spec (enc "STMIA r4, {r5-r10}");
  val thms = arm_spec (enc "LDMIA r4, {r5-r10}");
  val thms = arm_spec (enc "STRB r2, [r1], #1");
  val thms = arm_spec (enc "STRB r3, [r1], #1");
  val thms = arm_spec (enc "STMIB r8!, {r14}");
  val thms = arm_spec (enc "STMIB r8!, {r0, r14}");
  val thms = arm_spec (enc "LDR pc, [r8]");
  val thms = arm_spec (enc "LDRLS pc, [r8], #-4");
  val thms = arm_spec (enc "LDMIA sp!, {r0-r2, r15}");
  val thms = arm_spec (enc "LDR r0, [pc, #308]");
  val thms = arm_spec (enc "LDR r0, [pc, #4056]");
  val thms = arm_spec (enc "LDR r8, [pc, #3988]");
  val thms = arm_spec (enc "LDR r2, [pc, #3984]");
  val thms = arm_spec (enc "LDR r12, [pc, #3880]");
  val thms = arm_spec (enc "LDR r12, [pc, #3856]");
  val thms = arm_spec (enc "LDR r1, [pc, #1020]");
  val thms = arm_spec (enc "LDR r1, [pc, #-20]");
  val thms = arm_spec (enc "STMDB sp!, {r0-r2, r15}");
  val thms = arm_spec (enc "LDRB r2, [r3]");
  val thms = arm_spec (enc "STRB r2, [r3]");
  val thms = arm_spec (enc "SWPB r2, r4, [r3]");
  val thms = arm_spec (enc "LDR r2, [r3,#12]");
  val thms = arm_spec (enc "STR r2, [r3,#12]");
  val thms = arm_spec (enc "SWP r2, r4, [r3]");
  val thms = arm_spec (enc "LDMIB r4, {r5-r7}");
  val thms = arm_spec (enc "STMIA r4, {r5-r6}");
  val thms = arm_spec (enc "LDRH r2, [r3]");
  val thms = arm_spec (enc "STRH r2, [r3]");
  val thms = arm_spec (enc "MSR CPSR, r1");
  val thms = arm_spec (enc "MSR CPSR, #219");
  val thms = arm_spec (enc "MRS r1, CPSR");
  val thms = arm_spec (enc "LDR r0, [r11, #-8]");
  val thms = arm_spec (enc "LDR r0, [r11]");
  val thms = arm_spec (enc "STR r0, [r11, #-8]");
  val thms = arm_spec (enc "BX lr");

  val m_pred = "aMEM";
  val thms = arm_spec_mem (enc "SWP r0, r1, [r11]");
  val thms = arm_spec_mem (enc "LDR r0, [r11]");
  val thms = arm_spec_mem (enc "LDRB r0, [r11]");
  val thms = arm_spec_mem (enc "STRB r0, [r11]");
  val thms = arm_spec_mem (enc "STR r0, [r11]");
  val thms = arm_spec_mem (enc "STR r0, [r11,#8]");
  val thms = arm_spec_mem (enc "LDR r0, [r11,#8]");
  val thms = arm_spec_mem (enc "STR r0, [r11,#-8]");
  val thms = arm_spec_mem (enc "LDR r0, [r11,#-8]");
  val thms = arm_spec_mem (enc "LDMDB r0, {r2-r4}");
  val thms = arm_spec_mem (enc "STMDB r0, {r2-r4}");
  val thms = arm_spec_mem (enc "LDR r0, [sp,#8]");
  val thms = arm_spec_mem (enc "PUSH {r0-r2}");
  val thms = arm_spec_mem (enc "POP {r0-r2}");
  val thms = arm_spec_mem (enc "POP {r0-r2,pc}");
  val thms = arm_spec_mem (enc "POP {r4,pc}");
  val thms = arm_spec_mem (enc "BLNE -#40");
  val thms = arm_spec_mem (enc "LDRLS pc,[pc,r3,lsl #2]");
  val thms = arm_spec_mem "15832014"

  val thms = arm_spec_m (enc "POP {r4,pc}");
  val thms = arm_spec_m (enc "STM r0, {r2-r3}");

*)

end
