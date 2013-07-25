structure x64_decompLib :> x64_decompLib =
struct

open HolKernel Parse boolLib bossLib;
open helperLib set_sepTheory addressTheory progTheory wordsTheory wordsLib;
open pred_setTheory combinTheory x64_progTheory x64_prog_extraTheory listTheory;

structure Parse =
struct
   open Parse
   val (Type, Term) =
      parse_from_grammars x64_prog_extraTheory.x64_prog_extra_grammars
end

open Parse

local
  val pat = ``x64_REG r v``
  fun lowercase s = let
    fun f c = if #"A" <= c andalso c <= #"Z"
              then implode [chr (ord c + 32)]
              else implode [c]
    in String.translate f s end
in
  fun rename_vars th = let
    val (_,p,_,_) = th |> concl |> dest_spec
    val ps = list_dest dest_star p
    val ps = filter (fn tm => is_var (rand tm) andalso
                              is_const (rand (rator tm))
                              handle HOL_ERR _ => false) ps
    fun new_name r =
      rand r |->
      mk_var(r |> rator |> rand |> dest_const |> fst |> lowercase, type_of (rand r))
    in INST (map new_name ps) th end
end

fun try_to_remove_mem32 th = let
  val (_,p,_,q) = th |> concl |> dest_spec
  val i = match_term ``pp * x64_mem32 a w`` p |> fst
  val th = INST [subst i ``w:word32``|->``(w2w:word64 -> word32) w``] th
  val th = MATCH_MP x64_mem32_READ_EXTEND th handle HOL_ERR _ =>
           MATCH_MP x64_mem32_WRITE_EXTEND th
  in th end handle HOL_ERR _ => th;

val SING_SUBSET = prove(
  ``{x:'a} SUBSET s = x IN s``,
  SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]);

fun introduce_MEMORY th = if
  not (can (find_term (can (match_term ``x64_mem64``))) (concl th))
  then th else let
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val (_,p,_,q) = dest_spec(concl th)
  val xs = (rev o list_dest dest_star) p
  val tm = ``x64_mem64 a x``
  val xs = filter (can (match_term tm)) xs
  fun foo tm = cdr tm |->
               mk_comb(mk_var("m",``:word64->word64``),(cdr o car) tm)
  val th = INST (map foo xs) th
  in if length xs = 0 then th else let
    val (_,p,_,q) = dest_spec(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = ``x64_mem64 a x``
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o car) xs)
    fun foo [] = mk_var("dm",``:word64 set``)
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``x64_MEMORY``,foo ys),mk_var("m",``:word64->word64``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
    val th = RW [GSYM STAR_ASSOC] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) x64_MEMORY_INSERT
    fun compact th = let
      val x = find_term (can (match_term fff)) ((car o car o concl o UNDISCH_ALL) th)
      val rw = (INST (fst (match_term fff x)) o SPEC_ALL o DISCH_ALL o UNDISCH) x64_MEMORY_INSERT
      val th = DISCH ((fst o dest_imp o concl) rw) th
      val th = SIMP_RULE bool_ss [x64_MEMORY_INSERT] th
      in th end
    val th = repeat compact th
    val th = RW [STAR_ASSOC,AND_IMP_INTRO,GSYM CONJ_ASSOC] th
    val th = RW [APPLY_UPDATE_ID] th
    val v = hd (filter (is_var) ys @ ys)
    fun ss [] = ``{}:word64 set``
      | ss (v::vs) = pred_setSyntax.mk_insert(v,ss vs)
    val u1 = pred_setSyntax.mk_subset(ss (rev ys),mk_var("dm",``:word64 set``))
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

fun introduce_BYTE_MEMORY th = if
  not (can (find_term (can (match_term ``x64_MEM``))) (concl th))
  then th else let
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val (_,p,_,q) = dest_spec(concl th)
  val xs = (rev o list_dest dest_star) p
  val tm = ``x64_MEM a x``
  val xs = filter (can (match_term tm)) xs
  fun PRE_POST_CONV c = PRE_CONV c THENC POST_CONV c
  fun LIST_MOVE_OUT_CONV [] = ALL_CONV
    | LIST_MOVE_OUT_CONV (c::cs) =
        MOVE_OUT_CONV (rator c) THENC LIST_MOVE_OUT_CONV cs
  val th = CONV_RULE (PRE_POST_CONV (LIST_MOVE_OUT_CONV xs)) th
  fun foo tm = cdr (cdr tm) |->
               mk_comb(mk_var("b",``:word64->word8``),(cdr o car) tm)
  val th = INST (map foo xs) th
  in if length xs = 0 then th else let
    val (_,p,_,q) = dest_spec(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = ``x64_MEM a x``
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o car) xs)
    fun foo [] = mk_var("db",``:word64 set``)
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``x64_BYTE_MEMORY``,foo ys),mk_var("b",``:word64->word8``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
    val th = RW [GSYM STAR_ASSOC] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) x64_BYTE_MEMORY_INSERT
    fun compact th = let
      val x = find_term (can (match_term fff)) ((car o car o concl o UNDISCH_ALL) th)
      val rw = (INST (fst (match_term fff x)) o SPEC_ALL o DISCH_ALL o UNDISCH) x64_BYTE_MEMORY_INSERT
      val th = DISCH ((fst o dest_imp o concl) rw) th
      val th = SIMP_RULE bool_ss [x64_BYTE_MEMORY_INSERT] th
      in th end
    val th = repeat compact th
    val th = RW [STAR_ASSOC,AND_IMP_INTRO,GSYM CONJ_ASSOC] th
    val th = RW [APPLY_UPDATE_ID] th
    val v = hd (filter (is_var) ys @ ys)
    fun ss [] = ``{}:word64 set``
      | ss (v::vs) = pred_setSyntax.mk_insert(v,ss vs)
    val u1 = pred_setSyntax.mk_subset(ss (rev ys),mk_var("db",``:word64 set``))
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

local
  val rw = REWRITE_RULE [GSYM x64_PC_def,GSYM L3_X64_MODEL_def]
           o Q.INST [`rip`|->`p`]
in
  fun x64_triple hex = let
    val th = x64_progLib.x64_spec hex |> rw
    val th = try_to_remove_mem32 th
    val th = rename_vars th
    val th = introduce_MEMORY th
    val th = introduce_BYTE_MEMORY th
    in th end
end


local
  val pat_pc = ``x64_PC p``
  val pat = ``x64_PC (if b then x else y)``
  val lemma1 = prove(``b ==> (x64_PC (if b then x else y) = x64_PC x)``,
                     SIMP_TAC std_ss []);
  val lemma2 = prove(``~b ==> (x64_PC (if b then x else y) = x64_PC y)``,
                     SIMP_TAC std_ss []);
  val lemma3 = SPEC_MOVE_COND |> GSYM |> REWRITE_RULE [GSYM precond_def]
  fun get_length th = let
    val (_,_,c,_) = th |> concl |> dest_spec
    in c |> rator |> rand |> rand |> listSyntax.dest_list |> fst |> length end
  fun find_exit th = let
    val (_,_,_,q) = th |> concl |> dest_spec
    val pc = first (can (match_term pat_pc)) (list_dest dest_star q) |> rand
    in if can (match_term ``(p:word64) + n2w n``) pc then
         SOME (pc |> rand |> rand |> numLib.int_of_term)
       else if can (match_term ``(p:word64) - n2w n``) pc then
         SOME (0 - (pc |> rand |> rand |> numLib.int_of_term))
       else if pc = mk_var("p",``:word64``) then
         SOME 0
       else NONE end
  fun finalise th = (th, get_length th, find_exit th)
in
  fun x64_triples hex = let
    val th = x64_triple hex
    val (th1,th2) = let
      val pc = find_term (can (match_term pat)) (concl th)
      val m = fst (match_term pat pc)
      val l1 = lemma1 |> INST m |> UNDISCH
      val l2 = lemma2 |> INST m |> UNDISCH
      fun fix l th = let
        val th = REWRITE_RULE [l] th
        val th = DISCH_ALL th
        val th = SIMP_RULE (std_ss++WORD_SUB_ss) [lemma3,word_arith_lemma1,
                   word_arith_lemma3,word_arith_lemma4] th
        in finalise th end
      in (fix l1 th, SOME (fix l2 th)) end
      handle HOL_ERR _ => let
        val th = SIMP_RULE (std_ss++WORD_SUB_ss) [lemma3,word_arith_lemma1,
                   word_arith_lemma3,word_arith_lemma4] th
        in (finalise th,NONE) end
  in (th1,th2) end
end

val (x64_tools:decompiler_tools) =
  (x64_triples,(fn t => fail()),x64_ALL_EFLAGS_def,``x64_PC``)

val x64_decompile = decompilerLib.decompile x64_tools

(*

  val hex = "55"; x64_triples hex;
  val hex = "4889E5"; x64_triples hex;
  val hex = "48897DE8"; x64_triples hex;
  val hex = "8975E4"; x64_triples hex;
  val hex = "C745F800000000"; x64_triples hex;
  val hex = "EB3B"; x64_triples hex;
  val hex = "8B45F8"; x64_triples hex;
  val hex = "4863D0"; x64_triples hex;
  val hex = "488B45E8"; x64_triples hex;
  val hex = "4801D0"; x64_triples hex;
  val hex = "0FB600"; x64_triples hex;
  val hex = "0FBEC0"; x64_triples hex;
  val hex = "8945FC"; x64_triples hex;
  val hex = "837DFC60"; x64_triples hex;
  val hex = "7E1B"; x64_triples hex;
  val hex = "837DFC7A"; x64_triples hex;
  val hex = "7F15"; x64_triples hex;
  val hex = "8B45F8"; x64_triples hex;
  val hex = "4863D0"; x64_triples hex;
  val hex = "488B45E8"; x64_triples hex;
  val hex = "4801C2"; x64_triples hex;
  val hex = "8B45FC"; x64_triples hex;
  val hex = "83E820"; x64_triples hex;

  val hex = "8802"; x64_triples hex;

  val hex = "8345F801"; x64_triples hex;
  val hex = "8B45F8"; x64_triples hex;
  val hex = "3B45E4"; x64_triples hex;
  val hex = "7CBD"; x64_triples hex;
  val hex = "5D"; x64_triples hex;

*)

end
