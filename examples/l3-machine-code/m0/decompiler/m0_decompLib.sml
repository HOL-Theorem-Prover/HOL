structure m0_decompLib = struct

open HolKernel Parse boolLib bossLib;
open helperLib set_sepTheory addressTheory progTheory wordsTheory wordsLib;
open pred_setTheory combinTheory m0_progTheory m0_decompTheory listTheory;

val SING_SUBSET = prove(
  ``{x:'a} SUBSET s = x IN s``,
  SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]);

fun PRE_POST_CONV c = PRE_CONV c THENC POST_CONV c
fun LIST_MOVE_OUT_CONV [] = ALL_CONV
  | LIST_MOVE_OUT_CONV (c::cs) =
      MOVE_OUT_CONV (rator c) THENC LIST_MOVE_OUT_CONV cs

fun introduce_MEMORY th = if
  not (can (find_term (can (match_term ``m0_MEM``))) (concl th))
  then th else let
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
  val th = CONV_RULE (PRE_CONV STAR_REVERSE_CONV) th
  val (_,p,_,q) = dest_spec(concl th)
  val xs = (rev o list_dest dest_star) p
  val tm = ``m0_MEM a x``
  val xs = filter (can (match_term tm)) xs
  val th = CONV_RULE (PRE_POST_CONV (LIST_MOVE_OUT_CONV xs)) th
  fun foo tm = cdr tm |->
               mk_comb(mk_var("m",``:word32->word8``),(cdr o car) tm)
  val th = INST (map foo xs) th
  in if length xs = 0 then th else let
    val (_,p,_,q) = dest_spec(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = ``m0_MEM a x``
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o car) xs)
    fun foo [] = mk_var("dm",``:word32 set``)
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``m0_MEMORY``,foo ys),mk_var("m",``:word32->word8``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
    val th = RW [GSYM STAR_ASSOC] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) m0_MEMORY_INSERT
    fun compact th = let
      val x = find_term (can (match_term fff)) ((car o car o concl o UNDISCH_ALL) th)
      val rw = (INST (fst (match_term fff x)) o SPEC_ALL o
                        DISCH_ALL o UNDISCH) m0_MEMORY_INSERT
      val th = DISCH ((fst o dest_imp o concl) rw) th
      val th = SIMP_RULE bool_ss [m0_MEMORY_INSERT] th
      in th end
    val th = repeat compact th
    val th = RW [STAR_ASSOC,AND_IMP_INTRO,GSYM CONJ_ASSOC] th
    val th = RW [APPLY_UPDATE_ID] th
    val v = hd (filter (is_var) ys @ ys)
    fun ss [] = ``{}:word32 set``
      | ss (v::vs) = pred_setSyntax.mk_insert(v,ss vs)
    val u1 = pred_setSyntax.mk_subset(ss (rev ys),mk_var("dm",``:word32 set``))
    val u3 = (fst o dest_imp o concl) th
    val u2 = list_mk_conj (u1::filter is_eq (list_dest dest_conj u3))
    val goal = mk_imp(u2,u3)
    val imp = prove(goal,
      ONCE_REWRITE_TAC [ALIGNED_MOD_4]
      THEN SIMP_TAC std_ss [word_arith_lemma1,word_arith_lemma3,word_arith_lemma4]
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
  val xs = [``m0_exception x``,``m0_CONTROL_SPSEL x``,
            ``m0_AIRCR x``,``m0_REG RName_PC x``]
  val assum1 = ``~aircr.ENDIANNESS``
  val assum2 = ``Aligned (pc:word32,2)``
  val ss = SIMP_RULE std_ss [Aligned_2_SIMP,SEP_CLAUSES]
  fun fill tm th =
    if can (find_term (fn t => aconv t tm)) (concl th) then th else
      SPEC_FRAME_RULE th tm
in
  fun introduce_PC th = let
    val th = fill ``m0_CONTROL_SPSEL F`` th
    val th = CONV_RULE (PRE_POST_CONV (LIST_MOVE_OUT_CONV xs)) th
    val th = REWRITE_RULE [ASSUME assum1,ASSUME assum2] th
    val th = th |> DISCH assum2 |> DISCH assum1
    val th = PURE_REWRITE_RULE [AND_IMP_INTRO] th
    val th = MATCH_MP m0_PC_INTRO (Q.GEN `aircr` th)
    val th = ss th
    in th end
end

local
  val pat_pc = ``m0_PC p``
  fun get_length th = let
    val (_,_,c,_) = th |> concl |> dest_spec
    in if can (find_term (can (match_term sumSyntax.inl_tm))) c then 2 else 4 end
  fun find_exit th = let
    val (_,_,_,q) = th |> concl |> dest_spec
    val pc = first (can (match_term pat_pc)) (list_dest dest_star q) |> rand
    in if can (match_term ``(p:word32) + n2w n``) pc then
         SOME (pc |> rand |> rand |> numLib.int_of_term)
       else if can (match_term ``(p:word32) - n2w n``) pc then
         SOME (0 - (pc |> rand |> rand |> numLib.int_of_term))
       else if pc = mk_var("p",``:word32``) then
         SOME 0
       else NONE end
  fun finalise th = (th, get_length th, find_exit th)
  fun finalise' th = finalise (REWRITE_RULE [GSYM precond_def] th)
  val rw = CONV_RULE (RAND_CONV (SIMP_CONV (std_ss++WORD_SUB_ss) [])) o
           SIMP_RULE std_ss [GSYM arithmeticTheory.ADD_ASSOC,
             word_arith_lemma3,word_arith_lemma4,word_arith_lemma1] o
           introduce_MEMORY o introduce_PC
in
  fun m0_triples hex = let
    val ths = m0_progLib.m0_spec_hex hex |> map rw
    in if length ths < 2 then (finalise (hd ths), NONE)
       else (finalise' (hd ths), SOME (finalise (hd (tl ths)))) end
end

val (m0_tools:decompiler_tools) =
  (m0_triples,(fn t => fail()),m0_NZCV_def,``m0_PC``)

val m0_decompile = decompilerLib.decompile m0_tools

(*

map m0_triples
  ["b510", "680b", "2b00", "d003", "681a", "6804", "42a2", "db02",
   "6043", "6008", "bd10", "1d19", "e7f3"]

00000000 <insert>:
   0:   b510            push    {r4, lr}
   2:   680b            ldr     r3, [r1, #0]
   4:   2b00            cmp     r3, #0
   6:   d003            beq.n   10 <insert+0x10>
   8:   681a            ldr     r2, [r3, #0]
   a:   6804            ldr     r4, [r0, #0]
   c:   42a2            cmp     r2, r4
   e:   db02            blt.n   16 <insert+0x16>
  10:   6043            str     r3, [r0, #4]
  12:   6008            str     r0, [r1, #0]
  14:   bd10            pop     {r4, pc}
  16:   1d19            adds    r1, r3, #4
  18:   e7f3            b.n     2 <insert+0x2>

0000001a <sort>:
  1a:   b537            push    {r0, r1, r2, r4, r5, lr}
  1c:   1c04            adds    r4, r0, #0
  1e:   2200            movs    r2, #0
  20:   6800            ldr     r0, [r0, #0]
  22:   9201            str     r2, [sp, #4]
  24:   2800            cmp     r0, #0
  26:   d005            beq.n   34 <sort+0x1a>
  28:   6845            ldr     r5, [r0, #4]
  2a:   a901            add     r1, sp, #4
  2c:   f7ff fffe       bl      0 <insert>
  30:   1c28            adds    r0, r5, #0
  32:   e7f7            b.n     24 <sort+0xa>
  34:   9b01            ldr     r3, [sp, #4]
  36:   6023            str     r3, [r4, #0]
  38:   bd37            pop     {r0, r1, r2, r4, r5, pc}

map m0_triples ["bd10","f7ffff4e"]

*)

end
