structure ppc_Lib :> ppc_Lib =
struct

open HolKernel boolLib bossLib;
open wordsLib stringLib listSyntax simpLib listTheory wordsTheory;
open opmonTheory bit_listTheory combinTheory;

open ppc_Theory ppc_seq_monadTheory ppc_opsemTheory ppc_astTheory ppc_coretypesTheory;


(* decoder *)

fun ppc_decode s = let
  val tm = Parse.Term [QUOTE ("w2bits (0x"^s^"w:word32)")]
  val bits = (snd o dest_eq o concl o EVAL) tm
  val th = EVAL (mk_comb(``ppc_decode``,bits))
  in th end;

fun ppc_decode_next s = let
  fun fill s = if length (explode s) < 8 then fill ("0" ^ s) else s
  val s = fill s
  val th = ppc_decode s
  val th = MATCH_MP PPC_NEXT_THM th
  val th = Q.SPEC [QUOTE ("(0x"^(substring(s,0,2))^"w:word8)")] th
  val th = Q.SPEC [QUOTE ("(0x"^(substring(s,2,2))^"w:word8)")] th
  val th = Q.SPEC [QUOTE ("(0x"^(substring(s,4,2))^"w:word8)")] th
  val th = Q.SPEC [QUOTE ("(0x"^(substring(s,6,2))^"w:word8)")] th
  val th = CONV_RULE (RATOR_CONV EVAL THENC BETA_CONV) th
  in th end;


(* one step symbolic simulation *)

val else_none_mem_lemma = (UNDISCH o SPEC_ALL) ppc_else_none_mem_lemma
val else_none_status_lemma = (UNDISCH o SPEC_ALL) ppc_else_none_status_lemma
val assertT_lemma = (UNDISCH o SPEC_ALL) ppc_assertT_lemma
val else_none_conv1 = (fst o dest_eq o concl) else_none_mem_lemma
val else_none_conv2 = (fst o dest_eq o concl) else_none_status_lemma
val else_none_conv3 = (fst o dest_eq o concl) assertT_lemma
fun else_none_conv tm = let
  val ((i,t),th) = (match_term else_none_conv1 tm, else_none_mem_lemma) handle HOL_ERR _ =>
                   (match_term else_none_conv2 tm, else_none_status_lemma) handle HOL_ERR _ =>
                   (match_term else_none_conv3 tm, assertT_lemma)
  in INST i (INST_TYPE t th) end;

val w2bytes1 = SIMP_CONV std_ss [Ntimes word2bytes_def 7,ASR_ADD] ``word2bytes 1 (w:word32)``
val w2bytes2 = SIMP_CONV std_ss [Ntimes word2bytes_def 7,ASR_ADD] ``word2bytes 2 (w:word32)``
val w2bytes4 = SIMP_CONV std_ss [Ntimes word2bytes_def 7,ASR_ADD] ``word2bytes 4 (w:word32)``

val lemma1 = REWRITE_RULE [WORD_ADD_0] (Q.SPECL [`v`,`0w`,`x`] WORD_EQ_ADD_LCANCEL)
val lemma2 = REWRITE_RULE [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL)
val address_lemma = prove(
  ``~(0w = 1w:word32) /\ ~(0w = 2w:word32) /\ ~(0w = 3w:word32) /\
    ~(1w = 2w:word32) /\ ~(1w = 3w:word32) /\ ~(2w = 3w:word32)``,EVAL_TAC);

val w_conv = SIMP_CONV std_ss [ppc_write_mem_aux_def,GSYM WORD_ADD_ASSOC, word_add_n2w]
val ppc_write_mem_aux_lemma1 = w_conv ``ppc_write_mem_aux ii addr [x0]``
val ppc_write_mem_aux_lemma2 = w_conv ``ppc_write_mem_aux ii addr [x0;x1]``
val ppc_write_mem_aux_lemma3 = w_conv ``ppc_write_mem_aux ii addr [x0;x1;x2;x3]``

val if_SOME = prove(
  ``(if b then SOME((),x:ppc_state) else SOME((),y)) = SOME ((),if b then x else y)``,
  Cases_on `b` THEN SIMP_TAC std_ss []);

val ss = rewrites [OK_nextinstr_def, PREAD_M_LIST_curried_def,
  PREAD_M_LIST_tupled_primitive_def, PWRITE_M_LIST_def,
  bit_update_def, const_high_def, const_low_def, const_high_s_def,
  const_low_s_def, effective_address_def, goto_label_def,
  gpr_or_zero_def, load_word_def, no_carry_def, ppc_sint_cmp_def,
  ppc_uint_cmp_def, read_bit_word_def, read_ireg_def,
  read_mem_aux_def, reg_load_def, reg_store_def, reg_update_def,
  sint_compare_def, sint_reg_update_def, uint_compare_def,
  uint_reg_update_def, seq_monad_thm, write_reg_def, read_reg_def,
  ppc_write_mem_aux_lemma1, ppc_write_mem_aux_lemma2,
  ppc_write_mem_aux_lemma3, write_mem_def, read_mem_def,
  read_status_def, write_status_def, write_reg_seq_def,
  read_reg_seq_def, write_status_seq_def, constT_def, seqT_def,
  parT_def, parT_unit_def, failureT_def, PREAD_CLAUSES,
  ppc_reg_distinct, ppc_bit_distinct, w2w_def, w2n_n2w, WORD_ADD_0,
  n2w_w2n, w2bytes1, w2bytes2, w2bytes4, n2w_11, address_aligned_def,
  rich_listTheory.REVERSE, WORD_EQ_ADD_LCANCEL,ppc_branch_condition_def,
  rich_listTheory.SNOC_APPEND, APPEND, lemma1, lemma2, address_lemma]

fun EVAL_sw2sw th = let
  val tm = find_term (can (match_term ``(sw2sw:'a word -> 'b word) (n2w n)``)) (concl th)
  in EVAL_sw2sw (REWRITE_RULE [EVAL tm] th) end handle e => th;

fun EVAL_word_and_eq th = let
  val tm = find_term (can (match_term ``(n2w n) && (n2w m) = (n2w k):'a word``)) (concl th)
  in EVAL_word_and_eq (REWRITE_RULE [EVAL tm] th) end handle e => th;

fun ppc_step s = let
  val th = ppc_decode_next s
  val tm = (fst o dest_eq o fst o dest_imp o concl) th
  val th1 = SIMP_CONV (std_ss++ss++wordsLib.SIZES_ss) [ppc_exec_instr_def] tm
  fun cc th = CONV_RULE (ONCE_DEPTH_CONV else_none_conv) th
  fun f th = (DISCH_ALL o CONV_RULE (RAND_CONV (SIMP_CONV std_ss [pull_if_lemma])) o
              UNDISCH_ALL o SIMP_RULE (std_ss++ss) [LET_DEF] o
              DISCH_ALL o cc) th
  fun change f x = let val y = f x in if eq (concl y) (concl x) then x else change f y end
  val th1 = change f th1
  val th1 = EVAL_word_and_eq th1
  val th1 = DISCH_ALL (MATCH_MP th (UNDISCH_ALL (REWRITE_RULE [if_SOME] th1)))
  val th1 = (REWRITE_RULE [pull_if_lemma] o UNDISCH_ALL) th1
  val th1 = REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC,conditional_def] (DISCH_ALL th1)
  val th1 = EVAL_sw2sw th1
  in th1 end;


(*
  test cases:

  val th = ppc_step "7C640194";  (* addze 3,4 *)
  val th = ppc_step "7C221A14";  (* add 1,2,3 *)
  val th = ppc_step "7E6802A6";  (* mflr 19 *)
  val th = ppc_step "7C4903A6";  (* mtctr 2 *)
  val th = ppc_step "7C4803A6";  (* mtlr 2 *)
  val th = ppc_step "7C032040";  (* cmplw 3,4 *)
  val th = ppc_step "28070320";  (* cmplwi 7,800 *)
  val th = ppc_step "7C119000";  (* cmpw 17,18 *)
  val th = ppc_step "2C070258";  (* cmpwi 7,600 *)
  val th = ppc_step "7E7A21D6";  (* mullw 19, 26, 4 *)
  val th = ppc_step "7E7A2010";  (* subfc 19, 26, 4 *)
  val th = ppc_step "38221388";  (* addi 1,2,5000 *)
  val th = ppc_step "3C22FFCE";  (* addis 1,2,-50 *)
  val th = ppc_step "7C812839";  (* and. 1,4,5 *)
  val th = ppc_step "7C812878";  (* andc 1,4,5 *)
  val th = ppc_step "70E60050";  (* andi. 6,7,80 *)
  val th = ppc_step "76300007";  (* andis. 16,17,7 *)
  val th = ppc_step "4C221B82";  (* cror 1,2,3 *)
  val th = ppc_step "7C411A38";  (* eqv 1,2,3 *)
  val th = ppc_step "7E300774";  (* extsb 16,17 *)
  val th = ppc_step "7CA40734";  (* extsh 4,5 *)
  val th = ppc_step "8A7A00EA";  (* lbz 19, 234(26) *)
  val th = ppc_step "7E7A20AE";  (* lbzx 19, 26, 4 *)
  val th = ppc_step "7E7A22AE";  (* lhax 19, 26, 4 *)
  val th = ppc_step "7E7A222E";  (* lhzx 19, 26, 4 *)
  val th = ppc_step "827A00EA";  (* lwz 19, 234(26) *)
  val th = ppc_step "7E7A202E";  (* lwzx 19, 26, 4 *)
  val th = ppc_step "7C5A1378";  (* mr 26, 2 *)
  val th = ppc_step "1E7AFFFE";  (* mulli 19, 26, -2 *)
  val th = ppc_step "7C5A23B8";  (* nand 26, 2, 4 *)
  val th = ppc_step "7C5A20F8";  (* nor 26, 2, 4 *)
  val th = ppc_step "7C5A2378";  (* or 26, 2, 4 *)
  val th = ppc_step "7C5A2338";  (* orc 26, 2, 4 *)
  val th = ppc_step "605A0237";  (* ori 26, 2, 567 *)
  val th = ppc_step "645A0237";  (* oris 26, 2, 567 *)
  val th = ppc_step "7C5A2030";  (* slw 26, 2, 4 *)
  val th = ppc_step "7C5A2630";  (* sraw 26, 2, 4 *)
  val th = ppc_step "7C5A1E70";  (* srawi 26, 2, 3 *)
  val th = ppc_step "7C5A2430";  (* srw 26, 2, 4 *)
  val th = ppc_step "7C5A2278";  (* xor 26, 2, 4 *)
  val th = ppc_step "685A0237";  (* xori 26, 2, 567 *)
  val th = ppc_step "6C5A0237";  (* xoris 26, 2, 567 *)
  val th = ppc_step "227AFFFE";  (* subfic 19, 26, -2 *)
  val th = ppc_step "985A00EA";  (* stb 2, 234(26) *)
  val th = ppc_step "7C44D1AE";  (* stbx 2, 4, 26 *)
  val th = ppc_step "7C5A232E";  (* sthx 2, 26, 4 *)
  val th = ppc_step "905A00EA";  (* stw 2, 234(26) *)
  val th = ppc_step "7C5A212E";  (* stwx 2, 26, 4 *)
  val th = ppc_step "4BFFFFFC";  (* b L1 *)
  val th = ppc_step "4180FFF8";  (* bc 12,0,L1 *)
  val th = ppc_step "4181FFF4";  (* bc 12,1,L1 *)
  val th = ppc_step "4082FFF0";  (* bc 4,2,L1 *)
  val th = ppc_step "4083FFEC";  (* bc 4,3,L1 *)
  val th = ppc_step "7C858396";  (* divwu 4,5,16 *)

  (* these are not modelled *)

  val th = ppc_step "545A188A";  (* rlwinm 26, 2, 3, 2, 5 *)
  val th = ppc_step "7C221BD6";  (* divw 1,2,3 *)

*)

val _ = output_words_as_hex();

fun ppc_test_aux inst input output = let
  val rw = ppc_step inst
  fun format state (i,j) =
    if mem i ["PC","CTR","LR"]
    then ("PREAD_R PPC_"^i^" "^state^" = 0x"^j^"w")
    else if substring(i,0,3) = "GPR"
    then ("PREAD_R (PPC_IR "^substring(i,3,size(i)-3)^"w) "^state^" = 0x"^j^"w")
    else if i = "CARRY"
    then ("PREAD_S PPC_CARRY "^state^" = SOME "^j)
    else if substring(i,0,3) = "CR0"
    then ("PREAD_S (PPC_CR0 "^substring(i,3,size(i)-3)^"w) "^state^" = SOME "^j)
    else ("PREAD_M 0x"^i^"w "^state^" = SOME (0x"^j^"w)")
  fun p y = Parse.Term [QUOTE y]
  fun f s = map (p o format s)
  val th = foldr (fn (x,y) => DISCH x y) rw (f "s" input)
  val th = SIMP_RULE std_ss [ppc_reg_distinct,ppc_reg_11,ppc_bit_distinct,ppc_bit_11] th
  val th = SIMP_RULE std_ss [word_add_n2w,WORD_ADD_0,b2w_def,bits2num_def,GSYM AND_IMP_INTRO] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_n2w,word_mul_n2w,word_add_n2w,word_sub_def,word_2comp_n2w] th
  val th = SIMP_RULE (std_ss++ss++SIZES_ss) [n2w_11] th
  fun find_and_delete_cond th = let
    val tm = find_term (can (match_term ``n2w n && (n2w m):word32 = n2w k``)) (concl th)
    in REWRITE_RULE [prove(tm,EVAL_TAC)] th end
  val th = repeat find_and_delete_cond th
  val th = REWRITE_RULE [AND_IMP_INTRO] th
  val th = REWRITE_RULE [GSYM CONJ_ASSOC] th
  val xs = find_terms (can (match_term ``PWRITE_S x NONE``)) (concl th)
  val xs = map (snd o dest_comb o fst o dest_comb) xs
  val output1 = f "(THE (PPC_NEXT s))" output
  val output2 = Lib.zip (map (snd o dest_comb o fst o dest_comb o fst o dest_eq) output1) output1
  val output3 = filter (fn (x,y) => not (op_mem eq x xs)) output2
  val tm = list_mk_conj (map snd output3)
  val tm2 = (hd o hyp o UNDISCH) th
  val goal = mk_imp(tm2,tm)
(*
  set_goal([],goal)
*)
  val result = prove(goal,
    STRIP_TAC
    THEN (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO]) th
    THEN ASM_SIMP_TAC std_ss [PREAD_CLAUSES,optionTheory.THE_DEF,ppc_reg_distinct,ppc_reg_11,ppc_bit_distinct,ppc_bit_11]
    THEN EVAL_TAC)
  val result = REWRITE_RULE [GSYM AND_IMP_INTRO] result
  in result end;

fun ppc_test inst input output = let
  fun p s = if length (explode s) < 6 then s else "["^s^"]"
  val _ = print ("\nTesting:\n  instruction = "^inst^"\n")
  val _ = print ("Input:\n")
  val _ = map (fn (x,y) => print ("  "^(p x)^" = "^y^"\n")) input
  val _ = print ("Output:\n")
  val _ = map (fn (x,y) => print ("  "^(p x)^" = "^y^"\n")) output
  val _ = print ("Result:\n")
  val th = SOME (ppc_test_aux inst input output) handle e => NONE
  in case th of
      NONE => (print "  Test failed.\n"; TRUTH)
    | SOME th => (print "  Test successful.\n\n"; print_thm th; print "\n\n"; th)
  end;


end
