structure ppcLib :> ppcLib =
struct
 
open HolKernel boolLib bossLib;
open wordsLib stringLib listSyntax simpLib listTheory wordsTheory;
open opmonTheory bit_listTheory combinTheory;

open ppcTheory;


(* decoder *)

fun ppc_decode s = let
  val tm = subst [``s:string``|->fromMLstring s]
             ``ppc_decode (w2bits ((b2w I (hex2bits s)):word32))``
  val th = EVAL tm
  val _  = computeLib.add_funs [th]
  in MATCH_MP PPC_NEXT_THM th end;


(* one step symbolic simulation *)

fun tac g = prove(g, Cases THEN SIMP_TAC std_ss []);

val if_some_lemma = tac
  ``!b x y:'a. (if b then SOME x else SOME y) = SOME (if b then x else y)``;
val pull_if_lemma = tac
  ``!b x y (f:'a->'b). f (if b then x else y) = if b then f x else f y``;
val else_none_lemma = (UNDISCH o SPEC_ALL o tac) 
  ``!b. b ==> ((if b then x:'a option else NONE) = x)``;

val ss = rewrites [OK_nextinstr_def, LOCAL_def, reg_store_def,
  push_eaddress_def, read_reg_def, const_low_def, const_high_def,
  opt_thm, option_then_assoc, sint_compare_def, PREAD_R_def,
  PREAD_S_def, PREAD_M_def, write_mem_def, mem_access_ok_def,
  word2bytes_thm, SIMP_RULE std_ss [LET_DEF] PWRITE_MDATA_def,
  mem_read_bytes_thm, read_mem_def, listTheory.REVERSE_REV,
  listTheory.REV_DEF, PWRITE_M_LIST_def, PWRITE_M_def, pc_inc_def,
  read_pc_def, read_lr_def, read_ctr_def, set_pc_def, set_lr_def,
  set_ctr_def, opt_s_pop_def, PWRITE_R_def, address_aligned_def,
  EVERY_DEF, option_parallel_def, reg_load_def, reg_update_def,
  APPLY_UPDATE_THM, ppc_reg_distinct, LET_DEF, no_carry_def,
  PWRITE_S_def, PREAD_MDATA_def, MAP, listTheory.REV_DEF,
  reg_write_def, uint_compare_def, PPC_UINT_CMP_def, PPC_SINT_CMP_def,
  if_some_lemma, ppc_exec_instr_def, read_bit_word_def, read_bit_def,
  sint_reg_update_def, uint_reg_update_def, bit_update_def,
  gpr_or_zero_def, n2w_11, goto_label_def, opt_cond_def];

val else_none_conv = 
  let val tm1 = (fst o dest_eq o concl) else_none_lemma in 
    fn tm => (let val (i,t) = match_term tm1 tm
              in INST i (INST_TYPE t else_none_lemma) end) end;

fun ppc_step s = let
  val _ = print (" decoding")
  val th = ppc_decode s;
  val _ = print (", executing")
  val tm = (fst o dest_eq o fst o dest_imp o concl) th
  val th1 = SIMP_CONV (std_ss++ss++wordsLib.SIZES_ss) [] tm;
  fun cc th = CONV_RULE (ONCE_DEPTH_CONV else_none_conv) th handle e => th
  val th1 = SIMP_RULE std_ss [WORD_OR_IDEM, LET_DEF] (DISCH_ALL (cc th1))
  val th1 = SIMP_RULE std_ss [WORD_OR_IDEM, LET_DEF] (DISCH_ALL (cc th1))
  val th1 = SIMP_RULE std_ss [WORD_OR_IDEM, LET_DEF] (DISCH_ALL (cc th1))
  val th1 = SIMP_RULE std_ss [WORD_OR_IDEM, LET_DEF] (DISCH_ALL (cc th1))
  val th1 = DISCH_ALL (MATCH_MP th (UNDISCH_ALL th1))
  val th1 = SIMP_RULE bool_ss [pull_if_lemma, pairTheory.SND] th1
  in REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] (DISCH_ALL th1) end;

(*
  test cases:

  val th = ppc_step "7C221A14";  (* add 1,2,3 *)
  val th = ppc_step "7C640194";  (* addze 3,4 *)
  val th = ppc_step "7E6802A6";  (* mflr 19 *)
  val th = ppc_step "7C4903A6";  (* mtctr 2 *)
  val th = ppc_step "7C4803A6";  (* mtlr 2 *)
  val th = ppc_step "7C032040";  (* cmplw 3,4 *)
  val th = ppc_step "28070320";  (* cmplwi 7,800 *)
  val th = ppc_step "7C119000";  (* cmpw 17,18 *)
  val th = ppc_step "2C070258";  (* cmpwi 7,600 *)
  val th = ppc_step "7E7A21D6";  (* mullw 19, 26, 4 *)
  val th = ppc_step "7E7A2010";  (* subfc 19, 26, 4 *)
  val th = ppc_step "7C221BD6";  (* divw 1,2,3 *)
  val th = ppc_step "7C858396";  (* divwu 4,5,16 *)
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
  val th = ppc_step "545A188A";  (* rlwinm 26, 2, 3, 2, 5 *)
  val th = ppc_step "7C5A2030";  (* slw 26, 2, 4 *)
  val th = ppc_step "7C5A2630";  (* sraw 26, 2, 4 *)
  val th = ppc_step "7C5A1E70";  (* srawi 26, 2, 3 *)
  val th = ppc_step "7C5A2430";  (* srw 26, 2, 4 *)
  val th = ppc_step "985A00EA";  (* stb 2, 234(26) *)
  val th = ppc_step "7C44D1AE";  (* stbx 2, 4, 26 *)
  val th = ppc_step "7C5A232E";  (* sthx 2, 26, 4 *)
  val th = ppc_step "905A00EA";  (* stw 2, 234(26) *)
  val th = ppc_step "7C5A212E";  (* stwx 2, 26, 4 *)
  val th = ppc_step "227AFFFE";  (* subfic 19, 26, -2 *)
  val th = ppc_step "7C5A2278";  (* xor 26, 2, 4 *)
  val th = ppc_step "685A0237";  (* xori 26, 2, 567 *)
  val th = ppc_step "6C5A0237";  (* xoris 26, 2, 567 *)
  val th = ppc_step "4BFFFFFC";  (* b L1 *)
  val th = ppc_step "4180FFF8";  (* bc 12,0,L1 *)
  val th = ppc_step "4181FFF4";  (* bc 12,1,L1 *)
  val th = ppc_step "4082FFF0";  (* bc 4,2,L1 *)
  val th = ppc_step "4083FFEC";  (* bc 4,3,L1 *)

*)

end
