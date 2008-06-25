structure armLib :> armLib =
struct
 
open HolKernel boolLib bossLib;
open wordsLib stringLib listSyntax simpLib listTheory wordsTheory combinTheory;

open arm_rulesTheory arm_evalTheory armTheory arm_auxTheory;


(* decoder *)

fun arm_decode s = let
  val tm = instructionSyntax.decode_instruction_hex s
  in (tm, EVAL (mk_comb(``enc``,tm))) end;
 

(* one step symbolic simulation *)

val arm_rule_thms = map (fst o snd) (DB.match ["arm_rules"] ``enc (xxx)``)

fun conv_term_ss conv tm_name tm = simpLib.conv_ss
  { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K conv) };

val eval_term_ss = conv_term_ss EVAL;

val am1_ss = eval_term_ss "addr_mode1_encode" ``((11 >< 0) (addr_mode1_encode x)):'a word``
val am2_ss = eval_term_ss "addr_mode2_encode" ``((11 >< 0) (addr_mode2_encode x)):'a word``
val n2w_select_ss = eval_term_ss "n2w_select" ``((n2w n):'a word) ' i``
val n2w_extract_ss = eval_term_ss "n2w_extract" ``((k >< l) ((n2w n):'a word)):'b word``
val reg_list_ss = eval_term_ss "reg_list" ``REGISTER_LIST (n2w n)``

fun GENLIST_CONV tm = let
  val (y,z) = dest_comb tm  
  val (x,y) = dest_comb y  
  val _ = if numSyntax.is_numeral z then () else hd []
  val v = genvar(type_of y)
  in INST [v|->y] (EVAL (mk_comb(mk_comb(x,v),z))) end handle e => ALL_CONV tm;

val genlist_ss = conv_term_ss GENLIST_CONV "genlist" ``GENLIST (f:num->'b) x``;

val arm_ss = srw_ss() ++ genlist_ss ++ am1_ss ++ am2_ss ++
  n2w_select_ss ++ n2w_extract_ss ++ wordsLib.SIZES_ss ++ reg_list_ss
  ++ rewrites [IS_DP_IMMEDIATE_def,n2w_11, IS_DTH_IMMEDIATE_def,
  SHIFT_IMMEDIATE2_THM, LSL_def, ROR_def, LSR_def, LET_DEF,
  IS_DT_SHIFT_IMMEDIATE_def, systemTheory.MEM_WRITE_WORD_def,
  SHIFT_IMMEDIATE_def, IS_MSR_IMMEDIATE_def, IMMEDIATE_def,
  ADDR_MODE1_def, ADDR_MODE2_def, ADDR_MODE3_def, ADDRESS_LIST_def,
  GSYM ARM_MODE_def, GSYM ARM_WRITE_REG_def,ARM_READ_REG_INTRO,
  ADDR_MODE4_def, UP_DOWN_def, WB_ADDRESS_def, FIRST_ADDRESS_def, ZIP,
  NZCV_def, GSYM ARM_READ_MEM_def, GSYM ARM_READ_STATUS_def,
  CONDITION_PASSED2_def, ARM_WRITE_REG_PC_INTRO, ARM_READ_REG_15,
  ARM_WRITE_MEM_INTRO, ARM_REG_READ_INC_PC, ARM_WRITE_STATUS_INTRO,
  ARM_WRITE_REG_INTRO, COLLAPSE_ARM_STATE, ARM_READ_WRITE,
  ARM_WRITE_UNDEF_INTRO]

val UNABBREV_ALL_RULE = REWRITE_RULE [markerTheory.Abbrev_def] o
  repeat (fn th => let
  val tm = find_term (can (match_term ``Abbrev (x = y:'a)``)) (concl th)
  val (x,y) = (dest_eq o snd o dest_comb) tm     
  in REWRITE_RULE [] (INST [x|->y] th) end) o SPEC_ALL;

fun arm_step s = let
  val (tm,enc_th) = arm_decode s
  val tm2 = repeat (fst o dest_comb) tm
  val thms = filter (can (find_term (can (match_term tm2))) o concl) arm_rule_thms
  fun format th = let
    val th = UNABBREV_ALL_RULE th
    val tm3 = find_term (can (match_term ``enc v``)) (concl th)
    val tm3 = (snd o dest_comb) tm3
    val (i,t) = match_term tm3 tm
    val th = (INST i o INST_TYPE t) th
    val th = INST [``Rm:word4``|->``0w:word4``,``Rn:word4``|->``0w:word4``,``Rd:word4``|->``0w:word4``] th
    val th = REWRITE_RULE [CONDITION_PASSED2_AL] th
    val th = SIMP_RULE (srw_ss()++reg_list_ss) 
               [ADDR_MODE4_def,LET_DEF,WB_ADDRESS_def,ARM_WRITE_REG_PC_INTRO,
                UP_DOWN_def,FIRST_ADDRESS_def,ADDRESS_LIST_def] th
    val g = REWRITE_RULE [WORD_SUB_ONE_MULT,WORD_EQ_SUB_ZERO,GSYM word_sub_def] o SIMP_RULE arm_ss [enc_th]
    in if concl th = T then [] else [g th] end handle e => []
  val thms = foldr (uncurry append) [] (map format thms)
  in thms end;

(*

  val res = arm_step "0A0051E3"; (* cmp r1,#10 *)
  val res = arm_step "0A104122"; (* subcs r1,r1,#10 *)
  val res = arm_step "031082E0"; (* add r1,r2,r3 *)
  val res = arm_step "051082B2"; (* addlt r1,r2,#5 *)
  val res = arm_step "052095E5"; (* ldr r2,[r5,#5] *)
  val res = arm_step "0520B5E5"; (* ldr r2,[r5,#5]! *)
  val res = arm_step "01308914"; (* strne r3,[r9],#1 *)
  val res = arm_step "E00784E8"; (* stmia r4,{r5-r10} *)
  val res = arm_step "E00794E8"; (* ldmia r4,{r5-r10} *)
  val res = arm_step "060012E3"; (* tst r2,#6 *)
  val res = arm_step "FCFFFF2A"; (* bcs L *)
  val res = arm_step "0000A0E3"; (* mov r0, #0 *)
  val res = arm_step "000051E3"; (* L: cmp r1, #0 *)
  val res = arm_step "01008010"; (* addne r0, r0, #1 *)
  val res = arm_step "00109115"; (* ldrne r1, [r1] *)
  val res = arm_step "FBFFFF1A"; (* bne L *)
  val res = arm_step "030015E3"; (* tst r5,#3 *)
  val res = arm_step "0800001A"; (* bne L *)
  val res = arm_step "007095E5"; (* ldr r7,[r5] *)
  val res = arm_step "048095E5"; (* ldr r8,[r5,#4] *)
  val res = arm_step "039007E2"; (* and r9,r7,#3 *)
  val res = arm_step "010059E3"; (* cmp r9,#1 *)
  val res = arm_step "00708415"; (* strne r7,[r4] *)
  val res = arm_step "04808415"; (* strne r8,[r4,#4] *)
  val res = arm_step "01708412"; (* addne r7,r4,#1 *)
  val res = arm_step "00708515"; (* strne r7,[r5] *)
  val res = arm_step "015047E2"; (* sub r5,r7,#1 *)

*)
  

end
