structure arm_Lib :> arm_Lib =
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
  systemTheory.MEM_WRITE_BYTE_def, SHIFT_IMMEDIATE_def, ZIP, NZCV_def,
  IS_MSR_IMMEDIATE_def, IMMEDIATE_def, ADDR_MODE1_def, ADDR_MODE2_def,
  ADDR_MODE3_def, ADDRESS_LIST_def, CONDITION_PASSED2_def,
  WB_ADDRESS_def, FIRST_ADDRESS_def, ADDR_MODE4_def, UP_DOWN_def,
  systemTheory.MEM_WRITE_def, systemTheory.MEM_WRITE_WORD_def]

val arm_rev_ss = std_ss ++ rewrites [GSYM ARM_MODE_def, GSYM
  ARM_WRITE_REG_def,ARM_READ_REG_INTRO, GSYM ARM_READ_MEM_def, GSYM
  ARM_READ_STATUS_def, ARM_WRITE_REG_PC_INTRO, ARM_READ_REG_15,
  ARM_WRITE_MEM_INTRO, ARM_REG_READ_INC_PC, ARM_WRITE_STATUS_INTRO,
  ARM_WRITE_REG_INTRO, COLLAPSE_ARM_STATE, ARM_READ_WRITE,
  ARM_WRITE_UNDEF_INTRO, REG_READ6_EQ_ARM_READ_REG]

val UNABBREV_ALL_RULE = REWRITE_RULE [markerTheory.Abbrev_def] o
  repeat (fn th => let
  val tm = find_term (can (match_term ``Abbrev (x = y:'a)``)) (concl th)
  val (x,y) = (dest_eq o snd o dest_comb) tm
  in REWRITE_RULE [] (INST [x|->y] th) end) o SPEC_ALL;

fun expand_GENLIST th = let
  val tm = find_term (can (match_term ``GENLIST (f:num->'a) (NUMERAL n)``)) (concl th)
  val i = (Arbnum.toInt o numSyntax.dest_numeral o snd o dest_comb) tm
  fun g i = if i = 0 then ``0:num`` else mk_comb(``SUC``,g (i-1))
  val rw = GSYM (EVAL (g i))
  val rw = (RAND_CONV (REWRITE_CONV [rw]) THENC REWRITE_CONV [rich_listTheory.GENLIST] THENC SIMP_CONV std_ss [rich_listTheory.SNOC_APPEND,APPEND,word_mul_n2w]) tm
  val th = SIMP_RULE std_ss [rw,ZIP,STM_LIST_def,MAP,FOLDL,LDM_LIST_def] th
  val th = SIMP_RULE (srw_ss()) [systemTheory.TRANSFER_def] th
  in th end handle e => th;

fun arm_step s = let
  val (tm,enc_th) = arm_decode s
  val tm2 = repeat (fst o dest_comb) tm
  val thms = filter (can (find_term (can (match_term tm2))) o concl) arm_rule_thms
(*
  val th = hd thms
*)
  fun format th = let
    val th = UNABBREV_ALL_RULE th
    val th = ONCE_REWRITE_RULE [Abbrev_CONDITION_PASSED2] th
    val tm3 = find_term (can (match_term ``enc v``)) (concl th)
    val tm3 = (snd o dest_comb) tm3
    val (i,t) = match_term tm3 tm
    val th = (INST i o INST_TYPE t) th
    val th = INST [``Rm:word4``|->``0w:word4``,``Rn:word4``|->``0w:word4``,``Rd:word4``|->``0w:word4``] th
    val th = REWRITE_RULE [CONDITION_PASSED2_AL] th
    val th = SIMP_RULE (srw_ss()++reg_list_ss)
               [ADDR_MODE4_def,LET_DEF,WB_ADDRESS_def,ARM_WRITE_REG_PC_INTRO,
                UP_DOWN_def,FIRST_ADDRESS_def,ADDRESS_LIST_def] th
    val th = expand_GENLIST th
    val th = REWRITE_RULE [Abbrev_F] th
    in if concl th = T then [] else [th] end handle e => []
  val thms = foldr (uncurry append) [] (map format thms)
  val thms = map (SIMP_RULE arm_ss [enc_th]) thms
  val thms = map (SIMP_RULE arm_ss [REG_READ_REG_WRITE]) thms
  val thms = map (SIMP_RULE arm_rev_ss []) thms
  val thms = map (SIMP_RULE (std_ss++SIZES_ss) [n2w_11]) thms
  val g = REWRITE_RULE [WORD_SUB_ONE_MULT,WORD_EQ_SUB_ZERO,GSYM word_sub_def,systemTheory.addr30_def]
  val thms = map g thms
  in thms end;


(*

  val res = arm_step "E351000A"; (* cmp r1,#10 *)
  val res = arm_step "2241100A"; (* subcs r1,r1,#10 *)
  val res = arm_step "E0821003"; (* add r1,r2,r3 *)
  val res = arm_step "B2821005"; (* addlt r1,r2,#5 *)
  val res = arm_step "E5952005"; (* ldr r2,[r5,#5] *)
  val res = arm_step "E5B52005"; (* ldr r2,[r5,#5]! *)
  val res = arm_step "14893001"; (* strne r3,[r9],#1 *)
  val res = arm_step "E3120006"; (* tst r2,#6 *)
  val res = arm_step "2AFFFFFC"; (* bcs L *)
  val res = arm_step "E3A00000"; (* mov r0, #0 *)
  val res = arm_step "E3510000"; (* L: cmp r1, #0 *)
  val res = arm_step "10800001"; (* addne r0, r0, #1 *)
  val res = arm_step "15911000"; (* ldrne r1, [r1] *)
  val res = arm_step "1AFFFFFB"; (* bne L *)
  val res = arm_step "E3150003"; (* tst r5,#3 *)
  val res = arm_step "1A000008"; (* bne L *)
  val res = arm_step "E5957000"; (* ldr r7,[r5] *)
  val res = arm_step "E5958004"; (* ldr r8,[r5,#4] *)
  val res = arm_step "E2079003"; (* and r9,r7,#3 *)
  val res = arm_step "E3590001"; (* cmp r9,#1 *)
  val res = arm_step "15847000"; (* strne r7,[r4] *)
  val res = arm_step "15848004"; (* strne r8,[r4,#4] *)
  val res = arm_step "12847001"; (* addne r7,r4,#1 *)
  val res = arm_step "15857000"; (* strne r7,[r5] *)
  val res = arm_step "E2475001"; (* sub r5,r7,#1 *)
  val res = arm_step "0020D3E5"; (* ldrb r2,[r3] *)
  val res = arm_step "0020C3E5"; (* strb r2,[r3] *)
  val res = arm_step "E88407E0"; (* stmia r4,{r5-r10} *)
  val res = arm_step "E89407E0"; (* ldmia r4,{r5-r10} *)
  val res = arm_step "E8AD8007"; (* stmia sp!,{r0-r2,r15} *)
  val res = arm_step "E8BD8007"; (* ldmia sp!,{r0-r2,r15} *)

*)

end
