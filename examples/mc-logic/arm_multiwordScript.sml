(*
  quietdec := true;
  fun load_path_add x = loadPath := !loadPath @ [concat Globals.HOLDIR x];
  load_path_add "/examples/mc-logic";
  load_path_add "/examples/ARM/v4";
  load_path_add "/tools/mlyacc/mlyacclib";
*)

open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory arithmeticTheory wordsLib wordsTheory bitTheory;
open pairTheory listTheory rich_listTheory relationTheory pairTheory;
open set_sepTheory set_sepLib progTheory arm_progTheory arm_instTheory arm_progLib;
open multiwordTheory;

(*
  quietdec := false;
  show_code := false;
*)

val _ = new_theory "arm_multiword";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

fun n_times 0 f x = x | n_times n f x = n_times (n-1) f (f x) ;


(* temp *)

val HIDE1_xR_list = prove(
  ``ARM_PROG P code C (Q * xR_list (MAP (\x. (FST x, SOME (SND x))) xs)) Z ==>
    ARM_PROG P code C (Q * xR_list (MAP (\x. (FST x, NONE)) xs)) Z``,
  (MATCH_MP_TAC o GEN_ALL o RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_COMM] o 
   RW [AND_IMP_INTRO] o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL)
       ARM_PROG_PART_WEAKEN_POST1
  \\ Induct_on `xs` \\ REWRITE_TAC [MAP,SEP_IMP_REFL]
  \\ Cases \\ SIMP_TAC std_ss [MAP,xR_list_def]
  \\ MATCH_MP_TAC SEP_IMP_STAR \\ ASM_REWRITE_TAC []
  \\ SIMP_TAC std_ss [SEP_HIDE_THM,SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC []);

val ENCLOSE_STM_LDM = let
  val assum = ASSUME
    ``ARM_PROG (P * R30 a x * xR_list (MAP (\x. (FST x,NONE)) (xs:(word4 # word32) list)) * ~R 14w * ~S) 
        code C (Q * R30 a x * xR_list (MAP (\x. (FST x,NONE)) xs) * ~R 14w * ~S) {}``
  val th = Q.INST [`c_flag`|->`AL`,`a_mode`|->`am4_DB F`] arm_STM_R14
  val th = AUTO_HIDE_STATUS (FST_PROG2 (RW [PASS_CASES] th))
  val th = RW [ADDR_MODE4_ADDR_def,ADDR_MODE4_ADDR'_def,ADDR_MODE4_WB'_def,ADDR_MODE4_wb_def,ADDR_MODE4_WB_def,ADDR_MODE4_UP_def,LENGTH] th
  val th = MOVE_STAR_RULE `a*x*mm*ss` `a*mm*ss*x` th
  val th = RW [blank_ms_EQ_blank] th
  val th = MATCH_MP HIDE1_xR_list th
  val th = SIMP_RULE std_ss [xR_list_def,MAP,FST,SND,STAR_ASSOC] th
  val th1 = FRAME_COMPOSE th assum
  val th = Q.INST [`c_flag`|->`AL`,`a_mode`|->`am4_DB F`] arm_LDM_PC
  val th = AUTO_HIDE_STATUS (FST_PROG2 (RW [PASS_CASES] th))
  val th = RW [ADDR_MODE4_ADDR_def,ADDR_MODE4_ADDR'_def,ADDR_MODE4_WB'_def,ADDR_MODE4_wb_def,ADDR_MODE4_WB_def,ADDR_MODE4_UP_def,LENGTH] th
  val th = MOVE_STAR_RULE `a*x*mm*ss` `a*mm*ss*x` th
  val th = RW [blank_ms_EQ_blank] th
  val th = FRAME_COMPOSE th1 th
  val th = MOVE_POST `ms (x - n2w (SUC (LENGTH xs)))` th
  val th = RW [ADDR_MODE4_CMD_def] th
  val th = APP_PART_WEAKEN th 
    `blank_ms (x - n2w (SUC (LENGTH (xs:(word4 # word32)list)))) (LENGTH (reg_values ((15w,addr32 p)::xs)))`
    (REWRITE_TAC [SEP_IMP_ms_blank_ms])
  val th = RW [blank_ms_EQ_blank,LENGTH_reg_values,LENGTH] th
  val th = foldl (uncurry MOVE_POST) th [`R30 a`,`xR_list`,`R 14w`,`blank (x - 1w)`,`S`]  
  val th = foldl (uncurry MOVE_PRE) th [`R30 a`,`xR_list`,`R 14w`,`blank (x - 1w)`,`S`]  
  val th = DISCH_ALL (RW [GSYM R30_def] th)
  in th end;


(* general *)

val Rms_def = Define `Rms x xs = SEP_EXISTS a. R30 x a * ms a xs`;
val RRms_def = Define `RRms x y xs = SEP_EXISTS a. R30 x a * R30 y a * ms a xs`;
val Rblank_def = Define `Rblank x n = SEP_EXISTS a. R30 x a * blank_ms a n`;
val bignum_def = Define `bignum a i n = Rms a (n2mw i n)`;

val S_carry_def = Define `S_carry c (n,z,v) = S (n,z,c,v)`;

val Rblank_EQ_bignum = prove(
  ``!a i. Rblank a i = ~bignum a i``,
  SIMP_TAC (bool_ss++sep2_ss) [Rblank_def,SEP_HIDE_THM,bignum_def,Rms_def,blank_ms_EQ_ms]
  \\ REWRITE_TAC [SEP_IMP_EQ] \\ REPEAT STRIP_TAC 
  \\ SIMP_TAC std_ss [SEP_EXISTS,SEP_IMP_def,cond_STAR] \\ REPEAT STRIP_TAC << [  
    `?n. y' = n2mw i n` by METIS_TAC [n2mw_EXISTS]
    \\ Q.EXISTS_TAC `n` \\ Q.EXISTS_TAC `y` \\ FULL_SIMP_TAC bool_ss [],
    Q.EXISTS_TAC `y'` \\ Q.EXISTS_TAC `n2mw i y` \\ ASM_REWRITE_TAC [LENGTH_n2mw]]);

val ARM_PROG_HIDE_PRE3 = prove(
  ``(!sN:bool sZ:bool sV:bool. ARM_PROG (P * P' (sN,sZ,sV)) code C Q Z) ==> 
    ARM_PROG (P * ~P') code C Q Z``,
  CONV_TAC ((RATOR_CONV o RAND_CONV o QUANT_CONV o QUANT_CONV o QUANT_CONV) 
    (UNBETA_CONV ``(sN:bool,sZ:bool,sV:bool)``))
  \\ `!f. (!sN:bool sZ:bool sV:bool. f (sN,sZ,sV)) = !s. f s` by 
    (STRIP_TAC \\ EQ_TAC \\ STRIP_TAC \\ ASM_REWRITE_TAC [] 
     \\ Cases \\ Cases_on `r` \\ ASM_REWRITE_TAC [])
  \\ ASM_REWRITE_TAC [] \\ SIMP_TAC std_ss [ARM_PROG_HIDE_PRE]);  

fun HIDE_PRE3 th = MATCH_MP ARM_PROG_HIDE_PRE3 (QGENL [`sN`,`sZ`,`sV`] th);

val TEQ_BNE = let 
  val th1 = (*  teq i, t  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`a`|->`i`,`b`|->`t`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_TEQ2) 
  val th2 = (*  bne  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`NE`,`offset`|->`p` ] arm_B) 
  val th1 = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)` ] th2)
  val th1 = RW [addr32_11] (ALIGN_VARS ["x1","y1"] th1)
  val th1 = MOVE_STAR_RULE `s*c*i*t` `i*t*c*s` th1
  val th1 = RW [GSYM S_carry_def] th1
  val th1 = RW [STAR_ASSOC] (RW1 [STAR_COMM] (APP_FRAME `P` th1))  
  val th1 = (HIDE_PRE3 o HIDE_POST o HIDE_POST1) th1
  val th1 = PRE_MOVE_STAR `p*i*t*s` `p*i*s*t` th1    
  val th1 = Q.INST [`x1`|->`ix + x`,`y1`|->`ix + len`] th1
  val th1 = RW [WORD_EQ_ADD_LCANCEL] th1
  in th1 end;

val TEQ_BNE2 = let 
  val th1 = (*  teq i, t  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`a`|->`i`,`b`|->`t`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_TEQ2) 
  val th2 = (*  bne  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`NE`,`offset`|->`p` ] arm_B) 
  val th1 = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)` ] th2)
  val th1 = RW [addr32_11] (ALIGN_VARS ["x1","y1"] th1)
  val th1 = AUTO_HIDE_STATUS th1
  val th1 = RW [STAR_ASSOC] (RW1 [STAR_COMM] (APP_FRAME `P` th1))  
  val th1 = PRE_MOVE_STAR `p*i*t*s` `p*i*s*t` th1    
  val th1 = Q.INST [`x1`|->`ix + x`,`y1`|->`ix + len`] th1
  val th1 = SIMP_RULE (bool_ss++sep2_ss) [WORD_EQ_ADD_LCANCEL] th1
  in th1 end;

val ARM_PROG_DROP_COND1 = prove(
  ``ARM_PROG P code C (Q * cond g) Z ==> ARM_PROG P code C Q Z``,
  REPEAT STRIP_TAC \\ (MATCH_MP_TAC o GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o 
   SPEC_ALL o UNDISCH o SPEC_ALL) ARM_PROG_WEAKEN_POST1
  \\ Q.EXISTS_TAC `Q * cond g` \\ ASM_REWRITE_TAC [SEP_IMP_REFL,SEP_IMP_MOVE_COND]);
  
val ONE_EQ_wLENGTH = prove(
  ``LENGTH xs < 2**30 ==> ((1w:word30 = n2w (SUC (LENGTH (xs:word32 list)))) = (xs = []))``,
  REWRITE_TAC [wLENGTH_def,LENGTH,RW1 [ADD_COMM] ADD1,GSYM word_add_n2w]  
  \\ REWRITE_TAC [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL)]
  \\ SIMP_TAC bool_ss [n2w_11,ZERO_LT_dimword,LESS_MOD]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11,ZERO_LT_dimword,LESS_MOD]
  \\ METIS_TAC [LENGTH_NIL]);

val FORALL_CONS_EQ_FORALL = prove(
  ``(!y ys. (LENGTH (x::xs) <= LENGTH (y::ys)) ==> P (y::ys)) ==> 
    !ys. (LENGTH (x::xs) <= LENGTH ys) ==> P ys``,
  STRIP_TAC \\ Cases \\ ASM_SIMP_TAC bool_ss [DECIDE ``~(SUC n <= 0)``,LENGTH]);

val FORALL_CONS_EQ_FORALL_NOT_NIL = prove(
  ``(!x xs. P (x::xs)) ==> !xs. ~(xs = []) ==> P xs``,
  STRIP_TAC \\ Cases \\ ASM_REWRITE_TAC []);

fun GEN_CONS_LE y ys th = let
  val th = Q.INST [y|->`hd_variable__`,ys|->`tl_variable__`] th
  val th = CONV_RULE (UNBETA_CONV ``hd_variable__:word32 ::tl_variable__``) th
  val th = DISCH ``LENGTH (x:word32 ::xs) <= LENGTH (hd_variable__ :word32 ::tl_variable__ )`` th
  val th = (Q.SPEC ys o MATCH_MP FORALL_CONS_EQ_FORALL o QGENL [`hd_variable__`,`tl_variable__`]) th
  in SIMP_RULE std_ss [] th end;

fun GEN_CONS xxs x xs th = let
  val th = CONV_RULE (UNBETA_CONV xxs) (DISCH_ALL th)  
  val th = (Q.SPEC xs o MATCH_MP FORALL_CONS_EQ_FORALL_NOT_NIL o QGENL [x,xs]) th  
  val th = (RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_COMM] o SIMP_RULE std_ss [AND_IMP_INTRO]) th
  in th end;

fun GEN_x_CONS_xs th = GEN_CONS ``x:word32 :: xs`` `x` `xs` th;

val FORALL_CONS_EQ_FORALL_NOT_NIL = prove(
  ``(!x xs. P xs x (x::xs)) ==> !xs. ~(xs = []) ==> P (TL xs) (HD xs) xs``,
  STRIP_TAC \\ Cases \\ ASM_REWRITE_TAC [HD,TL]);

fun CONS_GEN t th = let
  val tm = parse_in_context (free_varsl (concl th :: hyp th)) t
  val (u1,u2) = dest_comb tm
  val u1 = snd (dest_comb u1)
  val c = UNBETA_CONV u1 THENC RATOR_CONV (UNBETA_CONV u2)
  val th1 = CONV_RULE (UNBETA_CONV tm THENC RATOR_CONV c) th
  val th1 = GENL [u1,u2] th1
  val th1 = MATCH_MP FORALL_CONS_EQ_FORALL_NOT_NIL th1
  val th1 = SPEC u2 (SIMP_RULE bool_ss [] th1)
  in th1 end;

fun CONS_GENL ts th = RW [AND_IMP_INTRO] (foldr (uncurry CONS_GEN) th ts);

val IMP_ms_EQ_emp = prove(
  ``!zs x. (LENGTH zs = 0) ==> (ms x zs = emp)``,
  Cases \\ REWRITE_TAC [ms_def,LENGTH,DECIDE ``~(SUC n = 0)``]);

val ARM_PROG_CONTAINS_ms_CONS = 
  RW [LENGTH,GSYM LESS_EQ] (Q.SPEC `x::xs` ARM_PROG_CONTAINS_ms);

val ARM_PROG_COMPOSE_0 = prove(
  ``ARM_PROG Q [] C' SEP_F Z' ==> ARM_PROG P cs C SEP_F ((Q,I) INSERT Z) ==> 
    ARM_PROG P cs (C UNION C') SEP_F (Z UNION Z')``,
  REWRITE_TAC [ARM_PROG_THM,pcINC_0,ARM_GPROG_FALSE_POST,ARM_GPROG_EMPTY_CODE] \\ REPEAT STRIP_TAC
  \\ `ARM_GPROG {(P,I)} ((cs,I) INSERT C) (Z UNION {(Q,I)})` by 
        ASM_REWRITE_TAC [RW1 [UNION_COMM] (GSYM INSERT_SING_UNION)]
  \\ `ARM_GPROG ({(Q,I)} UNION {}) C' Z'` by ASM_REWRITE_TAC [UNION_EMPTY]
  \\ IMP_RES_TAC ARM_GPROG_COMPOSE \\ FULL_SIMP_TAC bool_ss [UNION_EMPTY,INSERT_UNION_EQ]);

fun BASIC_arm_SIMP start finish = SEP_IMP_RULE
   (SIMP_CONV (bool_ss++sep2_ss) ([SEP_IMP_MOVE_COND] @ start)
    THENC REWRITE_CONV [wLENGTH_def,LENGTH,ADD1,GSYM word_add_n2w,LESS_EQ_REFL,
      WORD_ADD_0,ms_def,emp_STAR,EQ_ADD_RCANCEL,LE_ADD_RCANCEL,RW1[ADD_COMM]ADD1]
    THENC SIMP_CONV (bool_ss++sep_ss) [GSYM LENGTH_NIL,ADD_CLAUSES,IMP_ms_EQ_emp]
    THENC REWRITE_CONV ([ms_def,emp_STAR,WORD_ADD_0] @ finish)
    THENC SIMP_CONV bool_ss ([AC WORD_ADD_COMM WORD_ADD_ASSOC] @ finish));  

val ARM_PROG_CONTAINS_ms_CONS_INTRO = prove(
  ``(LENGTH xs < 2 ** 30 ==> ARM_PROG P code C Q Z) ==>
    (!a x. SEP_CONTAINS (ms a (x::xs)) P ==> ARM_PROG P code C Q Z)``,
  METIS_TAC [ARM_PROG_CONTAINS_ms_CONS]);

fun DISCH_ELIM_xs_ASSUM' d a x m th = let
  val th = MATCH_MP ARM_PROG_CONTAINS_ms_CONS_INTRO (DISCH_ALL th)
  val th = Q.SPECL [a,x] th
  val c  = REWRITE_CONV [d] THENC 
           RAND_CONV (MOVE_OUT_CONV m) THENC 
           REWRITE_CONV [SEP_CONTAINS_STAR]
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) c) th
  in RW [] th end;

fun DISCH_ELIM_xs_ASSUM d a x th =
  DISCH_ELIM_xs_ASSUM' d a x `ms ixx` th;

val IMP_cond_SEP_IMP = prove(
  ``(g ==> h) ==> SEP_IMP (P * cond g) (P * cond h)``,
  Cases_on `g` \\ SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_REFL]
  \\ REWRITE_TAC [SEP_IMP_def,SEP_F_def]);

fun SEP_IMP_cond_DECIDE th = let
  val goal = (snd o dest_comb o fst o dest_comb o snd o dest_thm) th
  val lemma = prove(goal, MATCH_MP_TAC IMP_cond_SEP_IMP \\ DECIDE_TAC)
  in MP th lemma end;

val EXPAND_PAIR = prove(
  ``!g x y. ((x,y) = g) = (x = FST g) /\ (y = SND g)``,
  Cases \\ SIMP_TAC std_ss []);

val ARM_PROG_COMPOSE_WEAKEN = prove(
  ``ARM_PROG P code C Q {} ==> 
    ARM_PROG P1 code C Q1 ((P * Q2,I) INSERT Z) ==>
    SEP_IMP (Q * Q2) Q1 ==>
    ARM_PROG P1 code C Q1 Z``,
  REWRITE_TAC [ARM_PROG_THM] \\ REPEAT STRIP_TAC 
  \\ Q.PAT_ASSUM `ARM_GPROG {(P,I)} ((code,I) INSERT C) {(Q,pcINC code)}` 
    (ASSUME_TAC o RW [setSTAR_CLAUSES] o Q.SPEC `Q2` o MATCH_MP ARM_GPROG_FRAME)
  \\ IMP_RES_TAC ARM_GPROG_WEAKEN_POST
  \\ (MATCH_MP_TAC o RW [INSERT_UNION_EQ,UNION_EMPTY,UNION_IDEMPOT,INSERT_INSERT] o 
      RW1 [UNION_COMM] o Q.SPECL [`Y`,`{}`,`{(P * Q2,I)}`,`C`,`C`,
      `(Q1,pcINC code) INSERT Z`,`{(Q1,pcINC code)}`]) ARM_GPROG_COMPOSE
  \\ ONCE_REWRITE_TAC [INSERT_COMM] \\ ASM_REWRITE_TAC []);

fun extract_spec th substs uni_list abs_list = let
  val p = parse_in_context (free_varsl (concl th :: hyp th))
  val ss = map (fn (x,y) => (p x |-> p y)) substs
  val tm = (fst o dest_comb o concl) th
  val tm = mk_comb(tm,(snd o dest_comb o snd o dest_comb o concl) th)
  val tm = subst ss tm
  val tm = foldr mk_forall tm (map p uni_list)
  val tm = foldr mk_abs tm (map p abs_list)
  in tm end;

fun delete_fst_case thms th = let
  val tm = (fst o dest_imp o concl) th
  val tac = SIMP_TAC (bool_ss++sep2_ss) (LENGTH :: thms)
            \\ REWRITE_TAC [ARM_PROG_MOVE_COND,ARM_PROG_FALSE_PRE]
            \\ REPEAT STRIP_TAC \\ `F` by DECIDE_TAC
  val th1 = prove(tm,tac)
  in MP th th1 end;

fun q_alpha v tm = let
  val t = mk_var(v,type_of (fst (dest_abs tm)))
  in ALPHA_CONV t tm end handle e => ALL_CONV tm;

fun alpha_forall_list [] tm = ALL_CONV tm
  | alpha_forall_list (v::vs) tm =
      RAND_CONV (q_alpha v THENC ABS_CONV (alpha_forall_list vs)) tm; 

fun rename_foralls xs th =
  CONV_RULE ((RATOR_CONV o RAND_CONV) (alpha_forall_list xs)) th;

fun extract_assum th = let
  val tm = (repeat (snd o dest_forall) o fst o dest_imp o concl) th
  val th = (SPEC_ALL o ASSUME o fst o dest_imp) tm
  in th end;

fun tidy_up th1 th = let
  val tm = (fst o dest_imp o concl) th1
  val (tm,vs1) = repeat (fn (tm,xs) => let val (v,x) = dest_forall tm in (x,xs@[v]) end) (tm,[])
  val tm = (snd o dest_imp) tm
  val (tm,vs2) = repeat (fn (tm,xs) => let val (v,x) = dest_forall tm in (x,xs@[v]) end) (tm,[])
  in (GENL vs1 o DISCH_ALL o GENL vs2) th end;


(* addition *)

val arm_add_pre_def = Define `
  arm_add_pre i j k t a b xs ys c ix jx kx = 
     R30 k kx * R30 i ix * R30 j jx * ~R a * ~R b * R30 t (ix + wLENGTH xs) *
     blank_ms kx (LENGTH xs) * ms ix xs * ms jx ys * ~S_carry c * cond ~(xs = []) * 
     cond (LENGTH xs <= LENGTH ys)`;

val arm_add_post_def = Define `
  arm_add_post i j k t a b xs ys c ix jx kx = 
     R30 k (kx + wLENGTH xs) * R30 i (ix + wLENGTH xs) * R30 j (jx + wLENGTH xs) * 
     ms kx (FST (mw_add xs ys c)) * ms ix xs * ms jx ys * ~R a * ~R b *
     R30 t (ix + wLENGTH xs) * ~S_carry (SND (mw_add xs ys c))`;

val add_thm = (SIMP_RULE (bool_ss++SIZES_ss) [] o INST_TYPE [``:'a``|->``:32``] o GSYM) (RW [dimword_def] single_add_cases)
val arm_add_SIMP = BASIC_arm_SIMP [arm_add_post_def,arm_add_pre_def] [mw_add_cases,RW [ADD1] blank_ms_def];  

val arm_add_imp = save_thm("arm_add_imp",let

  (* step 1: get basic spec (partly auto-generate code) *)
  (* make_spec ["ldr a, [i], #4","ldr b, [j], #4","adcs a, a, b","str a, [k], #4"] *)
  val th = (*  ldr a, [i], #4  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`b`|->`i`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  ldr b, [j], #4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`b`,`b`|->`j`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4` `(x4)*(x1*x2*x3)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  adcs a, a, b    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_ADC2'))) `x1*x2*x3*x4*x5*x6*x7` `(x1*x4*x5)*(x2*x3*x6*x7)` `x1*x2*x3` `(x2*x3*x1)*(emp)`
  val th = (*  str a, [k], #4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`b`|->`k`,`imm`|->`4w`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7` `(x1*x3)*(x2*x4*x5*x6*x7)` `x1*x2*x3*x4` `(x1*x4)*(x2*x3)`
  val th = ALIGN_VARS ["y4","y2","y1"] th
  val th = RW [GSYM (EVAL ``2**32``),ADD_ASSOC] th
  val th = AUTO_HIDE_PRE [`R a`,`R b`,`M y4`] (AUTO_HIDE_POST1 [`R a`,`R b`] th)
  val th = MOVE_PRE `S` (MOVE_POST1 `S` th)
  val th = RW [add_thm,addr32_11,GSYM S_carry_def] th
  val th = HIDE_PRE3 (HIDE_POST1 th)
  val th = Q.INST [`y1`|->`ix`,`y2`|->`jx`,`y4`|->`kx`,`z1`|->`x`,`z2`|->`y`,`z4`|->`z`] th
  val th = APP_FRAME `ms (ix + 1w) xs * ms (jx + 1w) ys * blank_ms (kx + 1w) (LENGTH xs)` th
  val th = MOVE_POST1 `S_carry (SND (single_add x y sC))` (MOVE_POST1 `R30 i` th)

  (* step 2: fix first post *)
  val th = MATCH_COMPOSE (APP_FRAME `R30 t (ix + wLENGTH ((x:word32)::xs))` th) TEQ_BNE
  val th = DISCH ``LENGTH (xs:word32 list) < 2**30`` th
  val th = UNDISCH (SIMP_RULE bool_ss [ONE_EQ_wLENGTH] th)
  val th = APP_FRAME `cond (LENGTH (xs:word32 list) <= LENGTH (ys:word32 list))` th
  val th = (arm_add_SIMP o SPEC_WEAKEN1 th)
    `arm_add_post i j k t a b ((x:word32)::xs) ((y:word32)::ys) sC ix jx kx`

  (* step 3: fix pre *)
  val th = (arm_add_SIMP o SPEC_STRENGTHEN th)
    `arm_add_pre i j k t a b ((x:word32) ::xs) ((y:word32) ::ys) sC ix jx kx`
  val th = DISCH_ELIM_xs_ASSUM' arm_add_pre_def `ix` `x` `ms ix` th

  (* step 4: show that second post satisfies the precondition *)
  val th = (arm_add_SIMP o SPEC_WEAKEN th)
    `arm_add_pre i j k t a b xs ys (SND (single_add x (y:word32) sC)) (ix+1w) (jx+1w) (kx+1w) *
     (M kx (FST (single_add (x:word32) y sC)) * M ix x * M jx y)`
  val th = CLOSE_LOOP th

  (* step 5: instantiate induction and extract ind hyp *)
  val tm = extract_spec th [(`x::xs`,`xs`),(`y::ys`,`ys`)] [`ix`,`jx`,`kx`] [`xs`,`ys`,`sC`]
  val th1 = SIMP_RULE bool_ss [EXPAND_PAIR,GSYM AND_IMP_INTRO] (ISPEC tm mw_add_ind)
  val th1 = delete_fst_case [arm_add_pre_def] th1
  val th1 = delete_fst_case [arm_add_pre_def] th1
  val asm = extract_assum th1

  (* step 6: match step and prove postcondition *)
  val asm = MATCH_MP ARM_PROG_COMPOSE_WEAKEN asm
  val th = arm_add_SIMP (MATCH_MP asm (Q.INST [`sC`|->`c`] th))
 
  (* step 7: clean up *)
  val th = MATCH_MP th1 (tidy_up th1 th)
  val th = SPEC_ALL (Q.SPECL [`xs`,`ys`,`c`] th)

  in th end);


(* subtraction *)

val arm_sub_pre_def = Define `
  arm_sub_pre i j k t a b xs ys c ix jx kx = 
     R30 k kx * R30 i ix * R30 j jx * ~R a * ~R b * R30 t (ix + wLENGTH xs) *
     blank_ms kx (LENGTH xs) * ms ix xs * ms jx ys * ~S_carry c * cond ~(xs = []) * 
     cond (LENGTH xs <= LENGTH ys)`;

val arm_sub_post_def = Define `
  arm_sub_post i j k t a b xs ys c ix jx kx = 
     R30 k (kx + wLENGTH xs) * R30 i (ix + wLENGTH xs) * R30 j (jx + wLENGTH xs) * 
     ms kx (FST (mw_sub xs ys c)) * ms ix xs * ms jx ys * ~R a * ~R b *
     R30 t (ix + wLENGTH xs) * ~S_carry (SND (mw_sub xs ys c))`;

val sub_thm = (SIMP_RULE (bool_ss++SIZES_ss) [] o INST_TYPE [``:'a``|->``:32``] o GSYM) (RW [dimword_def] single_sub_cases)
val arm_sub_SIMP = BASIC_arm_SIMP [arm_sub_post_def,arm_sub_pre_def] [mw_sub_cases,RW [ADD1] blank_ms_def];  

val arm_sub_imp = save_thm("arm_sub_imp",let

  (* step 1: get basic spec (partly auto-generate code) *)
  (* make_spec ["ldr a, [i], #4","ldr b, [j], #4","sbcs a, a, b","str a, [k], #4"] *)
  val th = (*  ldr a, [i], #4  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`b`|->`i`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  ldr b, [j], #4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`b`,`b`|->`j`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4` `(x4)*(x1*x2*x3)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  sbcs a, a, b    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_SBC2'))) `x1*x2*x3*x4*x5*x6*x7` `(x1*x4*x5)*(x2*x3*x6*x7)` `x1*x2*x3` `(x2*x3*x1)*(emp)`
  val th = (*  str a, [k], #4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`b`|->`k`,`imm`|->`4w`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7` `(x1*x3)*(x2*x4*x5*x6*x7)` `x1*x2*x3*x4` `(x1*x4)*(x2*x3)`
  val th = ALIGN_VARS ["y4","y2","y1"] th
  val th = RW [GSYM (EVAL ``2**32``),ADD_ASSOC] th
  val th = AUTO_HIDE_PRE [`R a`,`R b`,`M y4`] (AUTO_HIDE_POST1 [`R a`,`R b`] th)
  val th = MOVE_PRE `S` (MOVE_POST1 `S` th)
  val th = RW [sub_thm,addr32_11,GSYM S_carry_def] th
  val th = HIDE_PRE3 (HIDE_POST1 th)
  val th = Q.INST [`y1`|->`ix`,`y2`|->`jx`,`y4`|->`kx`,`z1`|->`x`,`z2`|->`y`,`z4`|->`z`] th
  val th = APP_FRAME `ms (ix + 1w) xs * ms (jx + 1w) ys * blank_ms (kx + 1w) (LENGTH xs)` th
  val th = MOVE_POST1 `S_carry (SND (single_sub x y sC))` (MOVE_POST1 `R30 i` th)

  (* step 2: fix first post *)
  val th = MATCH_COMPOSE (APP_FRAME `R30 t (ix + wLENGTH ((x:word32)::xs))` th) TEQ_BNE
  val th = DISCH ``LENGTH (xs:word32 list) < 2**30`` th
  val th = UNDISCH (SIMP_RULE bool_ss [ONE_EQ_wLENGTH] th)
  val th = APP_FRAME `cond (LENGTH (xs:word32 list) <= LENGTH (ys:word32 list))` th
  val th = (arm_sub_SIMP o SPEC_WEAKEN1 th)
    `arm_sub_post i j k t a b ((x:word32)::xs) ((y:word32)::ys) sC ix jx kx`

  (* step 3: fix pre *)
  val th = (arm_sub_SIMP o SPEC_STRENGTHEN th)
    `arm_sub_pre i j k t a b ((x:word32) ::xs) ((y:word32) ::ys) sC ix jx kx`
  val th = DISCH_ELIM_xs_ASSUM' arm_sub_pre_def `ix` `x` `ms ix` th

  (* step 4: show that second post satisfies the precondition *)
  val th = (arm_sub_SIMP o SPEC_WEAKEN th)
    `arm_sub_pre i j k t a b xs ys (SND (single_sub x (y:word32) sC)) (ix+1w) (jx+1w) (kx+1w) *
     (M kx (FST (single_sub (x:word32) y sC)) * M ix x * M jx y)`
  val th = CLOSE_LOOP th

  (* step 5: instantiate induction and extract ind hyp *)
  val tm = extract_spec th [(`x::xs`,`xs`),(`y::ys`,`ys`)] [`ix`,`jx`,`kx`] [`xs`,`ys`,`sC`]
  val th1 = SIMP_RULE bool_ss [EXPAND_PAIR,GSYM AND_IMP_INTRO] (ISPEC tm mw_sub_ind)
  val th1 = delete_fst_case [arm_sub_pre_def] th1
  val th1 = delete_fst_case [arm_sub_pre_def] th1
  val asm = extract_assum th1

  (* step 6: match step and prove postcondition *)
  val asm = MATCH_MP ARM_PROG_COMPOSE_WEAKEN asm
  val th = arm_sub_SIMP (MATCH_MP asm (Q.INST [`sC`|->`c`] th))

  (* step 7: clean up *)
  val th = MATCH_MP th1 (tidy_up th1 th)
  val th = SPEC_ALL (Q.SPECL [`xs`,`ys`,`c`] th)

  in th end);


(* multiplication *)

val mul_thm = GSYM single_mul_cases32;

(* ... *)


(* mw_add_mul_mult_def *)

val arm_amm_pre_def = Define `
  arm_amm_pre' xx ix ixx xs yx iy iyy ys zx iz izz zs p px q qx v t b bx c cx = 
    R b bx * R c cx * ms (izz+1w) zs * ms ixx xs * ms iyy ys * 
    R v 0w * ~R xx * ~R zx * ~R yx * R p px * R q qx * ~M izz *
    R30 ix ixx * R30 iy iyy * R30 iz (izz + 1w) * R30 t (ixx + wLENGTH xs) * ~S *
    cond ~(xs = []) * cond ((LENGTH xs = LENGTH ys) /\ (LENGTH ys = LENGTH zs))`;

val arm_amm_post_def = Define `
  arm_amm_post' xx ix ixx xs yx iy iyy ys zx iz izz zs p px q qx v t b bx c cx = 
    R b (SND (SND (mw_add_mul_mult xs ys zs px qx cx bx))) *
    R c (FST (SND (mw_add_mul_mult xs ys zs px qx cx bx))) *
    ms izz (FST (mw_add_mul_mult xs ys zs px qx cx bx)) *
    ms ixx xs * ms iyy ys * R v 0w * ~R xx * ~R zx * ~R yx * R p px * R q qx *
    R30 ix (ixx + wLENGTH xs) *
    R30 iy (iyy + wLENGTH xs) *
    R30 iz (izz + wLENGTH xs + 1w) *
    R30 t (ixx + wLENGTH xs) * ~S *
    ~M (izz + wLENGTH xs)`;

val arm_amm_imp = save_thm("arm_amm_imp",let

  val aam_thm = (SIMP_RULE (bool_ss++SIZES_ss) [ADD_0,WORD_ADD_0,GSYM add_thm,GSYM mul_thm] o INST_TYPE [``:'a``|->``:32``] o GSYM) add_double_mul_cases
  val amm_nil_lemma = prove(
    ``P * cond (xs = []) * cond ((LENGTH xs = LENGTH ys) /\ (LENGTH ys = LENGTH zs)) =
      P * cond ((xs = []) /\ (ys = []) /\ (zs = []))``,
    REWRITE_TAC [SEP_cond_CLAUSES,GSYM STAR_ASSOC]
    \\ MATCH_MP_TAC (prove(``(x = y) ==> (P * cond x = P * cond y)``,SIMP_TAC bool_ss []))
    \\ METIS_TAC [LENGTH_NIL])
  val arm_aam_SIMP = BASIC_arm_SIMP [arm_amm_post_def,arm_amm_pre_def,ms_def] [mw_add_mul_mult_cases];  

  (* step 1: get basic spec (partly auto-generate code) *)
  (* make_spec ["ldr  z,[iz],#4","ldr  x,[ix],#4","ldr  y,[iy],#4","umlal v,z,x,p","mov  x,#0","umlal x,z,y,q","adds z,z,c","str  z,[iz,#-8]","adcs b,v,b","mov  v,#0","adcs y,v,#0","adds c,x,b","adcs b,y,#0"] *)
  val th = (*  ldr  z,[iz],#4   *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`z`,`b`|->`iz`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  ldr  x,[ix],#4   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`x`,`b`|->`ix`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4` `(x4)*(x1*x2*x3)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  ldr  y,[iy],#4   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`y`,`b`|->`iy`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7` `(x4)*(x1*x2*x3*x5*x6*x7)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  umlal v,z,x,p    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c'`|->`v`,`c`|->`z`,`a`|->`x`,`b`|->`p`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4`,`z'`|->`z'4` ] arm_UMLAL4))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10` `(x4*x5*x8)*(x1*x2*x3*x6*x7*x9*x10)` `x1*x2*x3*x4*x5` `(x5*x1*x3)*(x2*x4)`
  val th = (*  mov  x,#0        *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`x`,`a_mode`|->`Imm 0w`,`x`|->`x5` ] arm_MOV1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12` `(x1*x5)*(x2*x3*x4*x6*x7*x8*x9*x10*x11*x12)` `x1*x2` `(x1*x2)*(emp)`
  val th = (*  umlal x,z,y,q    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c'`|->`x`,`c`|->`z`,`a`|->`y`,`b`|->`q`,`x`|->`x6`,`y`|->`y6`,`z`|->`z6`,`z'`|->`z'6` ] arm_UMLAL4))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12` `(x1*x2*x4*x6)*(x3*x5*x7*x8*x9*x10*x11*x12)` `x1*x2*x3*x4*x5` `(x4*x5*x3*x1)*(x2)`
  val th = (*  adds z,z,c       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`z`,`b`|->`c`,`a_mode`|->`OneReg`,`x`|->`x7`,`y`|->`y7` ] arm_ADD2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13` `(x3*x5)*(x1*x2*x4*x6*x7*x8*x9*x10*x11*x12*x13)` `x1*x2*x3` `(x1*x3)*(x2)`
  val th = (*  str  z,[iz,#-8]  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (8w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`a`|->`z`,`b`|->`iz`,`imm`|->`8w`,`x`|->`x8`,`y`|->`y8`,`z`|->`z8` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14` `(x1*x3*x13)*(x2*x4*x5*x6*x7*x8*x9*x10*x11*x12*x14)` `x1*x2*x3*x4` `(x1*x4*x2)*(x3)`
  val th = (*  adcs b,v,b       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`v`,`a_mode`|->`OneReg`,`x`|->`x9`,`y`|->`y9` ] arm_ADC2))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x4*x10)*(x1*x2*x3*x5*x6*x7*x8*x9*x11*x12*x13*x14*x15)` `x1*x2*x3` `(x3*x1)*(x2)`
  val th = (*  mov  v,#0        *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x10` ] arm_MOV1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16` `(x1*x3)*(x2*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16)` `x1*x2` `(x1*x2)*(emp)`
  val th = (*  adcs y,v,#0      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`y`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x11`,`y`|->`y11` ] arm_ADC2))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16` `(x1*x2*x8)*(x3*x4*x5*x6*x7*x9*x10*x11*x12*x13*x14*x15*x16)` `x1*x2*x3` `(x1*x3*x2)*(emp)`
  val th = (*  adds c,x,b       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`x`,`a_mode`|->`OneReg`,`x`|->`x12`,`y`|->`y12`,`z`|->`z12` ] arm_ADD3))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16` `(x3*x4*x8*x10)*(x1*x2*x5*x6*x7*x9*x11*x12*x13*x14*x15*x16)` `x1*x2*x3*x4` `(x4*x2*x3*x1)*(emp)`
  val th = (*  adcs b,y,#0      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`y`,`a_mode`|->`Imm 0w`,`x`|->`x13`,`y`|->`y13` ] arm_ADC2))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16` `(x2*x4*x6)*(x1*x3*x5*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16)` `x1*x2*x3` `(x2*x3*x1)*(emp)`
  val th = ALIGN_VARS ["y5","y3","y2","y1"] (AUTO_HIDE_STATUS th)
  val th = Q.INST [`z'4`|->`0w`] th    
  val th = INST [``b:word32``|->``bx:word32``] (RW [WORD_ADD_0,aam_thm] th)
  val th = AUTO_HIDE_POST1 [`R x`,`R z`,`R y`] th
  val th = AUTO_HIDE_PRE [`R x`,`R z`,`R y`,`M (y1 + 1w - 2w)`] th
  val th = Q.INST [`y1`|->`izz`,`y2`|->`ixx`,`y3`|->`iyy`,`z1`|->`zx`,`z2`|->`xx`,`z3`|->`yx`,`y4`|->`px`,`y6`|->`qx`,`y7`|->`cx`,`y9`|->`bx`] th
  val th = APP_FRAME `ms (ixx + 1w) xs * ms (iyy + 1w) ys * ms (izz + 1w) zs` th
  val th = Q.INST [`izz`|->`izz+1w`] th
  val rw = prove(``x+1w+1w-2w = x``,SIMP_TAC arith_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,WORD_ADD_SUB])
  val th = AUTO_HIDE_POST1 [`M (izz+1w)`] (RW [rw] th)
  val th = MOVE_POST1 `S` (MOVE_POST1 `R30 ix` th)

  (* step 2: fix first post *)
  val th = MATCH_COMPOSE (APP_FRAME `R30 t (ixx + wLENGTH ((x:word32)::xs))` th) TEQ_BNE2
  val th = DISCH ``LENGTH (xs:word32 list) < 2**30`` th
  val th = UNDISCH (SIMP_RULE bool_ss [ONE_EQ_wLENGTH] th)
  val th = APP_FRAME `cond ((LENGTH (xs:word32 list) = LENGTH (ys:word32 list)) /\ (LENGTH (ys:word32 list) = LENGTH (zs:word32 list)))` th  
  val th = (arm_aam_SIMP o RW [amm_nil_lemma] o SPEC_WEAKEN1 th)
    `arm_amm_post' x ix ixx (xx::xs) y iy iyy (yx::ys) z iz izz (zx::zs) p px q qx v t b bx c cx`
  
  (* step 3: fix pre *)
  val th1 = (arm_aam_SIMP o SPEC_STRENGTHEN th)
    `arm_amm_pre' x ix ixx (xx::xs) y iy iyy (yx::ys) z iz izz (zx::zs) p px q qx v t b bx c cx`
  val th = DISCH_ELIM_xs_ASSUM arm_amm_pre_def `ixx` `xx` th1

  (* step 4: show that second post satisfies the precondition *)
  val th1 = (arm_aam_SIMP o SPEC_WEAKEN th)
    `arm_amm_pre' x ix (ixx+1w) xs y iy (iyy+1w) ys z iz (izz+1w) zs p px q qx v t b 
       (SND (SND (add_double_mul xx yx px qx cx bx zx))) c 
       (FST (SND (add_double_mul xx yx px qx cx bx zx))) *
     (M izz (FST (add_double_mul xx yx px qx cx bx zx)) * M ixx xx * M iyy yx)`
  val th = CLOSE_LOOP th1

  (* step 5: instantiate induction and extract ind hyp *)
  val tm = extract_spec th [(`xx::xs`,`xs`),(`yx::ys`,`ys`),(`zx::zs`,`zs`)] [`ixx`,`iyy`,`izz`] [`xs`,`ys`,`zs`,`px`,`qx`,`cx`,`bx`]
  val th1 = SIMP_RULE bool_ss [EXPAND_PAIR,GSYM AND_IMP_INTRO] (ISPEC tm mw_add_mul_mult_ind)
  val th1 = n_times 4 (delete_fst_case [arm_amm_pre_def]) th1
  val th1 = rename_foralls ["xx","xs","yx","ys","zx","zs","px","qx","cx","bx"] th1
  val asm = extract_assum th1

  (* step 6: match step and prove postcondition *)
  val asm = MATCH_MP ARM_PROG_COMPOSE_WEAKEN asm
  val th = arm_aam_SIMP (MATCH_MP asm th)

  (* step 7: clean up *)
  val th = MATCH_MP th1 (tidy_up th1 th)
  val th = (SPEC_ALL o RW [FST,SND] o Q.SPECL [`xs`,`ys`,`zs`,`(px,qx,bx,cx)`]) th

  in th end);


(* mw_add_mul_mult_def - with zero input *)

val arm_amm0_pre_def = Define `
  arm_amm0_pre xx ix ixx xs yx iy iyy ys zx iz izz p px q qx v t b bx c cx = 
    R b bx * R c cx * blank_ms izz (LENGTH xs) * ms ixx xs * ms iyy ys * 
    ~R v * ~R xx * ~R zx * ~R yx * R p px * R q qx *
    R30 ix ixx * R30 iy iyy * R30 iz izz * R30 t (ixx + wLENGTH xs) * ~S *
    cond ~(xs = []) * cond (LENGTH xs = LENGTH ys)`;

val arm_amm0_post_def = Define `
  arm_amm0_post xx ix ixx xs yx iy iyy ys zx iz izz p px q qx v t b bx c cx = 
    R b (SND (SND (mw_add_mul_mult0 xs ys px qx cx bx))) *
    R c (FST (SND (mw_add_mul_mult0 xs ys px qx cx bx))) *
    ms izz (FST (mw_add_mul_mult0 xs ys px qx cx bx)) *
    ms ixx xs * ms iyy ys * ~R v * ~R xx * ~R zx * ~R yx * R p px * R q qx *
    R30 ix (ixx + wLENGTH xs) *
    R30 iy (iyy + wLENGTH xs) *
    R30 iz (izz + wLENGTH xs) *
    R30 t (ixx + wLENGTH xs) * ~S`;

val arm_amm0_imp = let

  val FST_single_mul = prove(``FST (single_mul x y 0w) = x * y``,SIMP_TAC std_ss [single_mul_def,WORD_ADD_0])
  val aam0_thm = (SIMP_RULE (bool_ss++SIZES_ss) [ZERO_concat_ZERO,ADD_0,WORD_ADD_0,GSYM add_thm,GSYM mul_thm] o RW [FST_single_mul] o Q.INST [`z`|->`0w`] o INST_TYPE [``:'a``|->``:32``] o GSYM) add_double_mul_cases
  val amm0_nil_lemma = prove(
    ``P * cond (xs = []) * cond (LENGTH xs = LENGTH ys) =
      P * cond ((xs = []) /\ (ys = []))``,
    REWRITE_TAC [SEP_cond_CLAUSES,GSYM STAR_ASSOC]
    \\ MATCH_MP_TAC (prove(``(x = y) ==> (P * cond x = P * cond y)``,SIMP_TAC bool_ss []))
    \\ METIS_TAC [LENGTH_NIL])
  val arm_aam0_SIMP = BASIC_arm_SIMP [arm_amm0_post_def,arm_amm0_pre_def,ms_def] [mw_add_mul_mult0_cases];  

  (* step 1: get basic spec (partly auto-generate code) *)
  (* make_spec ["ldr  x,[ix],#4","ldr  y,[iy],#4","umull v,z,x,p","mov  x,#0","umlal x,z,y,q","adds z,z,c","str  z,[iz],#4","adcs b,v,b","mov  v,#0","adcs y,v,#0","adds c,x,b","adcs b,y,#0"] *)
  val th = (*  ldr  x,[ix],#4  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`x`,`b`|->`ix`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  ldr  y,[iy],#4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`y`,`b`|->`iy`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4` `(x4)*(x1*x2*x3)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  umull v,z,x,p   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c'`|->`v`,`c`|->`z`,`a`|->`x`,`b`|->`p`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3`,`z'`|->`z'3` ] arm_UMULL4))) `x1*x2*x3*x4*x5*x6*x7` `(x4*x5)*(x1*x2*x3*x6*x7)` `x1*x2*x3*x4*x5` `(x5*x1)*(x2*x3*x4)`
  val th = (*  mov  x,#0       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`x`,`a_mode`|->`Imm 0w`,`x`|->`x4` ] arm_MOV1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10` `(x1*x5)*(x2*x3*x4*x6*x7*x8*x9*x10)` `x1*x2` `(x1*x2)*(emp)`
  val th = (*  umlal x,z,y,q   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c'`|->`x`,`c`|->`z`,`a`|->`y`,`b`|->`q`,`x`|->`x5`,`y`|->`y5`,`z`|->`z5`,`z'`|->`z'5` ] arm_UMLAL4))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10` `(x1*x2*x4*x6)*(x3*x5*x7*x8*x9*x10)` `x1*x2*x3*x4*x5` `(x4*x5*x3*x1)*(x2)`
  val th = (*  adds z,z,c      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`z`,`b`|->`c`,`a_mode`|->`OneReg`,`x`|->`x6`,`y`|->`y6` ] arm_ADD2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11` `(x3*x5)*(x1*x2*x4*x6*x7*x8*x9*x10*x11)` `x1*x2*x3` `(x1*x3)*(x2)`
  val th = (*  str  z,[iz],#4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`z`,`b`|->`iz`,`imm`|->`4w`,`x`|->`x7`,`y`|->`y7`,`z`|->`z7` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12` `(x1*x3)*(x2*x4*x5*x6*x7*x8*x9*x10*x11*x12)` `x1*x2*x3*x4` `(x1*x4)*(x2*x3)`
  val th = (*  adcs b,v,b      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`v`,`a_mode`|->`OneReg`,`x`|->`x8`,`y`|->`y8` ] arm_ADC2))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14` `(x4*x10)*(x1*x2*x3*x5*x6*x7*x8*x9*x11*x12*x13*x14)` `x1*x2*x3` `(x3*x1)*(x2)`
  val th = (*  mov  v,#0       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x9` ] arm_MOV1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x1*x3)*(x2*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15)` `x1*x2` `(x1*x2)*(emp)`
  val th = (*  adcs y,v,#0     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`y`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x10`,`y`|->`y10` ] arm_ADC2))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x1*x2*x8)*(x3*x4*x5*x6*x7*x9*x10*x11*x12*x13*x14*x15)` `x1*x2*x3` `(x1*x3*x2)*(emp)`
  val th = (*  adds c,x,b      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`x`,`a_mode`|->`OneReg`,`x`|->`x11`,`y`|->`y11`,`z`|->`z11` ] arm_ADD3))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x3*x4*x8*x10)*(x1*x2*x5*x6*x7*x9*x11*x12*x13*x14*x15)` `x1*x2*x3*x4` `(x4*x2*x3*x1)*(emp)`
  val th = (*  adcs b,y,#0     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`y`,`a_mode`|->`Imm 0w`,`x`|->`x12`,`y`|->`y12` ] arm_ADC2))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x2*x4*x6)*(x1*x3*x5*x7*x8*x9*x10*x11*x12*x13*x14*x15)` `x1*x2*x3` `(x2*x3*x1)*(emp)`
  val th = ALIGN_VARS ["y7","y2","y1"] (AUTO_HIDE_STATUS th)
  val th = INST [``b:word32``|->``bx:word32``] (RW [WORD_ADD_0,aam0_thm] th)
  val th = AUTO_HIDE_POST1 [`R x`,`R z`,`R y`,`R v`] th
  val th = AUTO_HIDE_PRE [`R x`,`R z`,`R y`,`M y7`,`R v`] th
  val th = Q.INST [`y1`|->`ixx`,`y2`|->`iyy`,`z1`|->`xx`,`z2`|->`yx`,`y3`|->`px`,`y5`|->`qx`,`y6`|->`cx`,`y8`|->`bx`,`y7`|->`izz`] th
  val th = APP_FRAME `ms (ixx + 1w) xs * ms (iyy + 1w) ys * blank_ms (izz + 1w) (LENGTH xs)` th
  val th = MOVE_POST1 `S` (MOVE_POST1 `R30 ix` th)

  (* step 2: fix first post *)
  val th = MATCH_COMPOSE (APP_FRAME `R30 t (ixx + wLENGTH ((x:word32)::xs))` th) TEQ_BNE2
  val th = DISCH ``LENGTH (xs:word32 list) < 2**30`` th
  val th = UNDISCH (SIMP_RULE bool_ss [ONE_EQ_wLENGTH] th)
  val th = APP_FRAME `cond (LENGTH (xs:word32 list) = LENGTH (ys:word32 list))` th  
  val th = (arm_aam0_SIMP o RW [amm0_nil_lemma] o SPEC_WEAKEN1 th)
    `arm_amm0_post x ix ixx (xx::xs) y iy iyy (yx::ys) z iz izz p px q qx v t b bx c cx`
  val th = (arm_aam0_SIMP o SIMP_RULE std_ss [MAP,blank_ms_def]) th
  
  (* step 3: fix pre *)
  val th1 = (arm_aam0_SIMP o SPEC_STRENGTHEN th)
    `arm_amm0_pre x ix ixx (xx::xs) y iy iyy (yx::ys) z iz izz p px q qx v t b bx c cx`
  val th1 = (arm_aam0_SIMP o RW [RW [ADD1] blank_ms_def]) th1
  val th = DISCH_ELIM_xs_ASSUM arm_amm0_pre_def `ixx` `xx` th1

  (* step 4: show that second post satisfies the precondition *)
  val th1 = (arm_aam0_SIMP o SPEC_WEAKEN th)
    `arm_amm0_pre x ix (ixx+1w) xs y iy (iyy+1w) ys z iz (izz+1w) p px q qx v t b 
       (SND (SND (add_double_mul xx yx px qx cx bx 0w))) c 
       (FST (SND (add_double_mul xx yx px qx cx bx 0w))) *
     (M izz (FST (add_double_mul xx yx px qx cx bx 0w)) * M ixx xx * M iyy yx)`
  val th = CLOSE_LOOP th1
 
  (* step 5: instantiate induction and extract ind hyp *)
  val tm = extract_spec th [(`xx::xs`,`xs`),(`yx::ys`,`ys`)] [`ixx`,`iyy`,`izz`] [`xs`,`ys`,`px`,`qx`,`cx`,`bx`]
  val th1 = SIMP_RULE bool_ss [EXPAND_PAIR,GSYM AND_IMP_INTRO] (ISPEC tm mw_add_mul_mult0_ind)
  val th1 = n_times 3 (delete_fst_case [arm_amm0_pre_def]) th1
  val th1 = rename_foralls ["xx","xs","yx","ys","px","qx","cx","bx"] th1
  val asm = extract_assum th1

  (* step 6: match step and prove postcondition *)
  val asm = MATCH_MP ARM_PROG_COMPOSE_WEAKEN asm
  val th = arm_aam0_SIMP (MATCH_MP asm th)

  (* step 7: clean up *)
  val th = MATCH_MP th1 (tidy_up th1 th)
  val th = (SPEC_ALL o Q.SPECL [`xs`,`ys`,`px`,`qx`,`bx`,`cs`]) th

  in th end;

val STAR_cond_EQ_STAR_cond = prove(``!P Q g. (P * cond g = Q * cond g) = g ==> (P = Q)``,Cases_on `g` \\ REWRITE_TAC [SEP_cond_CLAUSES,emp_STAR,F_STAR])
val SEP_IMP_cond_emp = prove(``SEP_IMP (cond g) emp``,SIMP_TAC std_ss [SEP_IMP_def,emp_def,cond_def])
val mw_monmult5_step_lemma = prove(``
  !xs ys a. M (a + wLENGTH ys) x * (ms a xs * cond (LENGTH ys = LENGTH xs)) = 
            ms a (xs ++ [x]) * cond (LENGTH (ys:word32 list) = LENGTH (xs:word32 list))``,
  REWRITE_TAC [STAR_ASSOC,STAR_cond_EQ_STAR_cond] \\ Induct
  \\ SIMP_TAC bool_ss [wLENGTH_def,ms_def,APPEND,LENGTH,WORD_ADD_0,emp_STAR]
  \\ STRIP_TAC \\ Cases \\ REWRITE_TAC [LENGTH,DECIDE ``~(0 = SUC n)``]
  \\ REWRITE_TAC [RW1[ADD_COMM]ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC,EQ_ADD_LCANCEL]
  \\ MOVE_STAR_TAC `m*(m1*m2)` `m1*(m*m2)`
  \\ ASM_SIMP_TAC bool_ss [GSYM wLENGTH_def]);

val mw_monmult5_step_imp = let

  val m00_thm = (SIMP_RULE (bool_ss++SIZES_ss) [ADD_0,WORD_ADD_0,GSYM add_thm,GSYM mul_thm] o INST_TYPE [``:'a``|->``:32``] o GSYM) add_double_mul_00_cases

  (* spec for init *)
  (* make_spec ["ldr  z,[sp]","ldr  b,[iz],#4","ldr  x,[ix],#4","ldr  y,[iy],#4","mov  v,#0","umlal v,b,x,p","mov  c,#0","mul  q,b,z","umlal c,b,y,q","adds c,c,v","mov  v,#0","adcs b,v,#0"] *)
  val th = (*  ldr  z,[sp]     *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`z`,`b`|->`13w`,`imm`|->`0w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  ldr  b,[iz],#4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`b`,`b`|->`iz`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4` `(x4)*(x1*x2*x3)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  ldr  x,[ix],#4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`x`,`b`|->`ix`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7` `(x4)*(x1*x2*x3*x5*x6*x7)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  ldr  y,[iy],#4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`y`,`b`|->`iy`,`imm`|->`4w`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10` `(x4)*(x1*x2*x3*x5*x6*x7*x8*x9*x10)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  mov  v,#0       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x5` ] arm_MOV1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13` `(x4)*(x1*x2*x3*x5*x6*x7*x8*x9*x10*x11*x12*x13)` `x1*x2` `(x2)*(x1)`
  val th = (*  umlal v,b,x,p   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c'`|->`v`,`c`|->`b`,`a`|->`x`,`b`|->`p`,`x`|->`x6`,`y`|->`y6`,`z`|->`z6`,`z'`|->`z'6` ] arm_UMLAL4))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14` `(x1*x2*x6*x9)*(x3*x4*x5*x7*x8*x10*x11*x12*x13*x14)` `x1*x2*x3*x4*x5` `(x4*x5*x1*x3)*(x2)`
  val th = (*  mov  c,#0       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`c`,`a_mode`|->`Imm 0w`,`x`|->`x7` ] arm_MOV1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x5)*(x1*x2*x3*x4*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15)` `x1*x2` `(x2)*(x1)`
  val th = (*  mul  q,b,z      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`q`,`a`|->`b`,`b`|->`z`,`x`|->`x8`,`y`|->`y8`,`z`|->`z8` ] arm_MUL3))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16` `(x2*x5*x14)*(x1*x3*x4*x6*x7*x8*x9*x10*x11*x12*x13*x15*x16)` `x1*x2*x3*x4` `(x4*x1*x2)*(x3)`
  val th = (*  umlal c,b,y,q   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c'`|->`c`,`c`|->`b`,`a`|->`y`,`b`|->`q`,`x`|->`x9`,`y`|->`y9`,`z`|->`z9`,`z'`|->`z'9` ] arm_UMLAL4))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16*x17` `(x1*x3*x4*x5*x9)*(x2*x6*x7*x8*x10*x11*x12*x13*x14*x15*x16*x17)` `x1*x2*x3*x4*x5` `(x3*x2*x5*x4*x1)*(emp)`
  val th = (*  adds c,c,v      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`c`,`b`|->`v`,`a_mode`|->`OneReg`,`x`|->`x10`,`y`|->`y10` ] arm_ADD2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16*x17` `(x4*x5*x9)*(x1*x2*x3*x6*x7*x8*x10*x11*x12*x13*x14*x15*x16*x17)` `x1*x2*x3` `(x1*x3*x2)*(emp)`
  val th = (*  mov  v,#0       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x11` ] arm_MOV1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16*x17` `(x2*x3)*(x1*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16*x17)` `x1*x2` `(x1*x2)*(emp)`
  val th = (*  adcs b,v,#0     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x12`,`y`|->`y12` ] arm_ADC2))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16*x17` `(x1*x2*x6)*(x3*x4*x5*x7*x8*x9*x10*x11*x12*x13*x14*x15*x16*x17)` `x1*x2*x3` `(x1*x3*x2)*(emp)`
  val th = ALIGN_VARS ["y4","y3","y2","y1"] (AUTO_HIDE_STATUS th)
  val th = RW [WORD_ADD_0,m00_thm] th
  val th = RW [mul_thm,single_mul_def,FST] th
  val th = AUTO_HIDE_PRE [`R z`,`R b`,`R x`,`R y`,`R q`,`R c`,`R v`] th
  val th1 = Q.INST [`y1`|->`sp`,`y2`|->`izz`,`y3`|->`ixx`,`y4`|->`iyy`,`z1`|->`px`,`z2`|->`zx`,`z3`|->`xx`,`z4`|->`yx`,`y6`|->`ux`] th
  val th1 = AUTO_HIDE_POST1 [`R x`,`R y`,`R z`,`M izz`] th1

  (* compose with spec for mw_mul_mult *)
  val th2 = RW [arm_amm_pre_def] arm_amm_imp   
  val th2 = MATCH_INST1 [`R p`] th1 th2
  val th2 = MATCH_INST1 [`R b`,`R c`,`R30 ix`,`R30 iy`,`R q`] th1 th2
  val thx = FRAME_COMPOSE th1 th2
  val thy = RW [arm_amm_post_def] thx
  val thy = AUTO_HIDE_POST1 [`R p`] thy

  (* finalisation *)
  (* make_spec ["ldr z,[sp,#-28]","ldr p,[sp,#4]","adds z,z,c","str z,[iz,#-4]","adc c,b,#0","sub ix,ix,p","sub iy,iy,p","sub iz,iz,p"] *)
  val th = (*  ldr z,[sp,#-28]  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (28w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`a`|->`z`,`b`|->`13w`,`imm`|->`28w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  ldr p,[sp,#4]    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`p`,`b`|->`13w`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4` `(x2*x4)*(x1*x3)` `x1*x2*x3*x4` `(x2*x4)*(x1*x3)`
  val th = (*  adds z,z,c       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`z`,`b`|->`c`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_ADD2'))) `x1*x2*x3*x4*x5*x6` `(x4*x5)*(x1*x2*x3*x6)` `x1*x2*x3` `(x3*x1)*(x2)`
  val th = (*  str z,[iz,#-4]   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`a`|->`z`,`b`|->`iz`,`imm`|->`4w`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7` `(x1*x3)*(x2*x4*x5*x6*x7)` `x1*x2*x3*x4` `(x1*x4)*(x2*x3)`
  val th = (*  adc c,b,#0       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`c`,`a`|->`b`,`a_mode`|->`Imm 0w`,`x`|->`x5`,`y`|->`y5` ] arm_ADC2))) `x1*x2*x3*x4*x5*x6*x7*x8*x9` `(x4*x5)*(x1*x2*x3*x6*x7*x8*x9)` `x1*x2*x3` `(x3*x2)*(x1)`
  val th = (*  sub ix,ix,p      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`ix`,`b`|->`p`,`a_mode`|->`OneReg`,`x`|->`x6`,`y`|->`y6` ] arm_SUB2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10` `(x3*x7)*(x1*x2*x4*x5*x6*x8*x9*x10)` `x1*x2*x3` `(x3*x2)*(x1)`
  val th = (*  sub iy,iy,p      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`iy`,`b`|->`p`,`a_mode`|->`OneReg`,`x`|->`x7`,`y`|->`y7` ] arm_SUB2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11` `(x2*x3)*(x1*x4*x5*x6*x7*x8*x9*x10*x11)` `x1*x2*x3` `(x2*x3)*(x1)`
  val th = (*  sub iz,iz,p      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`iz`,`b`|->`p`,`a_mode`|->`OneReg`,`x`|->`x8`,`y`|->`y8` ] arm_SUB2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12` `(x2*x3*x8)*(x1*x4*x5*x6*x7*x9*x10*x11*x12)` `x1*x2*x3` `(x2*x3*x1)*(emp)`
  val th = AUTO_HIDE_PRE [`R p`,`R z`] th
  val th = ALIGN_VARS ["y1","y4","x6","z2","x7"] (AUTO_HIDE_STATUS th)
  val th = RW [WORD_ADD_0,add_thm,GSYM addr32_SUB,GSYM R30_def] th
  val th = RW [RW [ADD_0,WORD_ADD_0] (Q.INST [`c`|->`F`] add_thm)] th
  val th = RW [GSYM add_double_mul_x00_cases] th
  val th = Q.INST [`x1`|->`zx`,`x2`|->`px`,`y1`|->`sp`,`y3`|->`cx`,`y4`|->`izz`,`x5`|->`bx`,`x6`|->`ixx`,`x7`|->`iyy`,`z9`|->`ux`,`z1`|->`z'`,`z2`|->`xlen`] th
  (* make_spec ["str c,[sp,#-28]"] *)
  val th1 = (*  str c,[sp,#-28]  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (28w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`a`|->`c`,`b`|->`13w`,`imm`|->`28w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_STR_NONALIGNED))
  val th1 = ALIGN_VARS ["y1"] (AUTO_HIDE_STATUS th1)
  val th1 = Q.INST [`y1`|->`sp`,`x1`|->`FST (SND (add_double_mul 0w 0w p q cx bx z'))`,`z1`|->`z'`] th1
  val th = FRAME_COMPOSE th th1  
  val th = INST [``b:word32``|->``bx:word32``] (AUTO_HIDE_POST1 [`R b`,`R c`,`R z`] th)
  val th = Q.INST [`izz`|->`izz + wLENGTH (xs:word32 list) + 1w`] th
  val th = MOVE_POST1 `M (izz + wLENGTH xs)` (RW [WORD_ADD_SUB] th)
  val th = APP_FRAME `ms izz qs * cond (LENGTH (xs:word32 list) = LENGTH qs)` th  
  val th = RW [STAR_ASSOC] (RW [mw_monmult5_step_lemma,GSYM STAR_ASSOC] th)
  val th = AUTO_HIDE_PRE [`M (izz + wLENGTH (xs:word32 list))`] th
  val th = Q.INST [`p:word32`|->`ux`,`q:word32`|->`((xx * ux + zx) * px)`] th 
  val th = MATCH_INST1 [`R30 ix`,`R30 iy`,`R b`,`R c`,`ms izz`] thy th
  val th = FRAME_COMPOSE thy th
  val lemma = prove(``(xx * ux + zx) * px = (ux * xx + zx) * px:'a word``,METIS_TAC [WORD_MULT_COMM])
  val th = RW1 [lemma] th
  val th = RW [GSYM mw_monmult5_step_cases] th

  (* remove condition on length of mw_add_mul_mul *)
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = MATCH_MP ARM_PROG_DROP_COND1 th
  val th = APP_PART_STRENGTHEN th 
    `cond ~((xs:word32 list) = []) * cond ((LENGTH xs = LENGTH (ys:word32 list)) /\ (LENGTH ys = LENGTH (zs:word32 list)))`
    (REWRITE_TAC [SEP_cond_CLAUSES,SEP_IMP_cond,GSYM LENGTH_NIL] 
     \\ REPEAT STRIP_TAC \\ REPEAT DECIDE_TAC
     \\ IMP_RES_TAC (SIMP_RULE (std_ss++SIZES_ss) [] 
          (INST_TYPE [``:'a``|->``:32``] LENGTH_FST_mw_add_mul_mult))  
     \\ ASM_REWRITE_TAC [])
  
  (* tidy up *)
  val th = Q.INST [`xlen`|->`wLENGTH (xx::xs)`] th
  val lm = prove(``(a + 1w + wLENGTH xs = a + wLENGTH (x::xs)) /\ 
                   (a + 1w + wLENGTH xs - wLENGTH (x::xs) = a) /\ 
                   (a + wLENGTH xs + 1w - wLENGTH (x::xs) = a)``,
    REWRITE_TAC [wLENGTH_def,LENGTH,ADD1,GSYM word_add_n2w]
    \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,WORD_ADD_SUB]
    \\ REWRITE_TAC [WORD_ADD_ASSOC,WORD_ADD_SUB,WORD_SUB_PLUS]
    \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC] \\ METIS_TAC [WORD_ADD_COMM]) 
  val th = RW [lm,emp_STAR,GSYM wLENGTH_def,STAR_ASSOC] th
  val th = (RW [GSYM R30_def] o AUTO_HIDE_POST1 [`R p`,`R q`,`R v`] o RW [R30_def]) th

  in th end;


val mw_moninit_lemma = prove(
  ``!qs a x. 
      ms a qs * (cond (LENGTH qs = LENGTH xs) * M (a + wLENGTH xs) x) =
      ms a (qs ++ [x]) * cond (LENGTH qs = LENGTH xs)``,
  SIMP_TAC (bool_ss++sep2_ss) [ms_APPEND,ms_def,wLENGTH_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `LENGTH qs = LENGTH xs` 
  \\ ASM_SIMP_TAC (bool_ss++sep_ss) []);

val mw_moninit_imp = let

  val FST_single_mul = prove(``FST (single_mul x y 0w) = x * y``,SIMP_TAC std_ss [single_mul_def,WORD_ADD_0])
  val m00_thm = (SIMP_RULE (bool_ss++SIZES_ss) [ZERO_concat_ZERO,ADD_0,WORD_ADD_0,GSYM add_thm,GSYM mul_thm] o RW [FST_single_mul] o Q.INST [`z`|->`0w`] o INST_TYPE [``:'a``|->``:32``] o GSYM) add_double_mul_00_cases

  (* spec for init *)
  (* make_spec ["ldr  z,[sp]","ldr  x,[ix],#4","ldr  y,[iy],#4","umull v,b,x,p","mov  c,#0","mul  q,b,z","umlal c,b,y,q","adds c,c,v","mov  v,#0","adcs b,v,#0"] *)
  val th = (*  ldr  z,[sp]     *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`z`,`b`|->`13w`,`imm`|->`0w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  ldr  x,[ix],#4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`x`,`b`|->`ix`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4` `(x4)*(x1*x2*x3)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  ldr  y,[iy],#4  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`y`,`b`|->`iy`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7` `(x4)*(x1*x2*x3*x5*x6*x7)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  umull v,b,x,p   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c'`|->`v`,`c`|->`b`,`a`|->`x`,`b`|->`p`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4`,`z'`|->`z'4` ] arm_UMULL4))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10` `(x4*x5)*(x1*x2*x3*x6*x7*x8*x9*x10)` `x1*x2*x3*x4*x5` `(x5*x1)*(x2*x3*x4)`
  val th = (*  mov  c,#0       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`c`,`a_mode`|->`Imm 0w`,`x`|->`x5` ] arm_MOV1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13` `(x5)*(x1*x2*x3*x4*x6*x7*x8*x9*x10*x11*x12*x13)` `x1*x2` `(x2)*(x1)`
  val th = (*  mul  q,b,z      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`q`,`a`|->`b`,`b`|->`z`,`x`|->`x6`,`y`|->`y6`,`z`|->`z6` ] arm_MUL3))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14` `(x2*x5*x12)*(x1*x3*x4*x6*x7*x8*x9*x10*x11*x13*x14)` `x1*x2*x3*x4` `(x4*x1*x2)*(x3)`
  val th = (*  umlal c,b,y,q   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c'`|->`c`,`c`|->`b`,`a`|->`y`,`b`|->`q`,`x`|->`x7`,`y`|->`y7`,`z`|->`z7`,`z'`|->`z'7` ] arm_UMLAL4))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x1*x3*x4*x5*x9)*(x2*x6*x7*x8*x10*x11*x12*x13*x14*x15)` `x1*x2*x3*x4*x5` `(x3*x2*x5*x4*x1)*(emp)`
  val th = (*  adds c,c,v      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`c`,`b`|->`v`,`a_mode`|->`OneReg`,`x`|->`x8`,`y`|->`y8` ] arm_ADD2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x4*x5*x9)*(x1*x2*x3*x6*x7*x8*x10*x11*x12*x13*x14*x15)` `x1*x2*x3` `(x1*x3*x2)*(emp)`
  val th = (*  mov  v,#0       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x9` ] arm_MOV1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x2*x3)*(x1*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15)` `x1*x2` `(x1*x2)*(emp)`
  val th = (*  adcs b,v,#0     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x10`,`y`|->`y10` ] arm_ADC2))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14*x15` `(x1*x2*x6)*(x3*x4*x5*x7*x8*x9*x10*x11*x12*x13*x14*x15)` `x1*x2*x3` `(x1*x3*x2)*(emp)`
  val th = ALIGN_VARS ["y3","y2","y1"] (AUTO_HIDE_STATUS th)
  val th = RW [WORD_ADD_0,m00_thm] th
  val th = AUTO_HIDE_PRE [`R z`,`R b`,`R x`,`R y`,`R q`,`R c`,`R v`] th
  val th = AUTO_HIDE_POST1 [`R x`,`R y`,`R z`,`R v`] th
  val th1 = Q.INST [`y1`|->`sp`,`y2`|->`ixx`,`y3`|->`iyy`,`z1`|->`px`,`z2`|->`xx`,`z3`|->`yx`,`y4`|->`ux`] th

  (* compose with spec for mw_add_mul_mult *)
  val th2 = RW [arm_amm0_pre_def] arm_amm0_imp   
  val th2 = MATCH_INST1 [`R p`] th1 th2
  val th2 = MATCH_INST1 [`R b`,`R c`,`R30 ix`,`R30 iy`,`R q`] th1 th2
  val thx = FRAME_COMPOSE th1 th2
  val thy = RW [arm_amm0_post_def] thx
  val thy = AUTO_HIDE_POST1 [`R p`] thy

  (* finalisation *)
  (* make_spec ["ldr p,[sp,#4]","str c,[iz],#4","str b,[sp,#-28]","sub ix,ix,p","sub iy,iy,p","sub iz,iz,p"] *)
  val th = (*  ldr p,[sp,#4]    *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`p`,`b`|->`13w`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  str c,[iz],#4    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`c`,`b`|->`iz`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4` `(x4)*(x1*x2*x3)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  str b,[sp,#-28]  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (28w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`a`|->`b`,`b`|->`13w`,`imm`|->`28w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7` `(x4*x6)*(x1*x2*x3*x5*x7)` `x1*x2*x3*x4` `(x4*x2)*(x1*x3)`
  val th = (*  sub ix,ix,p      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`ix`,`b`|->`p`,`a_mode`|->`OneReg`,`x`|->`x4`,`y`|->`y4` ] arm_SUB2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9` `(x4*x8)*(x1*x2*x3*x5*x6*x7*x9)` `x1*x2*x3` `(x3*x2)*(x1)`
  val th = (*  sub iy,iy,p      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`iy`,`b`|->`p`,`a_mode`|->`OneReg`,`x`|->`x5`,`y`|->`y5` ] arm_SUB2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10` `(x2*x3)*(x1*x4*x5*x6*x7*x8*x9*x10)` `x1*x2*x3` `(x2*x3)*(x1)`
  val th = (*  sub iz,iz,p      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`iz`,`b`|->`p`,`a_mode`|->`OneReg`,`x`|->`x6`,`y`|->`y6` ] arm_SUB2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11` `(x2*x3*x9)*(x1*x4*x5*x6*x7*x8*x10*x11)` `x1*x2*x3` `(x2*x3*x1)*(emp)`
  val th = ALIGN_VARS ["y2","y1","z1","x4","x5"] (AUTO_HIDE_STATUS th)    
  val th = AUTO_HIDE_PRE [`R p`,`M (y1 - 7w)`,`M y2`] th
  val th = AUTO_HIDE_POST1 [`R b`,`R c`] th
  val th = MATCH_INST1 [`R30 13w`,`R30 ix`,`R30 iy`,`R30 iz`] thy th
  val th = APP_FRAME `ms izz qs * cond (LENGTH qs = LENGTH (xs:word32 list))` th
  val th = MOVE_POST1 `M (izz + wLENGTH (xs:word32 list))` th
  val th = RW1 [GSYM STAR_ASSOC] (RW1 [GSYM STAR_ASSOC] th)
  val th = SIMP_RULE (bool_ss++sep2_ss) [] (RW [mw_moninit_lemma] th)
  val th = MATCH_MP ARM_PROG_DROP_COND1 th
  val th = MATCH_INST1 [`R b`,`R c`,`ms izz`] thy th
  val th = FRAME_COMPOSE thy th  
  val lemma = prove(``(xx * ux + zx) * px = (ux * xx + zx) * px:'a word``,METIS_TAC [WORD_MULT_COMM])
  val rw = (RW1 [lemma] o GSYM) mw_monmult5_step_cases
  val rw = (RW [WORD_ADD_0] o Q.INST [`zs`|->`(MAP (\x.0w) xs)`,`z`|->`0w`,`z'`|->`0w`]) rw
  val rw = RW [FST,SND,add_double_mul_000,mw_add_mul_mult0_spec] rw
  val th = RW [rw] th
  val th = AUTO_HIDE_POST1 [`R q`] th
  val th = RW [GSYM (SIMP_CONV bool_ss [MAP] ``MAP (\x.0w) (xx::xs)``)] th
  val th = RW [GSYM mw_moninit_def,GSYM WORD_ADD_ASSOC] th
  val th = RW [word_add_n2w,GSYM ADD1,GSYM (RW1[ADD_COMM]ADD1)] th
  val th = MOVE_PRE `M (izz + n2w (LENGTH xs))` (MOVE_PRE `blank_ms izz` th)
  val lemma = prove(
    ``!n a P. P * blank_ms a n * ~M (a + n2w n) = P * blank_ms a (SUC n)``,
    Induct THEN1 REWRITE_TAC [blank_ms_def,emp_STAR,WORD_ADD_0]
    \\ ONCE_REWRITE_TAC [blank_ms_def] \\ MOVE_STAR_TAC `p*(m*b)*n`  `m*(p*b*n)`
    \\ REWRITE_TAC [RW1[ADD_COMM]ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]  
    \\ ASM_REWRITE_TAC [RW1[ADD_COMM]ADD1] \\ SIMP_TAC (bool_ss++star_ss) [])
  val th = RW [lemma,GSYM (REWRITE_CONV [LENGTH] ``LENGTH (xx::xs)``)] th
  val th = Q.INST [`z1`|->`n2w (LENGTH (xx:word32::xs))`] th
  val th = RW [WORD_ADD_SUB,R30_def] th
  val th = RW [GSYM R30_def] (AUTO_HIDE_POST1 [`R p`] th)
  
  (* remove condition on length of mw_add_mul_mul *)
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = APP_PART_STRENGTHEN th 
    `cond (1 < LENGTH (xx:word32::xs) /\ (LENGTH (xx::xs) = LENGTH (yx::ys:word32 list)))`
    (REWRITE_TAC [SEP_cond_CLAUSES,SEP_IMP_cond,GSYM LENGTH_NIL] 
     \\ REWRITE_TAC [LENGTH,ADD1,EQ_ADD_RCANCEL]
     \\ REPEAT STRIP_TAC \\ REPEAT DECIDE_TAC
     \\ `LENGTH (ys:word32 list) = LENGTH (MAP (\x.0w:word32) (xs:word32 list))` by ASM_REWRITE_TAC [LENGTH_MAP]
     \\ IMP_RES_TAC (SIMP_RULE (std_ss++SIZES_ss) [] 
          (INST_TYPE [``:'a``|->``:32``] LENGTH_FST_mw_add_mul_mult))  
     \\ ASM_REWRITE_TAC [GSYM mw_add_mul_mult0_spec])

  (* quantify variables *)
  fun ms_combine f t1 t2 = RW [GSYM ms_def] o RW1 [GSYM STAR_ASSOC] o f t2 o f t1
  val th = ms_combine MOVE_PRE `M iyy` `ms (iyy+1w)` th
  val th = ms_combine MOVE_PRE `M ixx` `ms (ixx+1w)` th
  val th = ms_combine MOVE_POST1 `M iyy` `ms (iyy+1w)` th
  val th = ms_combine MOVE_POST1 `M ixx` `ms (ixx+1w)` th
  val th = CONS_GENL [`xx::xs`,`yx::ys`] th  
  val th = SIMP_RULE (bool_ss++sep2_ss) [GSYM LENGTH_NIL,GSYM ARM_PROG_MOVE_COND] th
  val th = APP_PART_STRENGTHEN th 
    `cond (1 < LENGTH xs /\ (LENGTH (xs:word32 list) = LENGTH (ys:word32 list)))`
    (REWRITE_TAC [SEP_IMP_cond] \\ DECIDE_TAC)

  in th end;


val arm_mm5_pre_def = Define `
  arm_mm5_pre p b c v q x y z sp t tt z' us xs ys zs iu ix iy iz iuu ixx iyy izz px P = 
      R30 iu iuu * R30 ix ixx * R30 iy iyy * R30 iz izz * R30 13w sp * 
      ~R z * ~R p * ~R b * ~R x * ~R y * ~R q * ~R c * ~R v *
      P * ms ixx xs * ms iyy ys * ms izz zs * 
      M sp px * M (sp - 7w) z' * M (sp + 1w) (addr32 (wLENGTH xs)) *
      R30 tt (ixx + wLENGTH xs) * R30 t (iuu + wLENGTH us) * ~S * 
      cond (LENGTH us <= LENGTH xs /\ (LENGTH xs = LENGTH ys) /\ 
            (LENGTH ys = LENGTH zs) /\ 1 < LENGTH xs /\ 0 < LENGTH us /\ 
            SEP_CONTAINS (ms iuu us) (P * ms ixx xs))`;

val arm_mm5_post_def = Define `
  arm_mm5_post p b c v q x y z sp t tt z' us xs ys zs iu ix iy iz iuu ixx iyy izz px P = 
      R30 iz izz * R30 iy iyy * R30 ix ixx * R30 13w sp *
      ms izz (FST (mw_monmult5 us xs ys px zs z')) *
      M (sp - 7w) (SND (mw_monmult5 us xs ys px zs z')) *
      ~R b * ~R c * ~R z * ~R x * ~R y * ~R p * ~R q * ~R v *
      M sp px * M (sp + 1w) (addr32 (wLENGTH xs)) *
      R30 tt (ixx + wLENGTH xs) * P * ms ixx xs * ms iyy ys * 
      R30 iu (iuu + wLENGTH us) * R30 t (iuu + wLENGTH us) * ~S`;

val ARM_PROG_CONTAINS = prove(
  ``ARM_PROG (P1 * P2) code C (Q * P2) {} ==>
    !P. ARM_PROG (P1 * P * cond (SEP_CONTAINS P2 P)) code C (Q * P) {}``,
  REWRITE_TAC [SEP_CONTAINS_def,ARM_PROG_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ IMP_RES_TAC ARM_PROG_FRAME 
  \\ FULL_SIMP_TAC bool_ss [STAR_ASSOC,setSTAR_CLAUSES]);

val ARM_PROG_CONTAINS_TAIL = prove(
  ``ARM_PROG P code C Q ((Z * cond (SEP_CONTAINS (ms a (x::xs)) PP),f) INSERT QQ) ==>
    ARM_PROG P code C Q ((Z * cond (SEP_CONTAINS (ms (a+1w) xs) PP),f) INSERT QQ)``,
  (MATCH_MP_TAC o GEN_ALL o RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_COMM] o 
   RW [AND_IMP_INTRO] o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL)
       ARM_PROG_PART_WEAKEN_POST
  \\ REWRITE_TAC [SEP_IMP_cond,SEP_CONTAINS_def,ms_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `M a x * F'` \\ ASM_SIMP_TAC (bool_ss++star_ss) []);
  
val mw_monmult5_imp = let

  val arm_mm5_SIMP = BASIC_arm_SIMP [arm_mm5_pre_def,arm_mm5_post_def] [mw_monmult5_cases];  

  (* compose first instruction *)
  val th = (*  ldr  p,[iu],#4  *) FST_PROG2 (SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`p`,`b`|->`iu`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED)) 
  val th = (AUTO_HIDE_PRE [`R p`] o ALIGN_VARS ["y1"] o AUTO_HIDE_STATUS) th
  val th = Q.INST [`y1`|->`iuu`,`z1`|->`ux`] th
  val th = MOVE_POST1 `M iuu` (MOVE_PRE `M iuu` th)
  val th = APP_FRAME `ms (iuu+1w) us` th
  val th = RW [GSYM ms_def] (RW1 [GSYM STAR_ASSOC] th)
  val th = Q.SPEC `P * ms ixx (xx::xs)` (MATCH_MP ARM_PROG_CONTAINS th)
  val th = RW [STAR_ASSOC,ms_def] th
  val th = FRAME_COMPOSE th (Q.INST [`t`|->`tt`] mw_monmult5_step_imp)
  val th = MOVE_POST1 `R30 iu` th
  val th = MOVE_POST1 `S` th

  (* step 2: fix first post *)
  val th = APP_FRAME `R30 t (iuu + wLENGTH ((ux:word32)::us))` th
  val th = MATCH_COMPOSE th TEQ_BNE2
  val th = DISCH ``LENGTH (us:word32 list) < 2**30`` th
  val th = UNDISCH (SIMP_RULE bool_ss [ONE_EQ_wLENGTH,WORD_ADD_SUB] th)
  val th = APP_FRAME `cond (LENGTH (us:word32 list) <= LENGTH (xs:word32 list) /\ (LENGTH (xs:word32 list) = LENGTH (ys:word32 list)) /\ (LENGTH ys = LENGTH (zs:word32 list))) * cond (SEP_CONTAINS ((ms iuu (ux::us)):'a ARMset -> bool) (P * ms ixx (xx::xs)))` th
  val th = MATCH_MP ARM_PROG_CONTAINS_TAIL (RW [STAR_ASSOC] th)
  val th = (RW [mw_monmult5_cases,SEP_IMP_REFL] o arm_mm5_SIMP o SPEC_WEAKEN1 th)
    `arm_mm5_post p b c v q x y z sp t tt z' (ux::us) (xx::xs) (yx::ys) (zx::zs) iu ix iy iz iuu ixx iyy izz px P`

  (* step 3: fix pre *)
  val th = DISCH ``1 < LENGTH (xx::xs:word32 list)`` th
  val th = SIMP_RULE (bool_ss++sep_ss) [GSYM LENGTH_NIL,DECIDE ``1<SUC n ==> ~(n = 0)``,LENGTH] th
  val th1 = (UNDISCH o DECIDE)
    ``LENGTH xs < 2**30 /\ LENGTH us <= LENGTH (xs:word32 list) ==> LENGTH (us:word32 list) < 2**30``  
  val th = DISCH_ALL (MP (DISCH_ALL th) th1)
  val th = RW [GSYM ARM_PROG_MOVE_COND] (UNDISCH (RW [GSYM AND_IMP_INTRO] th))
  val th = (arm_mm5_SIMP o SPEC_STRENGTHEN th)
    `arm_mm5_pre p b c v q x y z sp t tt z' (ux::us) (xx::xs) (yx::ys) (zx::zs) iu ix iy iz iuu ixx iyy izz px P`
  val th = SEP_IMP_RULE (SIMP_CONV (bool_ss++sep_ss) []) th
  val th = DISCH_ELIM_xs_ASSUM' arm_mm5_pre_def `ixx` `xx` `ms ixx` th

  (* step 4: show that second post satisfies the precondition *)
  val th1 = (arm_mm5_SIMP o SPEC_WEAKEN th)
    `arm_mm5_pre p b c v q x y z sp t tt 
       (SND (mw_monmult5_step (xx::xs) (yx::ys) (zx::zs) z' ux px)) us (xx::xs) (yx::ys) 
       (FST (mw_monmult5_step (xx::xs) (yx::ys) (zx::zs) z' ux px)) iu ix iy iz 
       (iuu+1w) ixx iyy izz px P`

  val th = SIMP_RULE (bool_ss++sep2_ss) [] (RW [GSYM SEP_IMP_MOVE_COND] th1)
  val th = APP_PART_STRENGTHEN (RW [GSYM ARM_PROG_MOVE_COND] th) `emp`
    (REWRITE_TAC [SEP_IMP_emp,cond_EMPTY] \\ MATCH_MP_TAC SEP_IMP_STAR
     \\ REWRITE_TAC [SEP_IMP_REFL,SEP_IMP_cond] \\ REPEAT STRIP_TAC \\ REPEAT DECIDE_TAC
     \\ ASM_SIMP_TAC bool_ss [LENGTH_FST_mw_monmult5_step] \\ ASM_REWRITE_TAC [LENGTH,ADD1])
  val th = RW [emp_STAR] th 
  val th = CLOSE_LOOP th

  (* step 5: instantiate induction and extract ind hyp *)
  val tm = extract_spec th [(`ux::us`,`us`),(`xx::xs`,`xs`),(`yx::ys`,`ys`),(`zx::zs`,`zs`)] [`iuu`,`ixx`,`iyy`,`izz`] [`us`,`xs`,`ys`,`px`,`zs`,`z'`]
  val th1 = SIMP_RULE bool_ss [EXPAND_PAIR,GSYM AND_IMP_INTRO] (ISPEC tm mw_monmult5_ind)
  val th1 = n_times 4 (delete_fst_case [arm_mm5_pre_def]) th1
  val th1 = rename_foralls ["ux","us","xx","xs","yx","ys","px","zx","zs","z'"] th1
  val asm = extract_assum th1

  (* step 6: match step and prove postcondition *)
  val asm = MATCH_MP ARM_PROG_COMPOSE_WEAKEN asm
  val asm = RW [emp_STAR] (Q.INST [`Q2`|->`emp`] asm)
  val th = arm_mm5_SIMP (MATCH_MP asm th)

  (* step 7: clean up *)
  val th = MATCH_MP th1 (tidy_up th1 th)
  val th = (SPEC_ALL o Q.SPECL [`us`,`xs`,`ys`,`px`,`zs`,`z'`]) th

  in th end;

val final_select = let
  val th = (*  movcc t,iz   *) SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`b`|->`t`,`a`|->`iz`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_MOV2))
  val th = (*  movcc iz,ix  *) MOVE_COMPOSE th (SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`b`|->`iz`,`a`|->`ix`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_MOV2))) `x1` `(x1)*(emp)` `x1*x2` `(x1)*(x2)`
  val th = (*  movcc ix,t   *) MOVE_COMPOSE th (SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`b`|->`ix`,`a`|->`t`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_MOV2))) `x1` `(x1)*(emp)` `x1*x2` `(x1)*(x2)`
  val th = (SIMP_RULE (bool_ss++sep2_ss) [] o APP_FRAME `cond sC` o AUTO_HIDE_STATUS) th
  val th = APP_FRAME `ms izz zs` th
  val th = APP_PART_WEAKEN1 th `blank_ms izz (LENGTH (zs:word32 list))` (REWRITE_TAC [SEP_IMP_ms_blank_ms])
  val th = APP_FRAME `R30 ix ixx * ms ixx xs * R30 iz izz * ~R t * cond (LENGTH (xs:word32 list) = LENGTH (zs:word32 list))` th
  val th = APP_WEAKEN1 th `Rms ix (if sC then xs else zs) * Rblank iz (LENGTH (xs:word32 list)) * ~R t * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,Rms_def]
    \\ SIMP_TAC (bool_ss++sep2_ss) [Rblank_def]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] 
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `ixx` \\ Q.EXISTS_TAC `izz` 
    \\ FULL_SIMP_TAC bool_ss [AC STAR_ASSOC STAR_COMM])
  val th1 = APP_STRENGTHEN th `R30 ix ixx * ms ixx xs * R30 iz izz * ms izz zs * ~R t * S (sN,sZ,sC,sV) * cond (LENGTH (xs:word32 list) = LENGTH (zs:word32 list)) * cond sC`
    (SIMP_TAC bool_ss [AC STAR_ASSOC STAR_COMM,SEP_IMP_REFL])
  val th = (*  movcc t,iz   *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`b`|->`t`,`a`|->`iz`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_MOV2))
  val th = (*  movcc iz,ix  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`b`|->`iz`,`a`|->`ix`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_MOV2))) `x1*x2*x3` `(x1*x3)*(x2)` `x1*x2*x3*x4` `(x2*x3)*(x1*x4)`
  val th = (*  movcc ix,t   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`b`|->`ix`,`a`|->`t`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_MOV2))) `x1*x2*x3*x4` `(x1*x3*x4)*(x2)` `x1*x2*x3*x4` `(x2*x3*x1)*(x4)`
  val th = (SIMP_RULE (bool_ss++sep2_ss) [] o APP_FRAME `cond ~sC` o AUTO_HIDE_STATUS) th
  val th = AUTO_HIDE_PRE [`R t`] (AUTO_HIDE_POST1 [`R t`] th)
  val th = Q.INST [`x1`|->`izz`,`x2`|->`ixx`] th
  val th = APP_FRAME `ms ixx xs` (ALIGN_VARS ["ixx","izz"] th)
  val th = APP_PART_WEAKEN1 th `blank_ms ixx (LENGTH (xs:word32 list))` (REWRITE_TAC [SEP_IMP_ms_blank_ms])
  val th = APP_FRAME `ms izz zs * cond (LENGTH (xs:word32 list) = LENGTH (zs:word32 list))` th
  val th = APP_WEAKEN1 th `Rms ix (if sC then xs else zs) * Rblank iz (LENGTH (xs:word32 list)) * ~R t * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,Rms_def] 
    \\ SIMP_TAC (bool_ss++sep2_ss) [Rblank_def]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] 
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `izz` \\ Q.EXISTS_TAC `ixx` 
    \\ FULL_SIMP_TAC bool_ss [AC STAR_ASSOC STAR_COMM])
  val th2 = APP_STRENGTHEN th `R30 ix ixx * ms ixx xs * R30 iz izz * ms izz zs * ~R t * S (sN,sZ,sC,sV) * cond (LENGTH (xs:word32 list) = LENGTH (zs:word32 list)) * cond ~sC`
    (SIMP_TAC bool_ss [AC STAR_ASSOC STAR_COMM,SEP_IMP_REFL])
  val th = APP_MERGE (Q.INST [`iz'`|->`iz`,`ix'`|->`ix`,`t'`|->`t`] th1) th2
  val th = RW [DECIDE ``b \/ ~b:bool``,SEP_cond_CLAUSES,emp_STAR] th
  in th end;

val monprod6_tail = let
  (* make_spec ["sub tt,tt,ix","ldr v,[sp,#-28]","add t,iz,tt","ldr z,[iz],#4","ldr y,[iy],#4","sub iu,iu,tt","subs z,z,y","str z,[ix],#4"] *)
  val th = (*  sub tt,tt,ix     *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`tt`,`b`|->`ix`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_SUB2'))
  val th = (*  ldr v,[sp,#-28]  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (28w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`a`|->`v`,`b`|->`13w`,`imm`|->`28w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3` `(x3)*(x1*x2)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  add t,iz,tt      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`t`,`a`|->`iz`,`b`|->`tt`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_ADD3))) `x1*x2*x3*x4*x5*x6` `(x4*x5)*(x1*x2*x3*x6)` `x1*x2*x3*x4` `(x4*x2)*(x1*x3)`
  val th = (*  ldr z,[iz],#4    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`z`,`b`|->`iz`,`imm`|->`4w`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7*x8` `(x1*x4)*(x2*x3*x5*x6*x7*x8)` `x1*x2*x3*x4` `(x2*x4)*(x1*x3)`
  val th = (*  ldr y,[iy],#4    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`y`,`b`|->`iy`,`imm`|->`4w`,`x`|->`x5`,`y`|->`y5`,`z`|->`z5` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10` `(x4)*(x1*x2*x3*x5*x6*x7*x8*x9*x10)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  sub iu,iu,tt     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`iu`,`b`|->`tt`,`a_mode`|->`OneReg`,`x`|->`x6`,`y`|->`y6` ] arm_SUB2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13` `(x4*x8)*(x1*x2*x3*x5*x6*x7*x9*x10*x11*x12*x13)` `x1*x2*x3` `(x3*x2)*(x1)`
  val th = (*  subs z,z,y       *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`z`,`b`|->`y`,`a_mode`|->`OneReg`,`x`|->`x7`,`y`|->`y7` ] arm_SUB2'))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14` `(x3*x4*x7)*(x1*x2*x5*x6*x8*x9*x10*x11*x12*x13*x14)` `x1*x2*x3` `(x3*x2*x1)*(emp)`
  val th = (*  str z,[ix],#4    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`z`,`b`|->`ix`,`imm`|->`4w`,`x`|->`x8`,`y`|->`y8`,`z`|->`z8` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13*x14` `(x1*x3*x14)*(x2*x4*x5*x6*x7*x8*x9*x10*x11*x12*x13)` `x1*x2*x3*x4` `(x1*x4*x2)*(x3)`
  val th = RW [RW [] (Q.INST [`c`|->`T`] sub_thm)] (ALIGN_VARS ["y1","y5","x3","y2","x1","x6"] th)
  val th = (AUTO_HIDE_PRE [`R t`,`R z`,`R y`,`R v`] o AUTO_PRE_HIDE_STATUS) th
  val th = (HIDE_POST1 o RW [GSYM S_carry_def] o MOVE_POST1 `S`) th  
  val th = Q.INST [`x1`|->`ixx+ttx`,`y1`|->`ixx`,`y2`|->`sp`,`z2`|->`z'`,`x3`|->`izz`,`x6`|->`iuu+ttx`,`z8`|->`xx`,`z4`|->`zx`,`y5`|->`iyy`,`z5`|->`yx`] th
  val th = AUTO_HIDE_POST1 [`M (sp - 7w)`,`R y`,`R z`] (RW [WORD_ADD_SUB2,WORD_ADD_SUB] th)
  val th = RW [WORD_ADD_ASSOC] (Q.INST [`ttx`|->`1w + wLENGTH (zs:word32 list)`] th)
  val th1 = Q.INST [`i`|->`iz`,`ix`|->`izz+1w`,`xs`|->`zs`,`j`|->`iy`,`jx`|->`iyy+1w`,`k`|->`ix`,`kx`|->`ixx+1w`,`a`|->`x`,`b`|->`y`,`c`|->`SND (single_sub zx (yx:word32) T)`] (RW [arm_sub_pre_def,arm_sub_post_def] arm_sub_imp)
  val th = FRAME_COMPOSE th th1    
  fun ms_combine f t1 t2 = RW [GSYM ms_def] o RW1 [GSYM STAR_ASSOC] o f t2 o f t1
  val th = ms_combine MOVE_POST1 `M iyy` `ms (iyy+1w)` th
  val th = ms_combine MOVE_POST1 `M izz` `ms (izz+1w)` th
  val th = ms_combine MOVE_POST1 `M ixx` `ms (ixx+1w)` th
  val th = RW [STAR_ASSOC] th     
  val th = ms_combine MOVE_PRE `M iyy` `ms (iyy+1w)` th
  val th = ms_combine MOVE_PRE `M izz` `ms (izz+1w)` th
  val th = AUTO_HIDE_PRE [`M ixx`] th
  val th = MOVE_PRE `blank_ms (ixx + 1w)` th
  val th = RW1 [GSYM STAR_ASSOC] th
  val th = RW [GSYM (REWRITE_CONV [LENGTH,blank_ms_def] ``blank_ms ixx (LENGTH (zx::zs))``)] th
  val th = RW [STAR_ASSOC,GSYM WORD_ADD_ASSOC,word_add_n2w] th     
  val th = RW [GSYM (REWRITE_CONV [LENGTH,RW1[ADD_COMM]ADD1] ``LENGTH (zx:word32::zs)``)] th
  val th = RW [(GSYM o REWRITE_CONV [mw_sub_cases]) ``SND (mw_sub (zx::zs) (yx:word32 ::ys) T)``] th
  val th = RW [(GSYM o REWRITE_CONV [mw_sub_cases,GSYM (CONJUNCT1 sub_thm),WORD_SUB_RZERO])
       ``FST (mw_sub (zx::zs) (yx:word32 ::ys) T)``] th
  val th = APP_PART_STRENGTHEN (SIMP_RULE (bool_ss++sep2_ss) [GSYM LENGTH_NIL] th)
    `cond (1 < LENGTH (zx:word32 ::zs) /\ (LENGTH (zx::zs) = LENGTH (yx:word32 ::ys)))`
    (REWRITE_TAC [LENGTH,SEP_IMP_cond] \\ DECIDE_TAC)
  val th = (GEN_CONS ``zx:word32 :: zs`` `zx` `zs` o Q.INST [`x:word32`|->`zx`,`xs`|->`zs`] o GEN_CONS_LE `yx` `ys`) th
  val thx = (RW [GSYM R30_def] o AUTO_HIDE_POST1 [`R t`] o RW [R30_def,GSYM ARM_PROG_MOVE_COND]) th
  val th = (*  sub ix,ix,tt  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`ix`,`b`|->`tt`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_SUB2'))
  val th = (*  sub iy,iy,tt  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`iy`,`b`|->`tt`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_SUB2'))) `x1*x2*x3` `(x2*x3)*(x1)` `x1*x2*x3` `(x2*x3)*(x1)`
  val th = (*  sub iz,iz,tt  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`iz`,`b`|->`tt`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_SUB2'))) `x1*x2*x3*x4` `(x2*x3)*(x1*x4)` `x1*x2*x3` `(x2*x3)*(x1)`
  val th = (*  sbcs v,v,#0   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`v`,`a_mode`|->`Imm 0w`,`x`|->`x4` ] arm_SBC1))) `x1*x2*x3*x4*x5` `(x3)*(x1*x2*x4*x5)` `x1*x2` `(x2)*(x1)`
  val th = Q.INST [`y1`|->`ttx`] (ALIGN_VARS ["x1","x2","x3","y1"] th)
  val th = (RW [GSYM R30_def] o AUTO_HIDE_POST1 [`R v`,`R tt`] o RW [R30_def]) th
  val th = Q.INST [`x3`|->`izz+ttx`,`x2`|->`iyy+ttx`,`x1`|->`ixx+ttx`,`x4`|->`vx`] th
  val th = RW [WORD_ADD_SUB,sub_thm] th
  val th = FRAME_COMPOSE th (MATCH_INST1 [`S`] th final_select)
  val th = (HIDE_PRE3 o RW [GSYM S_carry_def] o MOVE_PRE `S`) th
  val th = Q.INST [`ttx`|->`n2w (LENGTH (zs:word32 list))`,`xs`|->`FST (mw_sub zs ys T)`,`sC`|->`SND (mw_sub zs (ys:word32 list) T)`,`vx`|->`z'`] th
  val th = FRAME_COMPOSE thx th
  val th = DISCH ``LENGTH (zs:word32 list) = LENGTH (ys:word32 list)`` th
  val th = SIMP_RULE bool_ss [] th
  val th = SIMP_RULE (bool_ss++sep2_ss) [GSYM LENGTH_NIL,GSYM ARM_PROG_MOVE_COND] th  
  val th = APP_PART_STRENGTHEN th
    `cond ((LENGTH (ys:word32 list) = LENGTH (zs:word32 list)) /\ 1 < LENGTH ys)`
    (REWRITE_TAC [SEP_IMP_cond] \\ REPEAT STRIP_TAC \\ REPEAT DECIDE_TAC
     \\ ASM_REWRITE_TAC [] \\ MATCH_MP_TAC LENGTH_FST_mw_sub \\ ASM_REWRITE_TAC [])
  in th end;

val SEP_CONTAINS_ms_CONS = prove(
  ``SEP_CONTAINS (ms a (x::xs)) P ==> SEP_CONTAINS (ms (a + 1w) xs) P``,
  REWRITE_TAC [SEP_CONTAINS_def,ms_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `M a x * F'` \\ ASM_SIMP_TAC (bool_ss++star_ss) []);
 
val ARM_PROG_MOVE_COND2 = prove(
  ``(g ==> ARM_PROG (P * cond h) code C Q Z) ==>
    (h ==> g) ==> ARM_PROG (P * cond h) code C Q Z``,
  Cases_on `h` \\ SIMP_TAC (bool_ss++sep_ss) [ARM_PROG_FALSE_PRE]);

val mw_monprod6_imp = let

  (* init code *)
  val th = (*  ldr v,[sp,#4]  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`v`,`b`|->`13w`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  ldr p,[iu]     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`p`,`b`|->`iu`,`imm`|->`0w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4` `(x4)*(x1*x2*x3)` `x1*x2*x3*x4` `(x4)*(x1*x2*x3)`
  val th = (*  add tt,ix,v    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`tt`,`a`|->`ix`,`b`|->`v`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_ADD3))) `x1*x2*x3*x4*x5*x6*x7` `(x4*x5)*(x1*x2*x3*x6*x7)` `x1*x2*x3*x4` `(x4*x2)*(x1*x3)`
  val th = (*  add t,iu,v     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`t`,`a`|->`iu`,`b`|->`v`,`a_mode`|->`OneReg`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4` ] arm_ADD3))) `x1*x2*x3*x4*x5*x6*x7*x8*x9` `(x2*x4*x6)*(x1*x3*x5*x7*x8*x9)` `x1*x2*x3*x4` `(x2*x4*x1)*(x3)`
  val th = (*  add iu,iu,#4   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`iu`,`a_mode`|->`Imm 4w`,`x`|->`x5` ] arm_ADD1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9*x10` `(x1*x4)*(x2*x3*x5*x6*x7*x8*x9*x10)` `x1*x2` `(x1*x2)*(emp)`
  val th = ALIGN_VARS ["y2","y1","z1","x3"] (AUTO_HIDE_STATUS th)
  val th = AUTO_HIDE_POST1 [`R v`] (RW [R30_def] th)
  val th = RW [GSYM R30_def] (AUTO_HIDE_PRE [`R v`,`R p`,`R t`,`R tt`] th)
  val th = Q.INST [`x3`|->`ixx`,`y2`|->`iuu`,`z2`|->`ux`,`y1`|->`sp`,`z1`|->`n2w (LENGTH (xs:word32 list))`] th
  val th = MOVE_POST1 `M iuu` (MOVE_PRE `M iuu` th)
  val th = APP_FRAME `ms (iuu+1w) us` th
  val th = RW [GSYM ms_def] (RW1 [GSYM STAR_ASSOC] th)
  val th = Q.SPEC `P * ms ixx xs` (MATCH_MP ARM_PROG_CONTAINS th)  
  
  (* combine mw_moninit and mw_monmult5 *)
  val th1 = Q.INST [`t`|->`tt`] mw_moninit_imp
  val th2 = RW [arm_mm5_pre_def,arm_mm5_post_def] mw_monmult5_imp    
  val th2 = MATCH_INST1 [`ms izz`,`M (sp - 7w)`] th1 th2
  val thx = FRAME_COMPOSE th1 (RW [wLENGTH_def] th2)
  val thx = Q.INST [`iuu`|->`iuu+1w`] thx
  val thx = (RW [GSYM R30_def] o AUTO_HIDE_POST1 [`R t`] o RW [R30_def]) thx
  val rw = prove(``iuu + 1w + n2w (LENGTH us) = iuu + n2w (LENGTH (ux::us))``,
                 REWRITE_TAC [RW1[ADD_COMM]ADD1,GSYM word_add_n2w,LENGTH,WORD_ADD_ASSOC])
  val thx = (DISCH ``LENGTH (ux:word32 ::us) = LENGTH (xs:word32 list)`` o RW [rw]) thx
  val thx = (RW [LENGTH,GSYM ARM_PROG_MOVE_COND] o SIMP_RULE bool_ss []) thx
 
  (* add the init code and clean up *)
  val th = FRAME_COMPOSE th thx
  val th = APP_PART_STRENGTHEN (SIMP_RULE (bool_ss++sep2_ss) [] th)
    `cond ((LENGTH (ux:word32::us) = LENGTH (xs:word32 list)) /\ (LENGTH xs = LENGTH (ys:word32 list)) /\ 1 < LENGTH xs /\ SEP_CONTAINS ((ms iuu (ux::us)):'a ARMset -> bool) (P * ms ixx xs))`
   (REWRITE_TAC [SEP_IMP_cond,LENGTH,ADD1,mw_moninit_def] 
    \\ REPEAT STRIP_TAC \\ REPEAT DECIDE_TAC \\ IMP_RES_TAC SEP_CONTAINS_ms_CONS
    \\ Q.PAT_ASSUM `LENGTH xs = LENGTH ys` (ASSUME_TAC o GSYM) \\ ASM_REWRITE_TAC []
    \\ Cases_on `xs` THEN1 FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `ys` THEN1 (FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [MAP,ADD1,EQ_ADD_RCANCEL,LENGTH]
    \\ MATCH_MP_TAC (GSYM (RW [AND_IMP_INTRO,LENGTH,ADD1] LENGTH_FST_mw_monmult5_step))
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LENGTH_MAP] \\ DECIDE_TAC)   

  (* compose tail and clean *)
  val th = MOVE_POST1 `ms ixx` th
  val th = APP_PART_WEAKEN1 th 
           `blank_ms ixx (LENGTH (xs:word32 list))` (REWRITE_TAC [SEP_IMP_ms_blank_ms])
  val th = DISCH ``LENGTH (xs:word32 list) = LENGTH (ys:word32 list)`` th
  val th = RW [GSYM ARM_PROG_MOVE_COND,wLENGTH_def] (SIMP_RULE bool_ss [] th)
  val th = FRAME_COMPOSE th (MATCH_INST1 [`M (sp-7w)`,`ms izz`] th monprod6_tail)
  val th = DISCH ``(LENGTH (FST (mw_sub (FST (mw_monmult5 us xs ys px (FST (mw_moninit (xs:word32 list) ys ux px)) (SND (mw_moninit (xs:word32 list) ys ux px)))) ys T))) = LENGTH xs`` th 
  val th = SIMP_RULE (bool_ss++sep2_ss) [GSYM ARM_PROG_MOVE_COND] (SIMP_RULE bool_ss [] th)
  val th = APP_PART_STRENGTHEN th `cond (1 < LENGTH xs /\ (LENGTH (ux:word32::us) = LENGTH xs) /\ (LENGTH (xs:word32 list) = LENGTH (ys:word32 list)) /\ SEP_CONTAINS ((ms iuu (ux::us)):'a ARMset -> bool) (P * ms ixx xs))`
   (REWRITE_TAC [SEP_IMP_cond,LENGTH] \\ REPEAT STRIP_TAC \\ REPEAT DECIDE_TAC
    \\ `~(LENGTH (xs:word32 list) = 0)` by DECIDE_TAC
    \\ Q.ABBREV_TAC `qs = mw_monmult5 us xs ys px (FST (mw_moninit xs ys ux px)) (SND (mw_moninit xs ys ux px))`
    \\ `LENGTH (FST qs) = LENGTH xs` by  
       (Q.UNABBREV_TAC `qs` \\ METIS_TAC [LENGTH_FST_mw_moninit,LENGTH_FST_mw_monmult5])
    \\ METIS_TAC [LENGTH_FST_mw_moninit,LENGTH_FST_mw_sub])
  val th = RW [GSYM mw_monprod6_cases,GSYM M30_def,GSYM wLENGTH_def] th
  val th = CONS_GEN `ux::us` th  
  val th = MATCH_MP ARM_PROG_MOVE_COND2 th    
  val th = RW [GSYM LENGTH_NIL] th
  val goal = (fst o dest_imp o concl) th
  val th1 = prove(goal,REPEAT STRIP_TAC \\ DECIDE_TAC)
  val th = MATCH_MP th th1
  val th = Q.INST [`t`|->`14w`,`p`|->`v2`,`q`|->`v3`,`v`|->`v4`,`tt`|->`v5`,`x`|->`v6`,`y`|->`v7`,`z`|->`v8`,`b`|->`v9`,`c`|->`v1`] th

  (* enclose code inbetween STM and LDM *)
  val th1 = Q.INST [`a`|->`13w`,`x`|->`sp`] ENCLOSE_STM_LDM
  val th1 = Q.INST [`xs`|->`[(v1,x1);(v2,x2);(v3,x3);(v4,x4);(v5,x5)]`] th1
  val th1 = SIMP_RULE arith_ss [LENGTH,MAP,xR_list_def,emp_STAR,STAR_ASSOC] th1
  val th = foldl (uncurry MOVE_POST1) th [`R30 13w`,`R v1`,`R v2`,`R v3`,`R v4`,`R v5`,`R 14w`,`S`]
  val th = foldl (uncurry MOVE_PRE) th [`R30 13w`,`R v1`,`R v2`,`R v3`,`R v4`,`R v5`,`R 14w`,`S`]
  val th = MATCH_MP th1 th
  val th = RW [APPEND,setADD_CLAUSES,M30_def,wLENGTH_def,addr32_n2w] th
  val th = foldr (uncurry MOVE_PRE) th [`M (sp+1w)`,`M sp`,`M (sp-7w)`,`blank (sp-1w)`,`R30 13w`]
  val th = foldr (uncurry MOVE_POST) th [`M (sp+1w)`,`M sp`,`M (sp-7w)`,`blank (sp-1w)`,`R30 13w`]
  val lemma = prove(
    ``P * R30 13w sp * blank (sp - 1w) 6 * ~M (sp - 7w) * M sp x * M (sp + 1w) y =
      P * stack sp [x;y] 7``,
    REWRITE_TAC [GSYM (EVAL ``SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))``)]
    \\ REWRITE_TAC [GSYM (EVAL ``SUC (SUC (SUC (SUC (SUC (SUC 0)))))``)]
    \\ REWRITE_TAC [stack_def,ms_def,blank_def]
    \\ REWRITE_TAC [ADD1,GSYM word_add_n2w,WORD_SUB_PLUS,emp_STAR,WORD_SUB_RZERO]
    \\ SIMP_TAC (bool_ss++star_ss) [])
  val th = RW [lemma,GSYM R30_def] th  

  (* split specification into two: ixx and iuu alias or not *)
  val tha = Q.INST [`P`|->`emp`,`iuu`|->`ixx`,`us`|->`xs`] th
  val tha = RW [SEP_CONTAINS_CLAUSES,emp_STAR] tha 
  val th = Q.INST [`P`|->`ms iuu us`] th
  val th = RW [SEP_CONTAINS_CLAUSES,emp_STAR] th

  (* hide addresses for non-aliasing version *)
  val th = APP_WEAKEN th 
    `Rms iu us * Rms ix (mw_monprod6 us xs ys px) * Rms iy ys * Rblank iz (LENGTH xs) * 
     stack sp [px;n2w (4*LENGTH ys)] 7 * 
     R v1 x1 * R v2 x2 * R v3 x3 * R v4 x4 * R v5 x5 *
     ~R v6 * ~R v7 * ~R v8 * ~R v9 * ~R 14w * ~S`   
   (SIMP_TAC (bool_ss++sep2_ss) [Rms_def]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] 
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `iuu` \\ Q.EXISTS_TAC `a` \\ Q.EXISTS_TAC `iyy` 
    \\ FULL_SIMP_TAC bool_ss [AC STAR_ASSOC STAR_COMM])
  val th = (EXISTS_PRE `izz` o EXISTS_PRE `iuu` o EXISTS_PRE `iyy` o EXISTS_PRE `ixx`) th  
  val th = APP_STRENGTHEN (Q.INST [`zs`|->`ys`] th)
    `Rms iu us * Rms ix xs * Rms iy ys * Rblank iz (LENGTH xs) *  
     stack sp [px;n2w (4*LENGTH ys)] 7 * 
     R v1 x1 * R v2 x2 * R v3 x3 * R v4 x4 * R v5 x5 *
     ~R v6 * ~R v7 * ~R v8 * ~R v9 * R30 14w p * ~S *   
     cond ((LENGTH us = LENGTH xs) /\ (LENGTH xs = LENGTH (ys:word32 list)) /\ 
           1 < LENGTH (xs:word32 list))`
   (SIMP_TAC (bool_ss++sep2_ss) [Rms_def,Rblank_def] 
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `a'''` \\ Q.EXISTS_TAC `a` \\ Q.EXISTS_TAC `a''` \\ Q.EXISTS_TAC `a'` 
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [] \\ METIS_TAC [STAR_ASSOC,STAR_COMM])

  (* hide addresses for aliasing version *)
  val tha = AUTO_HIDE_POST [`R iu`] (RW [R30_def] tha)
  val tha = APP_WEAKEN tha 
    `Rms ix (mw_monprod6 xs xs ys px) * Rms iy ys * Rblank iz (LENGTH xs) * 
     stack sp [px;n2w (4*LENGTH ys)] 7 * 
     R v1 x1 * R v2 x2 * R v3 x3 * R v4 x4 * R v5 x5 *
     ~R iu * ~R v6 * ~R v7 * ~R v8 * ~R v9 * ~R 14w * ~S`   
   (SIMP_TAC (bool_ss++sep2_ss) [Rms_def,R30_def]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] 
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `a` \\ Q.EXISTS_TAC `iyy` 
    \\ FULL_SIMP_TAC bool_ss [AC STAR_ASSOC STAR_COMM])
  val tha = (EXISTS_PRE `izz` o EXISTS_PRE `iyy` o EXISTS_PRE `ixx`) tha  
  val tha = APP_STRENGTHEN (Q.INST [`zs`|->`ys`] tha)
    `RRms iu ix xs * Rms iy ys * Rblank iz (LENGTH xs) *  
     stack sp [px;n2w (4*LENGTH ys)] 7 * 
     R v1 x1 * R v2 x2 * R v3 x3 * R v4 x4 * R v5 x5 *
     ~R v6 * ~R v7 * ~R v8 * ~R v9 * R30 14w p * ~S *   
     cond ((LENGTH xs = LENGTH (ys:word32 list)) /\ 1 < LENGTH (xs:word32 list))`
   (SIMP_TAC (bool_ss++sep2_ss) [Rms_def,RRms_def,Rblank_def,R30_def] 
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `a''` \\ Q.EXISTS_TAC `a'` \\ Q.EXISTS_TAC `a` 
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [] \\ METIS_TAC [STAR_ASSOC,STAR_COMM])
  
  in (th,tha) end;

val montgomery_vars_imp = prove(
  ``montgomery_vars n n' (2 ** (i * 32)) r' /\ k < n /\ l < n /\ 1 < i ==>
    ((montprod_vars n n' (2 ** (i * 32)) r' k l /\ 0 < i) /\ 1 < i)``,
  REWRITE_TAC [montgomery_vars_def,montprod_vars_def]
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ REPEAT DECIDE_TAC);

val (monprod6_spec1,monprod6_spec2) = let
  val th = fst mw_monprod6_imp
  val th = Q.INST [`us`|->`n2mw i k`,`xs`|->`n2mw i l`,`ys`|->`n2mw i n`,`px`|->`n2w n'`] th
  val th = RW [GSYM bignum_def,wLENGTH_def,LENGTH_n2mw,Rblank_EQ_bignum] th
  val dimwords32 = prove(``dimwords i (:32) = 2**(i*32)``,REWRITE_TAC [dimwords_def] \\ SIMP_TAC (std_ss++SIZES_ss) []);
  val lemma = prove(``2 < dimword (:32)``,SIMP_TAC (std_ss++SIZES_ss) [])
  val spec = RW [dimwords32] (MATCH_MP mw_monprod6_spec lemma)
  val spec = Q.SPECL [`k`,`l`,`n`,`n'`,`r'`,`i`] (INST_TYPE [``:'a``|->``:32``] spec)
  val spec = UNDISCH spec
  val th = SIMP_RULE bool_ss [GSYM bignum_def] (DISCH (concl spec) th)
  val th = RW [GSYM AND_IMP_INTRO,ARM_PROG_MOVE_COND] (DISCH_ALL (MATCH_MP th spec))
  val th = MATCH_MP (RW [AND_IMP_INTRO] th) (UNDISCH montgomery_vars_imp)
  val th1 = RW [GSYM ARM_PROG_MOVE_COND] (DISCH_ALL th)
  val th = RW [GSYM AND_IMP_INTRO] (DISCH_ALL th)
  val th = SIMP_RULE bool_ss [] (DISCH ``2 ** (i * 32) = r`` th)
  val th = Q.INST [`k`|->`residue p r n`,`l`|->`residue q r n`] th
  val lemma1 = (UNDISCH (Q.SPECL [`n`,`n'`,`r`,`r'`,`p`] residue_LT))
  val lemma2 = (UNDISCH (Q.SPECL [`n`,`n'`,`r`,`r'`,`q`] residue_LT))
  val th = MATCH_MP (MATCH_MP ((UNDISCH o UNDISCH) th) lemma1) lemma2
  val lemma1 = (UNDISCH (Q.SPECL [`n`,`n'`,`r`,`r'`,`p`,`q`] residue_MULT))
  val th = MATCH_MP (SIMP_RULE bool_ss [] (DISCH (concl lemma1) th)) lemma1
  val th = (DISCH_ALL (DISCH ``montgomery_vars n n' r r'`` th))
  val th2 = RW [residue_def,GSYM ARM_PROG_MOVE_COND] (RW [AND_IMP_INTRO,GSYM CONJ_ASSOC] th)
  in (save_thm("monprod6_spec1",th1),save_thm("monprod6_spec2",th2)) end;

(* binary exponential *)

(* prove specs for both proc calls *)

val mult_if_odd = let
  val th = fst mw_monprod6_imp
  val th = MOVE_POST `R 14w` (MOVE_PRE `R30 14w` th)
  val th = Q.GEN `p` (EXTRACT_CODE th)
  val th = RW [GSYM ARM_PROC_THM,ARM_PROG_FALSE_POST] th
  val th = MATCH_MP arm_BL th
  val th = RW [setADD_CLAUSES] th  
  val th2 = AUTO_HIDE_PRE [`R v1`] (AUTO_HIDE_POST1 [`R v1`] th)
  (* make_spec ["mov ix,v1"] *)
  val th = (*  mov ix,v1  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`ix`,`a`|->`v1`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_MOV2))
  val th = AUTO_HIDE_STATUS th
  val th = AUTO_HIDE_PRE [`R ix`] th 
  val th = AUTO_HIDE_POST1 [`R v1`] th 
  val th = ALIGN_VARS ["x1"] th
  val th = APP_FRAME `ms x1 xs` th
  val th = APP_WEAKEN1 th `Rms ix xs * ~R v1 * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_def,Rms_def]
    \\ SIMP_TAC std_ss [SEP_EXISTS,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `x1` 
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = EXISTS_PRE `x1` th
  val th1 = APP_STRENGTHEN th `Rms v1 xs * ~R ix * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_def,Rms_def]
    \\ SIMP_TAC std_ss [SEP_EXISTS,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `y`
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = FRAME_COMPOSE th1 th2
  val th' = Q.INST [`v1`|->`ix`,`ix`|->`v1`] th1
  val th1 = FRAME_COMPOSE th (MATCH_INST1 [`Rms ix`] th th')
  
  (* make_spec ["tst v2,#1","beq 16"] *)
  val th = (*  tst v2,#1  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`v2`,`a_mode`|->`Imm 1w`,`x`|->`x1` ] arm_TST1))
  val th = (*  beq 16     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (2w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`2w` ] arm_B2))) `x1*x2` `(x2)*(x1)` `x1*x2` `(x1)*(x2)`
  val th = Q.INST [`x1`|->`x2`] (AUTO_HIDE_STATUS th)
  val th = SIMP_RULE (arith_ss++pcINC_ss++sep_ss) [wLENGTH_def,LENGTH] th
  val th = APP_FRAME `Rms v1 (if x2:word32 && 1w = 0w then xs else mw_monprod6 us xs ys px)` th
  val th = RW1[GSYM STAR_ASSOC](SIMP_RULE (bool_ss++sep2_ss) [] th)
  val th = APP_PART_STRENGTHEN th `Rms v1 xs * cond (x2 && 1w:word32 = 0w)`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_REFL,SEP_IMP_MOVE_COND])
  val th2 = RW [STAR_ASSOC] th  

  (* make_spec' [("tst v2,#1",true),("beq 16",false)] *)
  val th = (*  tst v2,#1  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`v2`,`a_mode`|->`Imm 1w`,`x`|->`x1` ] arm_TST1))
  val th = (*  beq 16     *) MOVE_COMPOSE th (SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (2w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`2w` ] arm_B2))) `x1*x2` `(x2)*(x1)` `x1*x2` `(x1)*(x2)`
  val th = AUTO_HIDE_STATUS th
  val th3 = UNDISCH (SIMP_RULE (bool_ss++sep2_ss) [ARM_PROG_MOVE_COND] th1)
  val th = FRAME_COMPOSE (Q.INST [`x1`|->`x2`] th) th3
  val th = MOVE_POST1 `Rms v1` th
  val th = APP_FRAME `cond ~(x2 && 1w = 0w:word32)` th
  val th = RW [SEP_cond_CLAUSES] (RW1[GSYM STAR_ASSOC] th)
  val th = APP_PART_WEAKEN1 th 
    `Rms v1 (if x2 && 1w:word32 = 0w then xs else (mw_monprod6 us xs ys px))`
    (SIMP_TAC bool_ss [SEP_IMP_REFL,SEP_IMP_MOVE_COND])
  
  val th3 = APP_FRAME `~R ix * Rms iu us * Rms iy ys *
          Rblank iz (LENGTH ys) * stack sp [px; n2w (4 * LENGTH ys)] 7 *
          R v3 x3 * R v4 x4 * R v5 x5 * ~R v6 * ~R v7 * ~R v8 *
          ~R v9 * ~R 14w` th2
  val th3 = SIMP_RULE (bool_ss++sep2_ss) [] th3
  val th = APP_MERGE th3 th
  val th = RW [STAR_ASSOC] (SIMP_RULE (bool_ss++star_ss) [] th)
  val th = SIMP_RULE (bool_ss++sep2_ss) [STAR_OVER_DISJ] th
  val th = RW1 [ARM_PROG_EXTRACT_POST] th
  val th = SIMP_RULE arith_ss [pcINC_def,wLENGTH_def,LENGTH,word_add_n2w] th
  val th = RW [ARM_PROG_MERGE_POST] th
  val th = RW [SEP_DISJ_CLAUSES] (SIMP_RULE (bool_ss++star_ss) [] th)
  val th = RW [STAR_ASSOC] th
  val th = ABSORB_POST th
  val th = RW [GSYM ARM_PROG_MOVE_COND] (DISCH_ALL th)
  in th end;

val square = let
  val th = snd mw_monprod6_imp
  val th = MOVE_POST `R 14w` (MOVE_PRE `R30 14w` th)
  val th = Q.GEN `p` (EXTRACT_CODE th)
  val th = RW [GSYM ARM_PROC_THM,ARM_PROG_FALSE_POST] th
  val th = MATCH_MP arm_BL th
  val th2 = RW [setADD_CLAUSES] th  
  (* make_spec ["mov ix,iu"] *)
  val th = (*  mov ix,iu  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`ix`,`a`|->`iu`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_MOV2))
  val th = AUTO_HIDE_STATUS th
  val th = AUTO_HIDE_PRE [`R ix`] th 
  val th = ALIGN_VARS ["x1"] th
  val th = APP_FRAME `ms x1 xs` th
  val th = APP_WEAKEN1 th `RRms iu ix xs * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_def,RRms_def]
    \\ SIMP_TAC std_ss [SEP_EXISTS,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `x1` 
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = EXISTS_PRE `x1` th
  val th1 = APP_STRENGTHEN th `Rms iu xs * ~R ix * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_def,Rms_def]
    \\ SIMP_TAC std_ss [SEP_EXISTS,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `y`
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th3 = FRAME_COMPOSE th1 th2
  (* make_spec ["mov iu,ix"] *)
  val th = (*  mov iu,ix  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`iu`,`a`|->`ix`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_MOV2))
  val th = AUTO_HIDE_STATUS th
  val th = AUTO_HIDE_PRE [`R iu`] th 
  val th = AUTO_HIDE_POST1 [`R ix`] th 
  val th = ALIGN_VARS ["x1"] th
  val th = APP_FRAME `ms x1 xs` th
  val th = APP_WEAKEN1 th `Rms iu xs * ~R ix * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_def,Rms_def]
    \\ SIMP_TAC std_ss [SEP_EXISTS,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `x1` 
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = EXISTS_PRE `x1` th
  val th1 = APP_STRENGTHEN th `Rms ix xs * ~R iu * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_def,Rms_def]
    \\ SIMP_TAC std_ss [SEP_EXISTS,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `y`
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th4 = FRAME_COMPOSE th3 (MATCH_INST1 [`Rms ix`] th3 th1)
  in th4 end;

val f_assum_def = Define `
  f_assum f (zs,sz:word32) = cond (!xs ys. mw_monprod6 xs ys zs sz = f xs ys)`;

val arm_el_pre_def = Define `
  arm_el_pre v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp x2 x3 x4 x5 f us xs = 
     Rms iu us * Rms v1 xs * Rms iy ys * Rblank iz (LENGTH ys) * 
     R v2 x2 * R v3 x3 * R v4 x4 * R v5 x5 * 
     ~R ix * ~R v6 * ~R v7 * ~R v8 * ~R v9 * ~R 14w * ~S * 
     stack sp [px; n2w (4 * LENGTH ys)] 7 * f_assum f (ys,px) * 
     cond ((LENGTH us = LENGTH xs) /\ (LENGTH xs = LENGTH ys) /\
           1 < LENGTH xs) * cond ~(x2 = 0w)`;

val arm_el_post_def = Define `
  arm_el_post v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp (x2:word32) x3 x4 x5 f us xs = 
     Rblank iu (LENGTH ys) * Rms v1 (exp_last f x2 xs us) * Rms iy ys * Rblank iz (LENGTH ys) * 
     R v2 0w * R v3 x3 * R v4 x4 * R v5 x5 * 
     ~R ix * ~R v6 * ~R v7 * ~R v8 * ~R v9 * ~R 14w * ~S * 
     stack sp [px; n2w (4 * LENGTH ys)] 7`;

val INTRO_Rms = let
  val th = SPEC_ALL (ASSUME ``!x1. ARM_PROG (P * R v1 x1) code C SEP_F {(Q * R v1 x1,f)}``)
  val th = ALIGN_VARS ["x1"] th
  val th = APP_FRAME `ms x1 xs` th
  val th = APP_WEAKEN th `Q * Rms v1 xs`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_def,Rms_def]
    \\ SIMP_TAC std_ss [SEP_EXISTS,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `x1`
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = EXISTS_PRE `x1` th
  val th = APP_STRENGTHEN th `P * Rms v1 xs`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_def,Rms_def]
    \\ SIMP_TAC std_ss [SEP_EXISTS,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `x1`
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = DISCH_ALL th  
  in th end;

val exp_last_pass1 = let
  (* make_spec ["b -40"] *)
  val th = (*  b -40  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (16777204w :word24) :word30)``] (Q.INST [`c_flag`|->`AL`,`offset`|->`16777204w` ] arm_B2))
  val th = AUTO_HIDE_STATUS th
  val th = Q.INST [`offset`|->`offset5`] (FRAME_COMPOSE square th)
  val th1 = MOVE_POST `R v1` (MOVE_PRE `R v1` th)
  val th3 = MATCH_MP INTRO_Rms (Q.GEN `x1` th1)  
  (* make_spec["movs v2,v2,LSR #1"] make_spec["beq 78"] *)
  val th1 = (*  movs v2,v2,LSR #1  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`v2`,`a_mode`|->`RegLSR 1w`,`x`|->`x1` ] arm_MOV1))
  val th2 = (*  beq k  *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`EQ`,`offset`|->`offset2` ] arm_B)
  val th = FRAME_COMPOSE th1 (MATCH_INST1 [`S`] th1 th2)
  val th = AUTO_HIDE_STATUS (Q.INST [`x1`|->`x2`] th)
  val th = RW [EVAL ``1w = 0w:word5``,EVAL ``w2n (1w:word5)``] th
  val th = FRAME_COMPOSE mult_if_odd th
  val th3 = MATCH_INST1 [`Rms iu`] th th3
  val th3 = MATCH_INST1 [`Rms v1`,`R v2`] th th3
  val th3 = DISCH ``LENGTH (us:word32 list) = LENGTH (ys:word32 list)`` th3
  val th3 = RW [GSYM ARM_PROG_MOVE_COND] (SIMP_RULE bool_ss [] th3)
  val th = FRAME_COMPOSE th th3
  val th = DISCH ``!us xs. mw_monprod6 us xs ys (px:word32) = f us xs`` th
  val th = SIMP_RULE bool_ss [] th
  val th = RW [GSYM ARM_PROG_MOVE_COND,GSYM f_assum_def] th
  val th = RW [INSERT_UNION_EQ,UNION_EMPTY] th
  val th = APP_FRAME `cond ~(x2:word32 = 0w)` th
  val th = Q.INST [`offset2`|->`3w`] th
  val th = RW[EVAL ``sw2sw (3w:word24) + 2w + 1w + 5w:word30``]th
  val th = ABSORB_POST th
  val lemma = prove(``n2w(2**30):word30=0w``,
    ONCE_REWRITE_TAC [GSYM n2w_mod] \\ SIMP_TAC (std_ss++SIZES_ss) [])
  val th = RW [GSYM(EVAL ``2**30``),lemma,pcADD_0]th
  (* tidy up *)
  val th = APP_FRAME `cond ((LENGTH (us:word32 list) = LENGTH (xs:word32 list)) /\ (LENGTH xs = LENGTH (ys:word32 list)) /\ 1 < LENGTH xs) * f_assum f (ys,px)` th
  val th = APP_STRENGTHEN th
    `arm_el_pre v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp x2 x3 x4 x5 f us xs`
   (REWRITE_TAC [arm_el_pre_def,f_assum_def]
    \\ SIMP_TAC (bool_ss++star_ss) [] \\ SIMP_TAC (bool_ss++sep2_ss) []
    \\ MATCH_MP_TAC SEP_IMP_STAR
    \\ REWRITE_TAC [SEP_IMP_cond,SEP_IMP_REFL]
    \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ DECIDE_TAC)
  val th = APP_WEAKEN th
    `arm_el_pre v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp (x2 >>> 1) x3 x4 x5 f (f us us) (if x2 && 1w = 0w then xs else f us xs) * cond ~(x2 = 0w)`
   (REWRITE_TAC [arm_el_pre_def,f_assum_def]
    \\ SIMP_TAC (bool_ss++star_ss) [] \\ SIMP_TAC (bool_ss++sep2_ss) []
    \\ MATCH_MP_TAC SEP_IMP_STAR
    \\ REWRITE_TAC [SEP_IMP_cond,SEP_IMP_REFL]
    \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ REPEAT DECIDE_TAC
    \\ Cases_on `x2 && 1w = 0w` \\ ASM_REWRITE_TAC []
    \\ Q.PAT_ASSUM `!x.b` (fn th => REWRITE_TAC [GSYM th])
    \\ IMP_RES_TAC (DECIDE ``!n:num. 1 < n ==> ~(0 = n)``)
    \\ METIS_TAC [LENGTH_mw_monprod6])
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = APP_PART_WEAKEN1 th 
    `cond ((x2 >>> 1 = 0w:word32) /\ ~(x2 = 0w)) * cond (LENGTH (us:word32 list) = LENGTH (ys:word32 list))`
    (REWRITE_TAC [SEP_IMP_cond,SEP_cond_CLAUSES] 
     \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [])  
  val th = RW1 [GSYM STAR_ASSOC] (MOVE_POST1 `Rms iu` th)   
  val th = APP_PART_WEAKEN1 th 
    `Rblank iu (LENGTH (ys:word32 list))`
    (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND]
    \\ SIMP_TAC (bool_ss++sep2_ss) [Rms_def,Rblank_def]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `y` \\ (IMP_RES_TAC o RW [SEP_IMP_def] o RW1 [STAR_COMM] o 
          MATCH_MP SEP_IMP_FRAME o Q.SPECL [`us`,`y`]) SEP_IMP_ms_blank_ms
    \\ METIS_TAC [])
  val th = APP_WEAKEN1 th
    `arm_el_post v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp x2 x3 x4 x5 f us xs`
   (REWRITE_TAC [arm_el_post_def,f_assum_def]
    \\ SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND]
    \\ ONCE_REWRITE_TAC [exp_last_def]
    \\ ONCE_REWRITE_TAC [exp_last_def]
    \\ SIMP_TAC bool_ss [] \\ SIMP_TAC std_ss [LET_DEF]
    \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  in th end;


val arm_exp_last = let

  val ind = SIMP_RULE bool_ss [] exp_last_ind
  val th = exp_last_pass1

  (* step 5: instantiate induction and extract ind hyp *)
  val tm = extract_spec th [] [] [`f`,`x2`,`xs`,`us`]
  val th1 = ISPEC tm ind
  val th1 = CONV_RULE (DEPTH_CONV BETA_CONV) th1
  val asm = extract_assum th1
  val asm = RW [GSYM ARM_PROG_MOVE_COND] asm

  (* step 6: match step and prove postcondition *)
  val asm = MATCH_MP ARM_PROG_COMPOSE_WEAKEN asm
  val th = Q.INST [`us`|->`n`,`xs`|->`m`,`x2`|->`x`] th
  val th = RW1[GSYM(REWRITE_CONV[SEP_cond_CLAUSES]``cond b * cond b``)]th  
  val th = MATCH_MP asm (RW [STAR_ASSOC] th)
  val lemma = prove((fst o dest_imp o concl) th,
    REWRITE_TAC [arm_el_post_def]
    \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exp_last_def]))
    \\ SIMP_TAC std_ss [SEP_IMP_MOVE_COND,LET_DEF,SEP_IMP_REFL])
  val th = MATCH_MP th lemma    
 
  (* step 7: clean up *)
  val th = MATCH_MP th1 (tidy_up th1 th)
  val th = SPEC_ALL (Q.SPECL [`f`,`x2`,`xs`,`us`] th)

  in th end;

val arm_e3_pre_def = Define `
  arm_e3_pre v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp x2 x3 x4 x5 f us xs = 
     Rms iu us * Rms v1 xs * Rms iy ys * Rblank iz (LENGTH ys) * 
     R v2 x2 * R v3 x3 * R v4 x4 * R v5 x5 * 
     ~R ix * ~R v6 * ~R v7 * ~R v8 * ~R v9 * ~R 14w * ~S * 
     stack sp [px; n2w (4 * LENGTH ys)] 7 * f_assum f (ys,px) * 
     cond ((LENGTH us = LENGTH xs) /\ (LENGTH xs = LENGTH ys) /\
           1 < LENGTH xs) * cond ~(x3 = 0w)`;

val arm_e3_post_def = Define `
  arm_e3_post v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp (x2:word32) x3 x4 x5 f us xs = 
     Rms iu (SND (exp_step3 f x3 x2 xs us)) * Rms v1 (FST (exp_step3 f x3 x2 xs us)) * Rms iy ys * Rblank iz (LENGTH ys) * 
     ~R v2 * R v3 0w * R v4 x4 * R v5 x5 * 
     ~R ix * ~R v6 * ~R v7 * ~R v8 * ~R v9 * ~R 14w * ~S * 
     stack sp [px; n2w (4 * LENGTH ys)] 7`;


val exp_step3_pass1 = let
  (* make_spec["mov v2,v2,lsr #1","subs v3,v3,#1","bne 60"] *)
  val th = (*  mov v2,v2,lsr #1  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`v2`,`a_mode`|->`RegLSR 1w`,`x`|->`x1` ] arm_MOV1))
  val th = (*  subs v3,v3,#1     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`v3`,`a_mode`|->`Imm 1w`,`x`|->`x2` ] arm_SUB1))) `x1*x2` `(x2)*(x1)` `x1*x2` `(x2)*(x1)`
  val th = RW [EVAL ``1w = 0w:word5``,EVAL ``w2n (1w:word5)``] th
  val tn = (*  bne __            *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (13w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`offset6` ] arm_B)
  val th = FRAME_COMPOSE th (MATCH_INST1 [`S`] th tn)  
  val th = AUTO_HIDE_STATUS th
  val th1 = mult_if_odd
  val th2 = DISCH ``LENGTH (xs:word32 list) = LENGTH (ys:word32 list)`` square
  val th2 = RW [GSYM ARM_PROG_MOVE_COND] (SIMP_RULE bool_ss [] th2)
  val th2 = MATCH_INST1 [`Rms iu`] th1 th2  
  val th2 = Q.GEN `x1` (MOVE_POST1 `R v1` (MOVE_PRE `R v1` th2))
  val th2 = MATCH_MP INTRO_Rms (RW1 [ARM_PROG_EXTRACT_POST] th2)
  val th2 = RW [GSYM ARM_PROG_EXTRACT_POST] th2
  val th3 = FRAME_COMPOSE th1 (MATCH_INST1 [`Rms v1`] th1 th2)
  val th = FRAME_COMPOSE th3 (MATCH_INST1 [`R v2`,`R v3`] th3 th) 
  val th = DISCH ``!us xs. mw_monprod6 us xs ys (px:word32) = f us xs`` th
  val th = SIMP_RULE bool_ss [] th
  val th = RW [GSYM ARM_PROG_MOVE_COND,GSYM f_assum_def] th
  val th = APP_FRAME `cond ((LENGTH (us:word32 list) = LENGTH (xs:word32 list)) /\ (LENGTH xs = LENGTH (ys:word32 list)) /\ 1 < LENGTH xs) * f_assum f (ys,px) * cond ~(x3:word32 = 0w)` th
  val th = APP_STRENGTHEN th
    `arm_e3_pre v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp x2 x3 x4 x5 f us xs`
   (REWRITE_TAC [arm_e3_pre_def,f_assum_def]
    \\ SIMP_TAC (bool_ss++star_ss) [] \\ SIMP_TAC (bool_ss++sep2_ss) []
    \\ MATCH_MP_TAC SEP_IMP_STAR \\ REWRITE_TAC [SEP_IMP_cond,SEP_IMP_REFL]
    \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ DECIDE_TAC)
  val th = CLOSE_LOOP th
  val th = APP_WEAKEN th
    `arm_e3_pre v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp (x2 >>> 1) (x3 - 1w) x4 x5 f (f us us) (if x2 && 1w = 0w then xs else f us xs) * cond ~(x3 = 0w) * cond ~(x3 = 0w)`
   (REWRITE_TAC [arm_e3_pre_def,f_assum_def]
    \\ SIMP_TAC (bool_ss++star_ss) [] \\ SIMP_TAC (bool_ss++sep2_ss) []
    \\ MATCH_MP_TAC SEP_IMP_STAR
    \\ REWRITE_TAC [SEP_IMP_cond,SEP_IMP_REFL,WORD_EQ_SUB_ZERO]
    \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ REPEAT DECIDE_TAC
    \\ Cases_on `x2 && 1w = 0w` \\ ASM_REWRITE_TAC []
    \\ Q.PAT_ASSUM `!x.b` (fn th => REWRITE_TAC [GSYM th])
    \\ IMP_RES_TAC (DECIDE ``!n:num. 1 < n ==> ~(0 = n)``)
    \\ METIS_TAC [LENGTH_mw_monprod6])
  val th = AUTO_HIDE_POST1 [`R v2`] th
  val th = APP_WEAKEN1 th
    `arm_e3_post v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp x2 x3 x4 x5 f us xs`
   (REWRITE_TAC [arm_e3_post_def,f_assum_def]
    \\ SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,WORD_SUB_REFL]
    \\ ONCE_REWRITE_TAC [exp_step3_def]
    \\ ONCE_REWRITE_TAC [exp_step3_def]
    \\ SIMP_TAC bool_ss [EVAL ``1w = 0w:word32``,WORD_SUB_REFL] 
    \\ SIMP_TAC std_ss [LET_DEF]
    \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  in th end;

val arm_exp_step3 = let

  val ind = SIMP_RULE bool_ss [] exp_step3_ind
  val th = exp_step3_pass1

  (* step 5: instantiate induction and extract ind hyp *)
  val tm = extract_spec th [] [] [`f`,`x3`,`x2`,`xs`,`us`]
  val th1 = ISPEC tm ind
  val th1 = CONV_RULE (DEPTH_CONV BETA_CONV) th1
  val asm = extract_assum th1
  val asm = RW [GSYM ARM_PROG_MOVE_COND] asm

  (* step 6: match step and prove postcondition *)
  val asm = MATCH_MP ARM_PROG_COMPOSE_WEAKEN asm
  val th = Q.INST [`us`|->`n`,`xs`|->`m`,`x2`|->`x`,`x3`|->`i`] th
  val th = MATCH_MP asm th
  val lemma = prove((fst o dest_imp o concl) th,
    REWRITE_TAC [arm_e3_post_def]
    \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exp_step3_def]))
    \\ SIMP_TAC std_ss [SEP_IMP_MOVE_COND,LET_DEF,SEP_IMP_REFL])
  val th = MATCH_MP th lemma    
 
  (* step 7: clean up *)
  val th = MATCH_MP th1 (tidy_up th1 th)
  val th = SPEC_ALL (Q.SPECL [`f`,`x3`,`x2`,`xs`,`us`] th)

  in th end;


val arm_ee_pre_def = Define `
  arm_ee_pre v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp f us xs ipp ps = 
     Rms iu us * Rms v1 xs * Rms iy ys * Rblank iz (LENGTH ys) * 
     R30 v5 ipp * ms ipp ps * 
     ~R v2 * ~R v3 * R v4 (wLENGTH ps) * 
     ~R ix * ~R v6 * ~R v7 * ~R v8 * ~R v9 * ~R 14w * ~S * 
     stack sp [px; n2w (4 * LENGTH ys)] 7 * f_assum f (ys,px) * 
     cond ((LENGTH us = LENGTH xs) /\ (LENGTH xs = LENGTH ys) /\
           1 < LENGTH xs) * cond ~(LENGTH ps = 0)`;

val arm_ee_post_def = Define `
  arm_ee_post' v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp f us xs ipp ps = 
     Rms iu (SND (exp_list f xs us ps)) * Rms v1 (FST (exp_list f xs us ps)) * Rms iy ys * Rblank iz (LENGTH ys) * 
     R30 v5 (ipp + wLENGTH ps) * ms ipp ps * 
     ~R v2 * ~R v3 * ~R v4 *  
     ~R ix * ~R v6 * ~R v7 * ~R v8 * ~R v9 * ~R 14w * ~S * 
     stack sp [px; n2w (4 * LENGTH ys)] 7`;

val arm_exp_list = let
  (* make_spec ["ldr v2,[v5],#4","mov v3,#32"] *)
  val th = (*  ldr v2,[v5],#4  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`v2`,`b`|->`v5`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  mov v3,#32      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (32w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`v3`,`a_mode`|->`Imm 32w`,`x`|->`x2` ] arm_MOV1))) `x1*x2*x3*x4` `(x4)*(x1*x2*x3)` `x1*x2` `(x2)*(x1)`
  val th = ALIGN_VARS ["y1"] (AUTO_HIDE_STATUS th)
  val th = AUTO_HIDE_PRE [`R v3`,`R v2`] th
  val th = Q.INST [`y1`|->`ipp`,`z1`|->`x2`] th
  val th = APP_FRAME `ms (ipp+1w) ps` th
  val th1 = RW [arm_e3_pre_def,arm_e3_post_def] arm_exp_step3
  val th1 = ALIGN_VARS ["x5"] th1
  val th = FRAME_COMPOSE th (MATCH_INST1 [`R30 v5`,`R v3`] th th1)
  val lemma = SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:32``] exp_step4_def)
  val th = SIMP_RULE (bool_ss++sep_ss) [GSYM lemma,EVAL ``32w = 0w:word32``] th  
  val th = AUTO_HIDE_POST1 [`R v3`] th
  val th1 = APP_FRAME `f_assum f (ys,px) * cond ((LENGTH (us:word32 list) = LENGTH xs) /\ (LENGTH xs = LENGTH (ys:word32 list)) /\ 1 < LENGTH (xs:word32 list) /\ ~(LENGTH (x2:word32::ps) = 0))` th
  (* make_spec ["subs v4,v4,#1"] *)
  val th = (*  subs v4,v4,#1  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a`|->`v4`,`a_mode`|->`Imm 1w`,`x`|->`x1` ] arm_SUB1))
  val tn = (*  bne __            *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (13w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`offset7` ] arm_B)
  val th = FRAME_COMPOSE th (MATCH_INST1 [`S`] th tn)  
  val th = AUTO_HIDE_STATUS th
  val th = Q.INST [`x1`|->`x4`] th
  val th = FRAME_COMPOSE th1 th  
  val th = Q.INST [`x4`|->`wLENGTH (x2::ps)`] th
  val th = RW1 [GSYM WORD_EQ_SUB_ZERO] th
  val th = RW [wLENGTH_CONS,WORD_ADD_SUB2] th
  val th = DISCH ``LENGTH (ps:word32 list) < 2**30`` th
  val lemma = prove(``LENGTH xs < 2 ** 30 ==> ((wLENGTH xs = 0w:word32) = (xs = []))``,
    SIMP_TAC (arith_ss++SIZES_ss) [LESS_MOD,wLENGTH_def,n2w_11,LENGTH_NIL])
  val th = UNDISCH (SIMP_RULE bool_ss [lemma] th)
  val th = AUTO_HIDE_POST1 [`R v4`] th
  val th = APP_WEAKEN1 th
    `arm_ee_post' v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp f us xs ipp (x2::ps)`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,f_assum_def]
    \\ SIMP_TAC arith_ss [arm_ee_post_def,wLENGTH_def,LENGTH,ms_def,emp_STAR,exp_list_def]
    \\ Cases_on `exp_step4 f x2 xs us` \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = APP_STRENGTHEN th
    `arm_ee_pre v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp f us xs ipp (x2::ps)`
   (SIMP_TAC (bool_ss++sep2_ss) [f_assum_def,arm_ee_pre_def,wLENGTH_CONS,ms_def]
    \\ MATCH_MP_TAC SEP_IMP_STAR
    \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL,SEP_IMP_cond,LENGTH])
  val th = DISCH_ELIM_xs_ASSUM' arm_ee_pre_def `ipp` `x2` `ms ipp` th
  val th = APP_WEAKEN th
    `arm_ee_pre v1 v2 v3 v4 v5 v6 v7 v8 v9 iu ix iy iz ys px sp f (SND (exp_step4 f x2 xs us)) (FST (exp_step4 f x2 xs us)) (ipp+1w) ps * M ipp x2`
   (SIMP_TAC (bool_ss++sep2_ss) [f_assum_def,arm_ee_pre_def,wLENGTH_CONS,ms_def]
    \\ MATCH_MP_TAC SEP_IMP_STAR
    \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL,SEP_IMP_cond,LENGTH,GSYM LENGTH_NIL]
    \\ STRIP_TAC    
    \\ `!xs zs. (\xs. (LENGTH xs = LENGTH ys)) xs /\ (LENGTH xs = LENGTH zs) ==> 
                (\xs. (LENGTH xs = LENGTH ys)) zs /\
                (\xs. (LENGTH xs = LENGTH ys)) (f xs zs) /\
                (LENGTH zs = LENGTH (f xs zs))` by
      (REPEAT STRIP_TAC \\ SIMP_TAC std_ss []
       \\ Q.PAT_ASSUM `!x.b` (fn th => REWRITE_TAC [GSYM th])
       \\ `~(LENGTH xs = 0)` by DECIDE_TAC \\ METIS_TAC [LENGTH_mw_monprod6])
    \\ IMP_RES_TAC (INST_TYPE [``:'a``|->``:32``,``:'b``|->``:word32 list``,``:'c``|->``:num``] MONO_exp_step3)
    \\ FULL_SIMP_TAC std_ss [exp_step4_def] \\ METIS_TAC []) 
  val th = CLOSE_LOOP th

(*
  (* step 5: instantiate induction and extract ind hyp *)
  val tm = extract_spec th [(`x2::ps`,`ps`)] [`ipp`,`f`,`us`,`xs`] [`ps`]
  val th1 = ISPEC tm (RW [GSYM AND_IMP_INTRO] list_induction)
  val th1 = CONV_RULE (DEPTH_CONV BETA_CONV) th1
  val th1 = delete_fst_case [arm_ee_pre_def] th1
  val asm = extract_assum th1

  (* step 6: match step and prove postcondition *)
  val asm = MATCH_MP ARM_PROG_COMPOSE_WEAKEN asm
  val th = MATCH_MP asm th
*)

  (* step 5: instantiate induction and extract ind hyp *)
  val tm = extract_spec th [(`x2::ps`,`ps`)] [`ipp`] [`f`,`xs`,`us`,`ps`]
  val th1 = ISPEC tm (SIMP_RULE bool_ss [EXPAND_PAIR] exp_list_ind)
  val th1 = CONV_RULE (DEPTH_CONV BETA_CONV) th1
  val th1 = delete_fst_case [arm_ee_pre_def] th1
  val asm = extract_assum th1

  (* step 6: match step and prove postcondition *)
  val asm = MATCH_MP ARM_PROG_COMPOSE_WEAKEN asm
  val th = Q.INST [`x2`|->`x`,`ps`|->`xs`,`xs`|->`m`,`us`|->`n`] th
  val th = MATCH_MP asm th handle e => Raise e
  val lemma = prove((fst o dest_imp o concl) th,
    REWRITE_TAC [arm_ee_post_def]
    \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exp_list_def]))
    \\ Cases_on `exp_step4 f x m n` \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ REWRITE_TAC [ms_def,wLENGTH_CONS,WORD_ADD_ASSOC]    
    \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = MATCH_MP th lemma    

  (* step 7: clean up *)
  val th = MATCH_MP th1 (tidy_up th1 th)
  val th = SPEC_ALL (Q.SPECL [`f`,`us`,`xs`,`ps`,`ipp`] th)
   
  in th end;




val _ = export_theory();
