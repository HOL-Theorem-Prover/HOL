(*
  quietdec := true;
  val armDir = concat Globals.HOLDIR "/examples/ARM/v4";
  val yaccDir = concat Globals.HOLDIR "/tools/mlyacc/mlyacclib";
  loadPath := !loadPath @ [armDir,yaccDir];
*)

open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory arithmeticTheory wordsLib wordsTheory bitTheory;
open pairTheory listTheory rich_listTheory relationTheory pairTheory addressTheory;
open set_sepTheory set_sepLib progTheory arm_progTheory arm_instTheory arm_progLib;

(*
  quietdec := false;
*)

val _ = new_theory "examples";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
val EQ_IMP_IMP = METIS_PROVE [] ``(x=y) ==> x ==> y``;


(* ----------------------------------------------------------------------------- *)
(* Specialising basic instruction specifications                                 *)
(* ----------------------------------------------------------------------------- *)

val AM1_AM2_PASS_ss = rewrites 
  [ADDR_MODE2_ADDR_def,ADDR_MODE2_WB_def,ADDR_MODE2_ADDR'_def,ADDR_MODE2_WB'_def,
   ADDR_MODE1_VAL_def,ADDR_MODE1_CMD_def,PASS_CASES];

val ARM_PROG_ss = bool_ss ++ sep_ss ++ AM1_AM2_PASS_ss;

val default_varnames = [`a`,`b`,`c`,`d`,`e`,`a1`,`a2`,`a3`,`a4`];
val default_expnames = [`x`,`y`,`z`,`s`,`t`,`x1`,`x2`,`x3`,`x4`];

fun proper_zip [] ys = []
  | proper_zip xs [] = []
  | proper_zip (x::xs) (y::ys) = (x,y) :: proper_zip xs ys;
  
fun SPEC_ARM_RULE_GENERAL th c s vs xs am = let
  fun attempt f x = f x handle e => x
  fun set_am NONE th = th
    | set_am (SOME a) th = Q.INST [`a_mode`|->a] th
  val th = set_am am th 
  val th = attempt (Q.INST [`s_flag:bool`|->s]) th 
  val th = attempt (Q.INST [`c_flag:condition`|->c]) th 
  val th = SIMP_RULE ARM_PROG_ss [FST,SND] th
  fun map_zip ys zs = map (fn (y,z) => y |-> z) (proper_zip ys zs)
  val th = Q.INST (map_zip default_varnames vs) th
  val th = Q.INST (map_zip default_expnames xs) th
  val th = REWRITE_RULE [ARM_PROG2_def] th  
  val (th,th') = (CONJUNCT1 th,CONJUNCT2 th) handle e => (th,th)
  val th' = attempt (SIMP_RULE ARM_PROG_ss [] o SPEC ``(sN:bool,sZ:bool,sC:bool,sV:bool)``) th'
  in (th,th') end;

fun SPEC_ARM_RULEcs th c vs xs am = SPEC_ARM_RULE_GENERAL th c `T` vs xs am;
fun SPEC_ARM_RULEc th c vs xs am = SPEC_ARM_RULE_GENERAL th c `F` vs xs am;
fun SPEC_ARM_RULEs th vs xs am = fst (SPEC_ARM_RULE_GENERAL th `AL` `T` vs xs am);
fun SPEC_ARM_RULE th vs xs am = fst (SPEC_ARM_RULE_GENERAL th `AL` `F` vs xs am);

(* for debugging:
  SPEC_ARM_RULEcs arm_ADD3 `NE` [`s`,`t`,`ttt`] [`x_s`,`x_t`,`x_ttt`] (SOME `OneReg`)
*)




(* ----------------------------------------------------------------------------- *)
(* Setting the environment                                                       *)
(* ----------------------------------------------------------------------------- *)

val AM1_ss = rewrites [ADDR_MODE1_VAL_def,ADDR_MODE1_CMD_def];
val AM2_ss = rewrites [ADDR_MODE2_ADDR_def,ADDR_MODE2_WB_def];
val PASS_ss = rewrites [PASS_CASES];
val ARM_PROG_ss = bool_ss++AM1_ss++AM2_ss++sep_ss++PASS_ss;

fun SET_SC s c = SIMP_RULE ARM_PROG_ss [] o Q.INST [`s_flag:bool`|->s,`c_flag:condition`|->c];
fun SET_AM x = SIMP_RULE ARM_PROG_ss [] o Q.INST [`a_mode`|->x];

val SET_AM2_12 = PROVE [] ``!x:word8. (w2w x) << 2 = ((w2w x) << 2):word12``;
val SET_AM2_30 = PROVE [] ``!x:word8. w2w x = (w2w x):word30``;
val SET_AM2_32 = PROVE [] ``!x:word8. w2w x = (w2w x):word32``;

fun SET_AM2 pre up wb imm = let 
  val rws = [instructionTheory.transfer_options_accessors,
    instructionTheory.transfer_options_accfupds,combinTheory.K_DEF] 
(*    val th1 = (EVAL o fst o dest_eq o concl o Q.SPEC imm) SET_AM2_12 
      val th2 = (EVAL o fst o dest_eq o concl o Q.SPEC imm) SET_AM2_30
      val th3 = (EVAL o fst o dest_eq o concl o Q.SPEC imm) SET_AM2_32  *)
  in
  SIMP_RULE ARM_PROG_ss [(*th1,th2,th3*)] o 
  CONV_RULE (ARM_PROG_PRE_CONV (SIMP_CONV bool_ss rws)) o
  CONV_RULE (ARM_PROG_POST_CONV (SIMP_CONV bool_ss rws)) o
  CONV_RULE (ARM_PROG_POST1_CONV (SIMP_CONV bool_ss rws)) o 
  Q.INST [`pre_default`|->pre,`up_default`|->up,`wb_default`|->wb,`imm`|->imm] o
  Q.INST [`opt`|->`<| Pre:= pre_default; Up:=up_default; Wb:=wb_default |>`] end;

fun SPLIT_PROG2 th = let
  val (x,y) = (CONJ_PAIR o RW [ARM_PROG2_def]) th
  val f = SIMP_RULE (pure_ss++PASS_ss) []
  in (f x,f (Q.ISPEC `(sN:bool,sZ:bool,sC:bool,sV:bool)` y)) end;

val FST_PROG2 = fst o SPLIT_PROG2;
val SND_PROG2 = snd o SPLIT_PROG2;


(* ----------------------------------------------------------------------------- *)
(* Derived loop rules                                                            *)
(* ----------------------------------------------------------------------------- *)

val ARM_PROG_LOOP_DEC = prove(
  ``!P cs C Z. 
      (!v:'var word. ARM_PROG (P v * cond ~(v = 0w)) cs C Q 
                     ((P (v - 1w) * cond ~(v - 1w = 0w),I) INSERT Z)) ==>
      (!v. ARM_PROG (P v * cond ~(v = 0w)) cs C Q Z)``,
  ONCE_REWRITE_TAC [(GSYM o BETA_CONV) ``(\x. P x * cond ~(x:'a word = 0w)) v``]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC ARM_PROG_LOOP_MEASURE
  \\ Q.EXISTS_TAC `w2n` \\ REWRITE_TAC [GSYM WORD_LO]
  \\ FULL_SIMP_TAC std_ss [ARM_PROG_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `!v. b` (ASSUME_TAC o UNDISCH o RW [ARM_PROG_MOVE_COND] o Q.SPEC `v0`)
  \\ (MATCH_MP_TAC o GEN_ALL o RW [AND_IMP_INTRO] o 
      DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL) ARM_PROG_WEAKEN_POST
  \\ Q.EXISTS_TAC `(P (v0 - 1w) * cond ~(v0 - 1w = 0w))` \\ ASM_REWRITE_TAC []
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `v0 - 1w`
  \\ ASM_SIMP_TAC bool_ss [WORD_PRED_THM,WORD_LO]);


(* ----------------------------------------------------------------------------- *)
(* Count down loop                                                               *)
(* ----------------------------------------------------------------------------- *)

val ARM_DOWN_LOOP = let
  val th1 = (*  subs a,a,#1   *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`Imm 1w`] arm_SUB1))
  val th2 = (*  bne <offset>  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (13w :word24) :word30)``, EVAL ``(13w :word30) + (2w :word30)``] (Q.INST [`c_flag`|->`NE`] arm_B)
  val th = FRAME_COMPOSE th1 (MATCH_INST1 [`S`] th1 th2)
  val th = AUTO_HIDE_STATUS th
  val form = (SPEC_ALL o ASSUME)
                ``!x. ARM_PROG (Inv x * R a x * ~S * cond ~(x = 0w)) code C 
                               (Inv (x - 1w) * R a x * ~S) {}``
  val th = FRAME_COMPOSE form th
  val th = DISCH ``sw2sw(offset:word24)+2w+1w+n2w (LENGTH (code:word32 list))=0w:word30`` th
  val th = UNDISCH (SIMP_RULE bool_ss [pcADD_0] th)
  val th = APP_WEAKEN1 th `Inv (0w:word32) * R a 0w * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,WORD_SUB_REFL]
    \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = APP_WEAKEN th `(\x. Inv x * R a x * ~S) (x - 1w) * cond ~(x - 1w = 0w)`
    (SIMP_TAC (bool_ss++star_ss) [WORD_EQ_SUB_ZERO,SEP_IMP_REFL])
  val th = APP_STRENGTHEN th `(\x. Inv x * R a x * ~S) x * cond ~(x = 0w)`
    (SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = Q.GEN `v` (Q.INST [`x`|->`v`] th)
  val th = Q.SPEC `x` (MATCH_MP ARM_PROG_LOOP_DEC th)
  val th = DISCH_ALL (PAT_DISCH ``x=y:'a`` (BETA_RULE th))
in th end;    


(* ----------------------------------------------------------------------------- *)
(* Factorial program                                                             *)
(* ----------------------------------------------------------------------------- *)

val FAC_def = Define `(FAC 0 = 1) /\ (FAC (SUC n) = SUC n * FAC n)`;

val ZERO_LESS_FAC = prove(
  ``!n. 0 < FAC n``,
  Induct \\ SRW_TAC [] [FAC_def,ZERO_LESS_MULT]);

val FAC_DECOMPOSE = prove(
  ``!n m. SUC n <= m ==> ?k. FAC m = k * SUC n * FAC n``,
  REPEAT STRIP_TAC
  \\ `?p. m = SUC n + p` by METIS_TAC [LESS_EQUAL_ADD]
  \\ ASM_REWRITE_TAC []
  \\ POP_ASSUM_LIST (fn thms => ALL_TAC)
  \\ Induct_on `p` << [
    REWRITE_TAC [ADD_0,FAC_def]
    \\ Q.EXISTS_TAC `1`
    \\ SIMP_TAC std_ss [],
    `SUC n + SUC p = SUC (SUC n + p)` by METIS_TAC [ADD1,ADD_ASSOC]
    \\ POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC)
    \\ ASM_REWRITE_TAC [FAC_def]
    \\ Q.EXISTS_TAC `SUC (SUC n + p) * k`
    \\ REWRITE_TAC [MULT_ASSOC]]);

val FAC_MOD_LEMMA = prove(
  ``!n m. SUC n <= m ==> ((FAC m DIV FAC n) MOD SUC n = 0)``,
  REPEAT STRIP_TAC
  \\ `?k. FAC m = k * SUC n * FAC n` by METIS_TAC [FAC_DECOMPOSE]
  \\ ASM_SIMP_TAC std_ss [ZERO_LESS_FAC,MULT_DIV]
  \\ METIS_TAC [MOD_EQ_0,DECIDE ``0 < SUC n``]);

val FAC_STEP_LEMMA = prove(
  ``!n m. ~(n = 0) /\ n <= m ==> 
          (FAC m DIV FAC n * n = FAC m DIV FAC (n - 1))``,
  Cases \\ SIMP_TAC std_ss [FAC_def]
  \\ REWRITE_TAC [DECIDE ``SUC n * m = m * SUC n``]
  \\ SIMP_TAC std_ss [GSYM DIV_DIV_DIV_MULT,ZERO_LESS_FAC]
  \\ METIS_TAC [DIVISION,FAC_MOD_LEMMA,DECIDE ``0 < SUC n``,ADD_0]);

val wFAC_def = Define `wFAC w = n2w (FAC (w2n w))`;
val RFAC_def = Define `RFAC m n = FAC m DIV FAC n`;

val RFAC_0 = prove(
  ``!m. RFAC m 0 = FAC m``,
  SRW_TAC [] [FAC_def,RFAC_def]);

val RFAC_EQ_1 = prove(
  ``!m. RFAC m m = 1``,
  SRW_TAC [] [RFAC_def,DIVMOD_ID,ZERO_LESS_FAC]);

val FAC_INV_def = Define `
  FAC_INV a n = \x. R a (n2w (RFAC n (w2n x))) * cond (w2n x <= n)`;

val FAC_INV_ID = prove(
  ``FAC_INV b (w2n x) x = R b 1w``,
  SIMP_TAC (bool_ss++sep_ss) [FAC_INV_def,RFAC_def,DIVMOD_ID,ZERO_LESS_FAC,LESS_EQ_REFL])

val FAC_INV_ZERO = prove(
  ``FAC_INV b (w2n x) 0w = R b (wFAC x)``,
  SIMP_TAC (bool_ss++sep_ss) [FAC_INV_def,RFAC_def,word_0_n2w,
    ZERO_LESS_EQ,FAC_def,wFAC_def,DIV_1]);
 

(* ------------ *)

val ARM_BASIC_FAC = let
  val th = (*  mul b,a,b  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`x`|->`x1`,`y`|->`y1` ] arm_MUL2))
  val th = AUTO_HIDE_STATUS th
  val th = APP_FRAME `cond (w2n (x:word32) <= n) * cond ~(x = 0w)` th
  val th = RW1 [WORD_MULT_COMM] th
  val th = Q.INST [`y1`|->`n2w (RFAC n (w2n x))`,`x1`|->`x`] th
  val th = APP_WEAKEN1 th `FAC_INV b n (x-1w) * R a x * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [FAC_INV_def,SEP_IMP_MOVE_COND] \\ STRIP_TAC            
    \\ `w2n (x-1w) < w2n x` by ASM_SIMP_TAC bool_ss [WORD_PRED_THM]   
    \\ `w2n (x-1w) <= n` by DECIDE_TAC \\ ASM_SIMP_TAC (bool_ss++sep_ss) []
    \\ `w2n (x-1w) = w2n x - 1` by METIS_TAC [DECIDE ``SUC n - 1 = n``,SUC_WORD_PRED]
    \\ FULL_SIMP_TAC bool_ss [GSYM w2n_eq_0,RFAC_def]    
    \\ IMP_RES_TAC (RW [GSYM AND_IMP_INTRO] FAC_STEP_LEMMA)
    \\ Q.PAT_ASSUM `z12341 = FAC n DIV FAC (w2n x - 1)` (ASSUME_TAC o GSYM)    
    \\ ASM_REWRITE_TAC [GSYM word_mul_n2w,n2w_w2n]
    \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = APP_STRENGTHEN th `FAC_INV b n x * R a x * ~S * cond ~(x = 0w)`
   (SIMP_TAC (bool_ss++star_ss) [FAC_INV_def,SEP_IMP_REFL])
  val th = MATCH_MP ARM_DOWN_LOOP (Q.GEN `x` th)
  val th = Q.INST [`offset`|->`0w-4w`] th
  val th = SIMP_RULE std_ss [APPEND] (CONV_RULE (RATOR_CONV EVAL) th)
  val th = RW [EVAL ``0w - 4w :word24``] th
  val th = Q.INST [`n`|->`w2n (x:word32)`] th
  val th = RW [FAC_INV_ID,FAC_INV_ZERO] th  
in th end;

val ARM_FAC_PROGRAM = let
  val th = (*  mov b,#1  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`b`,`a_mode`|->`Imm 1w`,`x`|->`x1` ] arm_MOV1))
  val th = AUTO_HIDE_STATUS th
  val th = FRAME_COMPOSE th ARM_BASIC_FAC
  val th = (SIMP_RULE (bool_ss++sep2_ss) [] o MOVE_PRE `S` o AUTO_HIDE_PRE [`R b`]) th
  val th = (MOVE_POST1 `S` o MOVE_POST1 `R b`) th
in th end;



(* verified implementations:

fac1:

  MOV    a,  #1
  MUL    a,  b,  a
  SUBS   b,  b,  #1
  BNE    -2

*)


(* ----------------------------------------------------------------------------- *)
(* GCD program                                                                   *)
(* ----------------------------------------------------------------------------- *)

(* GCD over num *)

val GCD_defn = Hol_defn "GCD"
   `(GCD (0,n) = n) /\
    (GCD (m,n) = GCD (n MOD m, m))`;

val (GCD_def,GCD_ind) = Defn.tprove(GCD_defn, 
  WF_REL_TAC `measure FST` \\ METIS_TAC [DIVISION,DECIDE ``0 < SUC n``]);

val GCD_REFL = prove(
  ``!m. GCD (m,m) = m``,
  Cases \\ SRW_TAC [] [GCD_def]);

val GCD_SYM = prove(
  ``!m n. GCD (m,n) = GCD (n,m)``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPECL [`m`,`n`] LESS_LESS_CASES)
  \\ ASM_REWRITE_TAC [] << [
    Cases_on `n` THEN1 DECIDE_TAC \\ ASM_SIMP_TAC std_ss [GCD_def,LESS_MOD],
    Cases_on `m` THEN1 DECIDE_TAC \\ ASM_SIMP_TAC std_ss [GCD_def,LESS_MOD]]);
    
val GCD_SUB_RIGHT = prove(
  ``!m n. m < n ==> (GCD (m,n-m) = GCD (m,n))``,
  Cases \\ SRW_TAC [] [GCD_def]
  \\ METIS_TAC [ADD_MODULUS,DECIDE ``!n. 0 < SUC n``,LESS_IMP_LESS_OR_EQ,SUB_ADD]);

val GCD_SUB_LEFT = prove(
  ``!m n. n < m ==> (GCD (m-n,n) = GCD (m,n))``,
  METIS_TAC [GCD_SYM,GCD_SUB_RIGHT]);


(* GCD over word *)

val wGCD_def = Define `wGCD (x,y) = n2w (GCD (w2n (x:'a word),w2n (y:'a word))):'a word`;

val wGCD_REFL = prove(``!x. wGCD (x,x) = x``,REWRITE_TAC [wGCD_def,GCD_REFL,n2w_w2n]);

val wGCD_SUB_RIGHT = prove(
  ``!x y. x <+ y ==> (wGCD (x,y-x) = wGCD (x,y))``,
  SIMP_TAC std_ss [WORD_LOWER_IMP_LOWER_OR_EQ,word_sub_w2n,wGCD_def,WORD_LO,GCD_SUB_RIGHT]);

val wGCD_SUB_LEFT = prove(
  ``!x y. y <+ x ==> (wGCD (x-y,y) = wGCD (x,y))``,
  SIMP_TAC std_ss [WORD_LOWER_IMP_LOWER_OR_EQ,word_sub_w2n,wGCD_def,WORD_LO,GCD_SUB_LEFT]);


(* the GCD program *)

val WORD_GT = let 
    val th = SIMP_RULE std_ss [nzcv_def,LET_DEF,GSYM word_add_def,GSYM word_sub_def] word_gt_def
    val th = SPEC_ALL th
    val th = CONV_RULE (funpow 5 RAND_CONV SYM_CONV) th
  in RW [WORD_EQ_SUB_ZERO] (GSYM th) end;

val WORD_LT = let 
    val th = SIMP_RULE std_ss [nzcv_def,LET_DEF,GSYM word_add_def,GSYM word_sub_def] word_lt_def
    val th = SPEC_ALL th
    val th = CONV_RULE (funpow 5 RAND_CONV SYM_CONV) th
  in RW [WORD_EQ_SUB_ZERO] (GSYM th) end;

val ARM_GCD_PROGRAM = let

  (* instantiation of the commands *)

  val cmp = FST_PROG2 (SET_AM `OneReg` (SET_SC `T` `AL` arm_CMP2))
  val cmp = GENL [``sN:bool``,``sZ:bool``,``sC:bool``,``sV:bool``] cmp
  val cmp = RW [EVAL ``(w2w (0w:word8)):word32``,ARM_PROG_HIDE_STATUS] cmp

  val instS = Q.INST [`sN:bool`|->`word_msb (x - y:word32)`,
                      `sZ:bool`|->`x = y:word32`,
                      `sC:bool`|->`y <=+ x:word32`,
                      `sV:bool`|->`~(word_msb x = word_msb y) /\ 
                                   ~(word_msb x = word_msb (x - y:word32))`]
  val instS = PURE_REWRITE_RULE [WORD_GT,WORD_LT] o instS

  val subGT = SET_AM `OneReg` (SET_SC `F` `GT` arm_SUB2')
  val (subGT,subGT_nop) = SPLIT_PROG2 subGT
  val (subGT,subGT_nop) = (instS subGT,instS subGT_nop)

  val subLT = SET_AM `OneReg` (SET_SC `F` `LT` arm_SUB2')
  val subLT = Q.INST [`a`|->`b`,`b`|->`a`,`x`|->`y`,`y`|->`x`] subLT
  val subLT = MOVE_STAR_RULE `b*a*s (x,y,z,q)` `a*b*s (x,y,z,q)` subLT
  val (subLT,subLT_nop) = SPLIT_PROG2 subLT
  val (subLT,subLT_nop) = (instS subLT,instS subLT_nop)

  val bne = SET_SC `F` `NE` arm_B
  val bne = RW1 [STAR_SYM] bne  
  val bne = MATCH_MP ARM_PROG_HIDE_POST1 bne
  val bne = MATCH_MP ARM_PROG_HIDE_POST bne
  val bne = RW1 [STAR_SYM] bne  
  val bne = instS bne

  (* apply frame *)

  val APP_FRAME = REWRITE_RULE [setSTAR_CLAUSES] o MATCH_MP ARM_PROG_FRAME 
  val cmp_f = APP_FRAME cmp
  val subGT_f = APP_FRAME subGT
  val subGT_nop_f = APP_FRAME subGT_nop
  val subLT_f = APP_FRAME subLT
  val subLT_nop_f = APP_FRAME subLT_nop
  val bne_f = APP_FRAME bne

  (* case x = y *)

  val subGT_SIMP = prove(
    ``!x y:word32. ~(x > y) /\ (x = y) = (x = y)``,
    METIS_TAC [WORD_GREATER,WORD_LESS_REFL])

  val subLT_SIMP = prove(
    ``!x y:word32. ~(x < y) /\ (x = y) = (x = y)``,
    METIS_TAC [WORD_GREATER,WORD_LESS_REFL])

  val bne1_SIMP = REWRITE_CONV [NOT_AND,Once CONJ_SYM] ``~b /\ b:bool``

  val cmp1 = Q.SPEC `cond (x = y:word32)` cmp_f
  val subGT1 = Q.SPEC `R a x * R b y * cond (x = y:word32)` subGT_nop_f
  val subLT1 = Q.SPEC `R a x * R b y * cond (x = y:word32)` subLT_nop_f
  val bne1 = Q.SPEC `R a x * R b y * cond (x = y:word32)` bne_f
  val subGT1 = SIMP_RULE (std_ss++SEP_cond_ss) [subGT_SIMP] subGT1
  val subLT1 = SIMP_RULE (std_ss++SEP_cond_ss) [subLT_SIMP] subLT1
  val bne1 = SIMP_RULE (std_ss++SEP_cond_ss) [bne1_SIMP,SEP_cond_CLAUSES,F_STAR] bne1
  val bne1 = RW [ARM_PROG_FALSE_POST] (RW1 [INSERT_COMM] bne1)
  val reorder = MOVE_STAR_RULE `s*a*b*c` `a*b*s*c`

  val th1 = cmp1
  val th1 = MATCH_COMPOSE th1 (reorder subGT1)
  val th1 = MATCH_COMPOSE th1 (reorder subLT1)
  val th1 = MATCH_COMPOSE th1 (reorder bne1)

  (* case x > y *)  
  
  val subLT2_SIMP = prove(
    ``!x y:word32. ~(x < y) /\ x > y = x > y``,
    METIS_TAC [WORD_GREATER,WORD_LESS_ANTISYM]);

  val bne2_SIMP = prove(
    ``!x y:word32. ((x = y) /\ x > y = F) /\ (~(x = y) /\ x > y = x > y)``,
    METIS_TAC [WORD_GREATER,WORD_LESS_REFL]);

  val cmp2 = Q.SPEC `cond (x > y:word32)` cmp_f
  val subGT2 = Q.SPEC `cond (x > y:word32)` subGT_f
  val subLT2 = Q.SPEC `R a (x - y) * R b y * cond (x > y:word32)` subLT_nop_f
  val bne2 = Q.SPEC `R a (x - y) * R b y * cond (x > y:word32)` bne_f
  val subGT2 = SIMP_RULE (std_ss++SEP_cond_ss) [] subGT2
  val subLT2 = SIMP_RULE (std_ss++SEP_cond_ss) [subLT2_SIMP] subLT2
  val bne2 = SIMP_RULE (std_ss++SEP_cond_ss) [bne2_SIMP,SEP_cond_CLAUSES,F_STAR,ARM_PROG_FALSE_POST] bne2
  val reorder = MOVE_STAR_RULE `s*a*b*c` `a*b*s*c`
  
  val th2 = cmp2
  val th2 = MATCH_COMPOSE th2 subGT2
  val th2 = MATCH_COMPOSE th2 (reorder subLT2)
  val th2 = MATCH_COMPOSE th2 (reorder bne2)

  (* case x < y *)  
  
  val subGT3_SIMP = prove(
    ``!x y:word32. ~(x > y) /\ x < y = x < y``,
    METIS_TAC [WORD_GREATER,WORD_LESS_ANTISYM]);

  val bne3_SIMP = prove(
    ``!x y:word32. ((x = y) /\ x < y = F) /\ (~(x = y) /\ x < y = x < y)``,
    METIS_TAC [WORD_GREATER,WORD_LESS_REFL]);

  val cmp3 = Q.SPEC `cond (x < y:word32)` cmp_f
  val subGT3 = Q.SPEC `R a x * R b y * cond (x < y:word32)` subGT_nop_f
  val subLT3 = Q.SPEC `cond (x < y:word32)` subLT_f
  val bne3 = Q.SPEC `R a x * R b (y - x) * cond (x < y:word32)` bne_f
  val subGT3 = SIMP_RULE (std_ss++SEP_cond_ss) [subGT3_SIMP] subGT3
  val subLT3 = SIMP_RULE (std_ss++SEP_cond_ss) [] subLT3
  val bne3 = SIMP_RULE (std_ss++SEP_cond_ss) [bne3_SIMP,SEP_cond_CLAUSES,F_STAR,ARM_PROG_FALSE_POST] bne3
  val reorder = MOVE_STAR_RULE `s*a*b*c` `a*b*s*c`
  
  val th3 = cmp3
  val th3 = MATCH_COMPOSE th3 (reorder subGT3)
  val th3 = MATCH_COMPOSE th3 subLT3
  val th3 = MATCH_COMPOSE th3 (reorder bne3)

  (* introducing the invariant *)

  val GCD_INV_def = Define `
    GCD_INV a b (x0:word32,y0:word32) (x:word32,y:word32) = 
      R a x * R b y * ~S * cond ((wGCD(x0,y0) = wGCD(x,y)) /\ (0w < x) /\ (0w < y))`;

  val APP_INV = Q.SPEC `cond ((wGCD(x0,y0)=wGCD(x,y))/\(0w<x:word32)/\(0w<y:word32))` o APP_FRAME

  val th1 = APP_INV th1
  val th2 = APP_INV th2
  val th3 = APP_INV th3

  val th1 = APP_STRENGTHEN th1 `GCD_INV a b (x0,y0) (x,y) * cond (x = y:word32)`
              (SIMP_TAC ARM_PROG_ss [GCD_INV_def,SEP_IMP_MOVE_COND,SEP_IMP_REFL])

  val th2 = APP_STRENGTHEN th2 `GCD_INV a b (x0,y0) (x,y) * cond (x > y:word32)`
              (SIMP_TAC ARM_PROG_ss [GCD_INV_def,SEP_IMP_MOVE_COND,SEP_IMP_REFL])

  val th3 = APP_STRENGTHEN th3 `GCD_INV a b (x0,y0) (x,y) * cond (x < y:word32)`
              (SIMP_TAC ARM_PROG_ss [GCD_INV_def,SEP_IMP_MOVE_COND,SEP_IMP_REFL])

  val wMAXn_def = Define `wMAXn (x,y) = MAX (w2n x) (w2n y)`;
  
  val WORD_LT_EQ_LO2 = prove(
    ``!x y. 0w < x /\ 0w < y ==> (x < y = x <+ y)``,
    REPEAT STRIP_TAC
    \\ MATCH_MP_TAC WORD_LT_EQ_LO
    \\ ASM_SIMP_TAC std_ss [WORD_LESS_IMP_LESS_OR_EQ]);

  val wMAXn_COMM = 
        prove(``!x y. wMAXn (x,y) = wMAXn (y,x)``,SRW_TAC [] [wMAXn_def,MAX_COMM]);

  val wMAXn_SUB = prove(
    ``!x y. 0w < y /\ y < x ==> wMAXn (x-y,y) < wMAXn (x,y)``,
    REWRITE_TAC [wMAXn_def,MAX_DEF,GSYM WORD_LO] \\ REPEAT STRIP_TAC
    \\ `y <+ x` by METIS_TAC [WORD_LT_EQ_LO2,WORD_LESS_TRANS]
    \\ `~(x <+ y)` by METIS_TAC [WORD_LO,LESS_ANTISYM]
    \\ Cases_on `x - y <+ y` \\ ASM_REWRITE_TAC [GSYM WORD_LO]
    \\ `0w < x - y /\ x - y < x` by METIS_TAC [WORD_SUB_LT]
    \\ `0w < x` by METIS_TAC [WORD_LESS_TRANS]
    \\ METIS_TAC [WORD_LT_EQ_LO2]);

  val th1 = APP_WEAKEN1 th1 `R a (wGCD(x0,y0)) * R b (wGCD(x0,y0)) * ~S`
              (REWRITE_TAC [SEP_IMP_MOVE_COND] \\ METIS_TAC [wGCD_REFL,SEP_IMP_REFL])

  val th2 = APP_WEAKEN th2 `GCD_INV a b (x0,y0) (x-y,y) * cond (wMAXn (x-y,y) < wMAXn (x,y))`
    (REWRITE_TAC [GCD_INV_def,SEP_IMP_MOVE_COND,WORD_GREATER]
     \\ SIMP_TAC bool_ss [GSYM WORD_LO,WORD_SUB_LT] \\ REPEAT STRIP_TAC  
     \\ `y <+ x` by METIS_TAC [WORD_LT_EQ_LO,WORD_LESS_IMP_LESS_OR_EQ]
     \\ ASM_SIMP_TAC (bool_ss++sep_ss) [wGCD_SUB_LEFT,GSYM WORD_LO,wMAXn_SUB,SEP_IMP_REFL])

  val th3 = APP_WEAKEN th3 `GCD_INV a b (x0,y0) (x,y-x) * cond (wMAXn (x,y-x) < wMAXn (x,y))`
    (REWRITE_TAC [GCD_INV_def,SEP_IMP_MOVE_COND,WORD_GREATER]
     \\ SIMP_TAC bool_ss [GSYM WORD_LO,WORD_SUB_LT] \\ REPEAT STRIP_TAC  
     \\ `x <+ y` by METIS_TAC [WORD_LT_EQ_LO,WORD_LESS_IMP_LESS_OR_EQ]
     \\ ASM_SIMP_TAC (bool_ss++sep_ss) 
            [RW1 [wMAXn_COMM] wMAXn_SUB,wGCD_SUB_RIGHT,SEP_IMP_REFL])
  
  val th2 = APP_WEAKEN th2 
    `SEP_EXISTS v. GCD_INV a b (x0,y0) v * cond (wMAXn v < wMAXn (x:word32,y:word32))`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  
  val th3 = APP_WEAKEN th3 
    `SEP_EXISTS v. GCD_INV a b (x0,y0) v * cond (wMAXn v < wMAXn (x:word32,y:word32))`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])

  val th2 = SIMP_RULE (bool_ss++sep_ss) [] th2  
  val th3 = SIMP_RULE (bool_ss++sep_ss) [] th3  

  (* collect parts *)

  val th123 = APP_MERGE th1 (APP_MERGE th2 th3)
  val lemma = METIS_PROVE [WORD_LESS_LESS_CASES,WORD_GREATER] ``(x=y) \/ x>y \/ x<y:word32 = T``
  val th123 = SIMP_RULE (bool_ss++sep_ss) [lemma,STAR_OVER_DISJ] th123
  val th123 = PAIR_GEN "x" `(x,y)` th123
  val th123 = Q.INST [`offset`|->`0w-5w`] th123
  val th123 = RW [EVAL ``sw2sw (0w-5w:word24) + 2w + 3w:word30``,pcADD_0] th123
  val th123 = MATCH_MP ARM_PROG_LOOP_MEASURE th123
  val th123 = Q.SPEC `(x,y)` th123
  val th123 = RW [GCD_INV_def] (Q.INST [`x0`|->`x`,`y0`|->`y`] th123)
  val th123 = RW [GSYM (REWRITE_CONV [SEP_cond_CLAUSES] ``cond x * cond y``),STAR_ASSOC] th123  

in th123 end;



val GCD_INV_def = Define `
  GCD_INV a b (x0:word32,y0:word32) (x:word32,y:word32) = 
    R a x * R b y * ~S * cond ((wGCD(x0,y0) = wGCD(x,y)) /\ ~(x = 0w) /\ ~(y = 0w))`;

val wMAXn_def = Define `wMAXn (x,y) = MAX (w2n x) (w2n y)`;

val wMAXn_LESS = prove(
  ``!x y. ~(y = 0w) /\ y <+ x ==> wMAXn (x-y,y) < wMAXn (x,y)``,
  REWRITE_TAC [wMAXn_def,MAX_DEF,GSYM WORD_LO] \\ REPEAT STRIP_TAC
  \\ `~(x <+ y)` by METIS_TAC [WORD_LO,LESS_ANTISYM]
  \\ Cases_on `x - y <+ y` \\ ASM_REWRITE_TAC [GSYM WORD_LO]
  \\ IMP_RES_TAC WORD_LOWER_IMP_LOWER_OR_EQ
  \\ ASM_SIMP_TAC bool_ss [word_sub_w2n,WORD_LO]
  \\ FULL_SIMP_TAC bool_ss [word_sub_w2n,WORD_LO,GSYM w2n_eq_0]
  \\ DECIDE_TAC);

val wMAXn_COMM = prove(
  ``!x y. wMAXn (x,y) = wMAXn (y,x)``,
  REWRITE_TAC [wMAXn_def] \\ METIS_TAC [MAX_COMM]);

val ARM_GCD_PROGRAM_BETTER = let
  val l2 = prove(``1073741824w = 0w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val g = SIMP_RULE (pure_ss++sep2_ss) [WORD_SUB_ADD]

  (*
  compose_progs'
  [("subs  a,a,b",true),
   ("addcc a,a,b",true),
   ("subcc b,b,a",true),
   ("bne -12",false)] "th" "  "
  *)

  (* case: a < b *)
  val th1 = (*  subs  a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_SUB2') 
  val th2 = (*  addcc a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_ADD2') 
  val th3 = (*  subcc b,b,a  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`a`|->`b`,`b`|->`a`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_SUB2') 
  val th4 = (*  bne -12  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(sw2sw (16777211w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`16777211w` ] arm_B2) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(x2 :word32)`|->`(x1 :word32) - (y1 :word32)`,`(y2 :word32)`|->`(y1 :word32)`,`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (FST_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(y3 :word32)`|->`(x1 :word32) - (y1 :word32) + y1`,`(x3 :word32)`|->`(y1 :word32)`,`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (FST_PROG2 th4))
  val th = g (AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th))
  val lemma1 = prove(``~(y1 <=+ x1) /\ ~(x1 = y1) = x1 <+ y1``,METIS_TAC [GSYM WORD_NOT_LOWER,WORD_LOWER_OR_EQ])
  val th = RW [lemma1] (RW [CONJ_ASSOC] th)
  val th = UNDISCH (RW [ARM_PROG_MOVE_COND] th)
  val th = APP_FRAME `cond (x1 <+ y1 /\ (wGCD(x0,y0:word32) = wGCD(x1,y1)) /\ ~(x1 = 0w) /\ ~(y1 = 0w))` th
  val th = APP_WEAKEN th `GCD_INV a b (x0,y0) (x1,y1-x1)`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_MOVE_COND,wGCD_SUB_RIGHT,GCD_INV_def,WORD_EQ_SUB_ZERO,WORD_LOWER_NOT_EQ] \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = SIMP_RULE bool_ss [l2,pcADD_0,GSYM GCD_INV_def] (DISCH_ALL th)
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_FRAME `cond (x1 <+ (y1:word32))` th
  val th = SIMP_RULE (std_ss++sep2_ss) [] th
  val t1 = APP_WEAKEN th `SEP_EXISTS x. GCD_INV a b (x0,y0) x * cond (wMAXn x < wMAXn (x1:word32,y1:word32))`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ REPEAT STRIP_TAC
     \\ Q.EXISTS_TAC `(x1,y1-x1)` \\ ONCE_REWRITE_TAC [wMAXn_COMM]
     \\ ASM_REWRITE_TAC [] \\ MATCH_MP_TAC wMAXn_LESS     
     \\ FULL_SIMP_TAC bool_ss [GCD_INV_def,cond_STAR])

  (* case: b < a *)
  val th1 = (*  subs  a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_SUB2') 
  val th2 = (*  addcc a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_ADD2') 
  val th3 = (*  subcc b,b,a  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`a`|->`b`,`b`|->`a`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_SUB2') 
  val th4 = (*  bne -12  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(sw2sw (16777211w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`16777211w` ] arm_B2) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (SND_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (FST_PROG2 th4))
  val th = g (AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th))
  val lemma1 = prove(``(y1 <=+ x1) /\ ~(x1 = y1) = y1 <+ x1``,METIS_TAC [GSYM WORD_NOT_LOWER,WORD_LOWER_OR_EQ])
  val th = RW [lemma1] (RW [CONJ_ASSOC] th)
  val th = UNDISCH (RW [ARM_PROG_MOVE_COND] th)
  val th = APP_FRAME `cond (y1 <+ x1 /\ (wGCD(x0,y0:word32) = wGCD(x1,y1)) /\ ~(x1 = 0w) /\ ~(y1 = 0w))` th  
  val th = APP_WEAKEN th `GCD_INV a b (x0,y0) (x1-y1,y1)`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_MOVE_COND,wGCD_SUB_LEFT,GCD_INV_def,WORD_EQ_SUB_ZERO,WORD_LOWER_NOT_EQ] \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = SIMP_RULE bool_ss [l2,pcADD_0,GSYM GCD_INV_def] (DISCH_ALL th)
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_FRAME `cond (y1 <+ (x1:word32))` th
  val th = SIMP_RULE (std_ss++sep2_ss) [] th
  val t2 = APP_WEAKEN th `SEP_EXISTS x. GCD_INV a b (x0,y0) x * cond (wMAXn x < wMAXn (x1:word32,y1:word32))`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ REPEAT STRIP_TAC
     \\ Q.EXISTS_TAC `(x1-y1,y1)` \\ ASM_REWRITE_TAC [] \\ MATCH_MP_TAC wMAXn_LESS     
     \\ FULL_SIMP_TAC bool_ss [GCD_INV_def,cond_STAR])

  (* case: a=b *)
  val th1 = (*  subs  a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_SUB2') 
  val th2 = (*  addcc a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_ADD2') 
  val th3 = (*  subcc b,b,a  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`a`|->`b`,`b`|->`a`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_SUB2') 
  val th4 = (*  bne -12  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(sw2sw (16777211w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`16777211w` ] arm_B2) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (SND_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (SND_PROG2 th4))
  val th = g (AUTO_PRE_HIDE_STATUS (AUTO_POST1_HIDE_STATUS th))
  val lemma1 = prove(``(y1 <=+ x1) /\ (x1 = y1) = (x1 = y1)``,METIS_TAC [GSYM WORD_NOT_LOWER,WORD_LOWER_OR_EQ])
  val th = RW [lemma1] (RW [CONJ_ASSOC] th)
  val th = UNDISCH (RW [ARM_PROG_MOVE_COND] th)
  val th = APP_FRAME `cond ((x1 = y1) /\ (wGCD(x0,y0) = wGCD(x1,y1:word32)) /\ ~(x1 = 0w) /\ ~(y1 = 0w))` th  
  val th = APP_WEAKEN1 th `R a 0w * R b (wGCD (x0,y0)) * ~S`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_MOVE_COND,SEP_IMP_REFL,GSYM AND_IMP_INTRO,wGCD_REFL,WORD_SUB_REFL,WORD_EQ_SUB_ZERO,WORD_LOWER_NOT_EQ])   
  val th = DISCH_ALL th
  val th = RW [ARM_PROG_MOVE_COND,AND_IMP_INTRO,CONJ_ASSOC] th
  val th = RW1 [GSYM ARM_PROG_MOVE_COND] (RW1 [GSYM AND_IMP_INTRO] (RW [GSYM CONJ_ASSOC] th))
  val th = RW [GSYM GCD_INV_def] th

  (* cases together *)
  val t12 = APP_MERGE t1 t2
  val th = APP_MERGE t12 (RW [GSYM ARM_PROG_MOVE_COND] th)
  val lemma = prove(``(x1 <+ y1 \/ y1 <+ x1) \/ (x1 = y1)``,METIS_TAC [WORD_LOWER_LOWER_CASES])
  val th = SIMP_RULE (bool_ss++sep_ss) [lemma] th 
  val th = PAIR_GEN "y" `(x1,y1)` th
  val th = MATCH_MP ARM_PROG_LOOP_MEASURE th
  val th = RW [GCD_INV_def] (Q.INST [`x0`|->`x`,`y0`|->`y`] (Q.SPEC `(x0,y0)` th))
  val th = RW [GSYM (REWRITE_CONV [SEP_cond_CLAUSES] ``cond x * cond y``),STAR_ASSOC] th  
  
  in th end;


val ARM_GCD_PROGRAM_FIXED = let
  val l2 = prove(``1073741824w = 0w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val g = SIMP_RULE (pure_ss++sep2_ss) [WORD_SUB_ADD]

  (*
  compose_progs'
  [("subs  a,a,b",true),
   ("addls a,a,b",false),
   ("subcc b,b,a",false),
   ("bne -12",true)] "th" "  "
  *)

  (* case: a < b *)
  val th1 = (*  subs  a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_SUB2') 
  val th2 = (*  addls a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`LS`,`s_flag`|->`F`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_ADD2') 
  val th3 = (*  subcc b,b,a  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`a`|->`b`,`b`|->`a`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_SUB2') 
  val th4 = (*  bne -12  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(sw2sw (16777211w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`16777211w` ] arm_B2) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(x2 :word32)`|->`(x1 :word32) - (y1 :word32)`,`(y2 :word32)`|->`(y1 :word32)`,`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (FST_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(y3 :word32)`|->`(x1 :word32) - (y1 :word32) + y1`,`(x3 :word32)`|->`(y1 :word32)`,`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (FST_PROG2 th4))
  val th = g (AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th))
  val lemma1 = prove(``((~(y1 <=+ x1) \/ (x1 = y1)) /\ ~(y1 <=+ x1) /\ ~(x1 = y1)) = x1 <+ y1``,METIS_TAC [GSYM WORD_NOT_LOWER,WORD_LOWER_OR_EQ])
  val th = RW [lemma1] th
  val th = UNDISCH (RW [ARM_PROG_MOVE_COND] th)
  val th = APP_FRAME `cond (x1 <+ y1 /\ (wGCD(x0,y0:word32) = wGCD(x1,y1)) /\ ~(x1 = 0w) /\ ~(y1 = 0w))` th  
  val th = APP_WEAKEN th `GCD_INV a b (x0,y0) (x1,y1-x1)`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_MOVE_COND,wGCD_SUB_RIGHT,GCD_INV_def,WORD_EQ_SUB_ZERO,WORD_LOWER_NOT_EQ] \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = SIMP_RULE bool_ss [l2,pcADD_0,GSYM GCD_INV_def] (DISCH_ALL th)
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_FRAME `cond (x1 <+ (y1:word32))` th
  val th = SIMP_RULE (std_ss++sep2_ss) [] th
  val t1 = APP_WEAKEN th `SEP_EXISTS x. GCD_INV a b (x0,y0) x * cond (wMAXn x < wMAXn (x1:word32,y1:word32))`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ REPEAT STRIP_TAC
     \\ Q.EXISTS_TAC `(x1,y1-x1)` \\ ONCE_REWRITE_TAC [wMAXn_COMM]
     \\ ASM_REWRITE_TAC [] \\ MATCH_MP_TAC wMAXn_LESS     
     \\ FULL_SIMP_TAC bool_ss [GCD_INV_def,cond_STAR])

  (* case: b < a *)
  val th1 = (*  subs  a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_SUB2') 
  val th2 = (*  addls a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`LS`,`s_flag`|->`F`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_ADD2') 
  val th3 = (*  subcc b,b,a  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`a`|->`b`,`b`|->`a`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_SUB2') 
  val th4 = (*  bne -12  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(sw2sw (16777211w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`16777211w` ] arm_B2) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (SND_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (FST_PROG2 th4))
  val th = g (AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th))
  val lemma1 = prove(``(y1 <=+ x1) /\ ~(x1 = y1) = y1 <+ x1``,METIS_TAC [GSYM WORD_NOT_LOWER,WORD_LOWER_OR_EQ])
  val th = RW [lemma1] (RW [CONJ_ASSOC] th)
  val th = UNDISCH (RW [ARM_PROG_MOVE_COND] th)
  val th = APP_FRAME `cond (y1 <+ x1 /\ (wGCD(x0,y0:word32) = wGCD(x1,y1)) /\ ~(x1 = 0w) /\ ~(y1 = 0w))` th  
  val th = APP_WEAKEN th `GCD_INV a b (x0,y0) (x1-y1,y1)`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_MOVE_COND,wGCD_SUB_LEFT,GCD_INV_def,WORD_EQ_SUB_ZERO,WORD_LOWER_NOT_EQ] \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = SIMP_RULE bool_ss [l2,pcADD_0,GSYM GCD_INV_def] (DISCH_ALL th)
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_FRAME `cond (y1 <+ (x1:word32))` th
  val th = SIMP_RULE (std_ss++sep2_ss) [] th
  val t2 = APP_WEAKEN th `SEP_EXISTS x. GCD_INV a b (x0,y0) x * cond (wMAXn x < wMAXn (x1:word32,y1:word32))`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ REPEAT STRIP_TAC
     \\ Q.EXISTS_TAC `(x1-y1,y1)` \\ ASM_REWRITE_TAC [] \\ MATCH_MP_TAC wMAXn_LESS     
     \\ FULL_SIMP_TAC bool_ss [GCD_INV_def,cond_STAR])

  (* case: a=b *)
  val th1 = (*  subs  a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1` ] arm_SUB2') 
  val th2 = (*  addls a,a,b  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`LS`,`s_flag`|->`F`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_ADD2') 
  val th3 = (*  subcc b,b,a  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`CC`,`s_flag`|->`F`,`a`|->`b`,`b`|->`a`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_SUB2') 
  val th4 = (*  bne -12  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(sw2sw (16777211w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`16777211w` ] arm_B2) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(x2 :word32)`|->`(x1 :word32) - (y1 :word32)`,`(y2 :word32)`|->`(y1 :word32)`,`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (FST_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (SND_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (y1 :word32))`,`(sZ :bool)`|->`(x1 :word32) = (y1 :word32)`,`(sC :bool)`|->`(y1 :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (y1 :word32)) /\ ~(word_msb x1 = word_msb (x1 - y1))` ] (SND_PROG2 th4))
  val th = g (AUTO_PRE_HIDE_STATUS (AUTO_POST1_HIDE_STATUS th))
  val lemma1 = prove(``(~(y1 <=+ x1) \/ (x1 = y1)) /\ y1 <=+ x1 /\ (x1 = y1) = (x1 = y1)``,METIS_TAC [GSYM WORD_NOT_LOWER,WORD_LOWER_OR_EQ])
  val th = RW [lemma1] th
  val th = UNDISCH (RW [ARM_PROG_MOVE_COND] th)
  val th = APP_FRAME `cond ((x1 = y1) /\ (wGCD(x0,y0) = wGCD(x1,y1:word32)) /\ ~(x1 = 0w) /\ ~(y1 = 0w))` th  
  val th = APP_WEAKEN1 th `R a (wGCD (x0,y0)) * R b (wGCD (x0,y0)) * ~S`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_MOVE_COND,SEP_IMP_REFL,GSYM AND_IMP_INTRO,wGCD_REFL,WORD_SUB_REFL,WORD_EQ_SUB_ZERO,WORD_LOWER_NOT_EQ])   
  val th = DISCH_ALL th
  val th = RW [ARM_PROG_MOVE_COND,AND_IMP_INTRO,CONJ_ASSOC] th
  val th = RW1 [GSYM ARM_PROG_MOVE_COND] (RW1 [GSYM AND_IMP_INTRO] (RW [GSYM CONJ_ASSOC] th))
  val th = RW [GSYM GCD_INV_def] th

  (* cases together *)
  val t12 = APP_MERGE t1 t2
  val th = APP_MERGE t12 (RW [GSYM ARM_PROG_MOVE_COND] th)
  val lemma = prove(``(x1 <+ y1 \/ y1 <+ x1) \/ (x1 = y1)``,METIS_TAC [WORD_LOWER_LOWER_CASES])
  val th = SIMP_RULE (bool_ss++sep_ss) [lemma] th 
  val th = PAIR_GEN "y" `(x1,y1)` th
  val th = MATCH_MP ARM_PROG_LOOP_MEASURE th
  val th = RW [GCD_INV_def] (Q.INST [`x0`|->`x`,`y0`|->`y`] (Q.SPEC `(x0,y0)` th))
  val th = RW [GSYM (REWRITE_CONV [SEP_cond_CLAUSES] ``cond x * cond y``),STAR_ASSOC] th  

  in th end;




fun parse_in_thm q th = Parse.parse_in_context (free_varsl (concl th::hyp th)) q;

val EXISTS_PRE_LEMMA = MATCH_MP EQ_IMP_IMP (SPEC_ALL ARM_PROG_EXISTS_PRE);
fun EXISTS_PRE var th =  
  let 
    val v = parse_in_thm var th 
    val th = PRE_CONV_RULE (UNBETA_CONV v) th
    val th = GEN v th
    val th = MATCH_MP EXISTS_PRE_LEMMA th   
    val th = PRE_CONV_RULE (RAND_CONV (ALPHA_CONV v)) th
    val th = BETA_RULE th
  in th end;


(*
  BTree = Node x BTree Btree | Leaf
  
  bt (a,Leaf) = cond (a = 0w)
  bt (a,Node x t1 t2) = cond ~(a = 0w) * 
    SEP_EXISTS a1 a2. M a x * M (a+1) (word32 a1) * M (a+2) (word32 a2) * bt(a1,t1) * bt(a2,t2)
 
  sumBTree Leaf = 0w
  sumBTree (Node x t1 t2) = x + sumBTree t1 + sumBTree t2

  naive:
  
  sum: CMP    a,#0           ; test: a = 0 
       MOVEQ  r15,r14        ; return, if a = 0 
       STR    a,[r13,#-4]    ; push a 
       STR    r14,[r13,#-4]  ; push link-register 
       LDR    b,[a],#+0      ; b := node value 
       ADD    s,s,b          ; s := s + b 
       LDR    a,[a],#+4      ; a := address of left 
       BL     sum            ; s := s + sumBTree a 
       LDR    a,[sp],#+4     ; a := original a 
       LDR    a,[a],#+8      ; a := address of right       
       BL     sum            ; s := s + sumBTree a 
       LDR    r15,[r13,#-8]  ; pop two and return

  tail-rec:

       <same as above>
       LDR    r14,[r13,#-8]! ; reset link-register and stack 
       B      sum            ; loop 

*)


val PROG_INST = HIDE_STATUS o HIDE_POST1 o FST_PROG2 o 
                SIMP_RULE (srw_ss()++sep_ss) [] o SET_SC `F` `AL`  

val _ = Hol_datatype `BTree = Leaf | Node of BTree # word32 # BTree`;

val sumBTree_def = Define `
  (sumBTree Leaf = 0w) /\
  (sumBTree (Node (t1,x,t2)) = sumBTree t1 + x + sumBTree t2)`;

val depth_def = Define `
  (depth Leaf = 0) /\
  (depth (Node (t1,x,t2)) = SUC (MAX (depth t1) (depth t2)))`;

val ldepth_def = Define `
  (ldepth Leaf = 0) /\
  (ldepth (Node (t1,x,t2)) = MAX (SUC (ldepth t1)) (ldepth t2))`;

val bt_def = Define `
  (bt (a,Leaf) = cond (a = 0w)) /\ 
  (bt (a,Node (t1,x,t2)) = cond ~(a = 0w) * 
     SEP_EXISTS a1 a2. M a x * M (a+1w) (addr32 a1) * M (a+2w) (addr32 a2) * 
                       bt(a1,t1) * bt(a2,t2))`;

val bt_Node = prove(
  ``bt (a,Node (t1,x,t2)) * P = 
    SEP_EXISTS a1 a2. M a x * M (a+1w) (addr32 a1) * M (a+2w) (addr32 a2) * 
                      bt(a1,t1) * bt(a2,t2) * cond ~(a = 0w) * P``,
  REWRITE_TAC [bt_def] \\ Cases_on `~(a = 0w)` \\ ASM_SIMP_TAC (std_ss++sep_ss) []
  \\ ONCE_REWRITE_TAC [STAR_def]
  \\ REWRITE_TAC [FUN_EQ_THM]		
  \\ SIMP_TAC std_ss [SEP_EXISTS_THM]
  \\ METIS_TAC []);

val n2w_lsl = prove(
  ``!m n. (n2w m):'a word << n = n2w (m * 2 ** n)``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [word_lsl_n2w]
  \\ Cases_on `dimindex (:'a) - 1 < n` \\ ASM_REWRITE_TAC []
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM n2w_mod]))
  \\ REWRITE_TAC [dimword_def]
  \\ `0 < dimindex (:'a)` by METIS_TAC [DIMINDEX_GT_0]
  \\ `dimindex (:'a) <= n` by DECIDE_TAC
  \\ `?k. n = dimindex (:'a) + k` by METIS_TAC [LESS_EQUAL_ADD]
  \\ ASM_REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ REWRITE_TAC [EXP_ADD,MULT_ASSOC]
  \\ `0 < 2**dimindex(:'a)` by METIS_TAC [ZERO_LT_EXP,EVAL ``0 < 2``]
  \\ ASM_SIMP_TAC bool_ss [MOD_EQ_0]);

val MULT_MOD_MULT = prove(
  ``!k m n. 0 < k /\ 0 < n ==> ((m MOD k) * n = (m*n) MOD (k*n))``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (UNDISCH (Q.SPECL [`m`,`k`] DA))
  \\ ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB,GSYM MULT_ASSOC]  
  \\ `0 < k * n` by ASM_SIMP_TAC bool_ss [LESS_MULT2]  
  \\ `r * n < k * n` by ASM_SIMP_TAC bool_ss [LT_MULT_RCANCEL]
  \\ ASM_SIMP_TAC bool_ss [MOD_MULT]);

val addr32_0 = prove(
  ``!x. (addr32 x = 0w) = (x = 0w)``,
  Cases_word \\ REWRITE_TAC [addr32_def] \\ CONV_TAC (SYM_CONV)
  \\ EQ_TAC \\ SIMP_TAC std_ss []
  THEN1 EVAL_TAC
  \\ ASM_SIMP_TAC std_ss [w2w_def,w2n_n2w]
  \\ REWRITE_TAC [n2w_lsl,EVAL ``2**2``]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``1073741824*4``)]
  \\ `0 < 4 /\ 0 < 1073741824` by DECIDE_TAC 
  \\ ASM_SIMP_TAC bool_ss [GSYM MULT_MOD_MULT]
  \\ DECIDE_TAC);

val ms_def = Define `
  (ms a [] = emp) /\
  (ms a (x::xs) = M a x * ms (a+1w) xs)`;

val blank_def = Define `
  (blank a 0 = emp) /\
  (blank a (SUC n) = ~ M a * blank (a-1w) n)`;

val STACK_def = Define `
  STACK a xs n = R30 13w a * ms a xs * blank (a-1w) n`;

val ARM_PROCS_def = Define `
  ARM_PROCS d P Q C = 
    !sp. ARM_PROC (P * STACK sp [] d * ~S) (Q * STACK sp [] d * ~S) C`;

val blank_ADD = prove(
  ``!x m n. blank x (m+n) = blank x m * blank (x-n2w m) n``,
  Induct_on `m` \\ SIMP_TAC std_ss [blank_def,emp_STAR,WORD_SUB_RZERO]
  \\ ASM_REWRITE_TAC [ADD,blank_def]
  \\ REWRITE_TAC [ADD1,GSYM word_add_n2w,GSYM WORD_SUB_PLUS,STAR_ASSOC]
  \\ METIS_TAC [WORD_ADD_COMM]);

val STACK_ADD = prove(
  ``STACK sp xs (m+n) = STACK sp xs m * blank (sp - 1w - n2w m) n``,
  REWRITE_TAC [STACK_def,blank_ADD,STAR_ASSOC]);

val STACK_EXTRACT = prove(
  ``STACK a xs n = ms a xs * STACK a [] n``,
  SIMP_TAC (bool_ss++sep_ss++star_ss) [ms_def,STACK_def]);

val STACK_PUSH = 
  let 
    val th = SET_AM2 `T` `F` `T` `1w` (PROG_INST arm_STR)  
    val th = PRE_MOVE_STAR `a*b*m*s` `(a*b*s)*m` th
    val th = HIDE_PRE th
    val th = RW [EVAL ``(w2w (1w:word8)):word30``] th  
    val th = Q.INST [`b`|->`13w`,`y`|->`sp`] th 
    val th = APP_FRAME `ms sp xs * blank (sp - 1w - 1w) n` th
    val tac = SIMP_TAC (bool_ss++star_ss) 
              [STACK_def,blank_def,SEP_IMP_REFL,ms_def,WORD_SUB_ADD]
    val th = APP_STRENGTHEN th `R a x * STACK sp xs (SUC n) * ~S` tac
    val th = APP_WEAKEN1 th `R a x * STACK (sp-1w) (x::xs) n * ~S` tac
  in th end;     

val STACK_EXPAND = prove(
  ``?X. STACK sp xs (MAX n m) = STACK sp xs n * X``,
  REWRITE_TAC [MAX_DEF] \\ Cases_on `~(n < m)` \\ FULL_SIMP_TAC std_ss []
  THEN1 (Q.EXISTS_TAC `emp` \\ SIMP_TAC (std_ss++sep_ss) [])
  \\ FULL_SIMP_TAC std_ss [LESS_EQ,LESS_EQ_EXISTS,ADD1,GSYM ADD_ASSOC]
  \\ REWRITE_TAC [STACK_ADD]
  \\ Q.EXISTS_TAC `blank (sp - 1w - n2w n) (1 + p)`
  \\ REWRITE_TAC []);

val ARM_PROG_EXPAND_STACK = prove(
  ``ARM_PROG (P * STACK sp xs n) cs C (Q * STACK sp xs n) {} ==> 
    !m. ARM_PROG (P * STACK sp xs (MAX n m)) cs C (Q * STACK sp xs (MAX n m)) {}``,
  REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o APP_BASIC_FRAME o SPEC_ALL)
  \\ STRIP_ASSUME_TAC STACK_EXPAND
  \\ ASM_SIMP_TAC (std_ss++sep_ss) []
  \\ MOVE_STAR_TAC `p*(sp*x)` `p*sp*x` 
  \\ ASM_REWRITE_TAC []);

val ARM_PROG_EXPAND_STACK2 = prove(
  ``ARM_PROG (P * STACK sp xs n) cs C SEP_F {(Q * STACK sp xs n,f)} ==> 
    !m. ARM_PROG (P * STACK sp xs (MAX n m)) cs C SEP_F {(Q * STACK sp xs (MAX n m),f)}``,
  REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o APP_BASIC_FRAME o SPEC_ALL)
  \\ STRIP_ASSUME_TAC STACK_EXPAND
  \\ ASM_SIMP_TAC (std_ss++sep_ss) []
  \\ MOVE_STAR_TAC `p*(sp*x)` `p*sp*x` 
  \\ ASM_REWRITE_TAC []);

val ARM_PROC_EXPAND_STACK = prove(
  ``ARM_PROC (P * STACK sp xs n) (Q * STACK sp xs n) C ==>
    !m. ARM_PROC (P * STACK sp xs (MAX n m)) (Q * STACK sp xs (MAX n m)) C``,
  REWRITE_TAC [ARM_PROC_THM] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o APP_BASIC_FRAME o SPEC_ALL)
  \\ STRIP_ASSUME_TAC STACK_EXPAND
  \\ ASM_SIMP_TAC (std_ss++sep_ss) []
  \\ MOVE_STAR_TAC `p*(sp*x)*q` `p*sp*q*x` 
  \\ ASM_REWRITE_TAC []);

val ARM_PROCS_EXPAND_STACK = prove(
  ``!m P Q C. ARM_PROCS m P Q C ==> !n. ARM_PROCS (MAX m n) P Q C``,
  REWRITE_TAC [ARM_PROCS_def]
  \\ MOVE_STAR_TAC `a*b*c` `a*c*b` \\ METIS_TAC [ARM_PROC_EXPAND_STACK]);

val blank_ADD1 = prove(
  ``!n a. blank a n * ~M (a - n2w n) = blank a (SUC n)``,
  Induct \\ REWRITE_TAC [blank_def,WORD_SUB_RZERO,emp_STAR]
  \\ REWRITE_TAC [ADD1,GSYM word_add_n2w]
  \\ ONCE_REWRITE_TAC [GSYM WORD_ADD_COMM]
  \\ ASM_REWRITE_TAC [WORD_SUB_PLUS,GSYM STAR_ASSOC,blank_def]);

val WORD_SUB_COMM = prove(
  ``!x v w. x - v - w = x - w - v``,
  REWRITE_TAC [GSYM WORD_SUB_PLUS,Once WORD_ADD_COMM]);
  
val blank_APPEND = prove(
  ``!n m a. blank a n * blank (a - n2w n) m = blank a (n + m)``,
  Induct \\ REWRITE_TAC [blank_def,emp_STAR,WORD_SUB_RZERO,EVAL ``0 + m:num``]
  \\ REWRITE_TAC [ADD,blank_def]
  \\ REWRITE_TAC [ADD1,GSYM word_add_n2w,WORD_SUB_PLUS]
  \\ ONCE_REWRITE_TAC [WORD_SUB_COMM]
  \\ ASM_REWRITE_TAC [GSYM STAR_ASSOC]);

val ms_IMP_blank = prove(
  ``!xs a. SEP_IMP (ms (a - wLENGTH xs) xs) (blank (a-1w) (LENGTH xs))``,
  Induct_on `xs`  
  \\ ASM_REWRITE_TAC [ms_def,wLENGTH_def,LENGTH]
  THEN1 REWRITE_TAC [SEP_IMP_REFL,blank_def]
  \\ REWRITE_TAC [GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_ADD,ADD1]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC SEP_IMP_TRANS
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ REWRITE_TAC [GSYM wLENGTH_def]
  \\ Q.EXISTS_TAC `blank (a-1w) (LENGTH xs) * M (a - wLENGTH xs - 1w) h`
  \\ STRIP_TAC THEN1 METIS_TAC [SEP_IMP_FRAME]
  \\ MATCH_MP_TAC SEP_IMP_TRANS
  \\ Q.EXISTS_TAC `blank (a-1w) (LENGTH xs) * ~ M (a - wLENGTH xs - 1w)`
  \\ REWRITE_TAC [SEP_HIDE_INTRO]
  \\ ONCE_REWRITE_TAC [WORD_SUB_COMM]
  \\ REWRITE_TAC [blank_ADD1,wLENGTH_def,GSYM ADD1,SEP_IMP_REFL]);

val MULTI_POP_LEMMA = prove(
  ``SEP_IMP (R30 13w sp * ms (sp - n2w (LENGTH (x::xs))) (x::xs) *
             blank (sp - n2w (LENGTH (x::xs)) - 1w) n)
            (STACK sp [] (n + LENGTH (x::xs)))``,
  REWRITE_TAC [STACK_def]
  \\ CONV_TAC (RAND_CONV (REWRITE_CONV [ms_def,emp_STAR]))
  \\ REWRITE_TAC [GSYM STAR_ASSOC]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ MATCH_MP_TAC ((DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL) SEP_IMP_FRAME)
  \\ MATCH_MP_TAC SEP_IMP_TRANS
  \\ Q.EXISTS_TAC `blank (sp - 1w) (LENGTH (x::xs)) * blank (sp - n2w (LENGTH (x::xs)) - 1w) n`
  \\ STRIP_TAC THEN1 METIS_TAC [wLENGTH_def,ms_IMP_blank,SEP_IMP_FRAME]
  \\ ONCE_REWRITE_TAC [WORD_SUB_COMM]  
  \\ REWRITE_TAC [blank_APPEND]
  \\ REWRITE_TAC [Once ADD_COMM,SEP_IMP_REFL]);

val MULTI_POP_STACK = let
  val ldr = PROG_INST (SET_AM2 `F` `T` `T` `n2w n` arm_LDR)
  val ldr = MOVE_STAR_RULE `a*b*y*s` `b*y*s*a` ldr
  val ldr = RW [ARM_PROG_HIDE_PRE] (Q.GEN `x` ldr)
  val ldr = MOVE_STAR_RULE `b*y*s*a` `a*b*y*s` ldr
  val ldr = Q.INST [`y`|->`sp-n2w n`,`b`|->`13w`,`z`|->`x`] ldr
  val lemma1 = prove(``!n. n < 256 ==> (w2w ((n2w n):word8) = (n2w n):word30)``,  
                     SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,w2n_n2w])
  val lemma2 = prove(``!n. n < 256 ==> (w2w ((n2w n):word8) = (n2w n):word12)``,  
                     SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,w2n_n2w])
  val ldr = SIMP_RULE std_ss [lemma1,lemma2,WORD_SUB_ADD] (DISCH ``n < 256`` ldr)
  val ldr = UNDISCH (Q.INST [`n`|->`LENGTH (x::xs)`] ldr)
  val ldr = APP_FRAME `ms (sp - n2w (LENGTH (x::xs)) + 1w) xs * 
                       blank (sp - n2w (LENGTH (x::xs)) - 1w) n` ldr
  val ldr = MOVE_STAR_RULE `a*sp*m*s*(mm*b)` `(sp*(m*mm)*b)*(a*s)` ldr
  val ldr = RW [GSYM ms_def,GSYM STACK_def] ldr
  val th = Q.SPEC `R a x * ~S` (MATCH_MP SEP_IMP_FRAME MULTI_POP_LEMMA) 
  val ldr = MATCH_MP ARM_PROG_WEAKEN_POST1 ldr 
  val ldr = MATCH_MP ldr th
  val ldr = RW [STACK_def] (RW1 [STAR_COMM] ldr)
  val ldr = APP_FRAME 
    `blank (sp - 1w - n2w (n + LENGTH (x::xs))) (m - (LENGTH ((x:word32)::xs) + n))` ldr
  val ldr = RW [GSYM STAR_ASSOC,blank_APPEND] ldr
  val lemma = prove( 
    ``blank (sp-n2w xxs-1w) n * blank (sp-1w-n2w(n + xxs)) m = blank (sp-n2w xxs-1w) (n+m)``,
    REWRITE_TAC [GSYM word_add_n2w,WORD_SUB_PLUS,GSYM blank_APPEND]    
    \\ METIS_TAC [WORD_SUB_COMM])
  val ldr = RW1 [lemma] ldr
  val ldr = MOVE_STAR_RULE `a*s*sp*mm*b` `a*(sp*mm*b)*s` (RW [STAR_ASSOC] ldr)
  val ldr = RW [GSYM STACK_def] ldr
  val lemma = prove(``n + xs + (m - (xs + n)) = MAX (n + xs) m``,SRW_TAC [] [MAX_DEF] \\ DECIDE_TAC)
  val ldr = RW [lemma] ldr
  val lemma = prove(``n + (m - (xs + n)) = MAX n (m - xs)``,SRW_TAC [] [MAX_DEF] \\ DECIDE_TAC)
  val ldr = RW [lemma] ldr
in (Q.GEN `x` o Q.GEN `xs` o Q.GEN `a` o Q.GEN `n` o Q.GEN `m` o DISCH_ALL) ldr end;



val SUM_BTREE_SPEC'_def = Define 
  `SUM_BTREE_SPEC' e a s d C' tree =
      !ax sum. ARM_PROCS d
        (R30 a ax * bt (ax,tree) * R s sum * e) 
        (~ R a * bt (ax,tree) * R s (sum + sumBTree tree)) C'`;

val SUM_BTREE_SPEC_def = Define 
  `SUM_BTREE_SPEC e a s C' tree = SUM_BTREE_SPEC' e a s (2 * depth tree) C' tree`;

val SUM_BTREE_SPEC_TR_def = Define 
  `SUM_BTREE_SPEC_TR e a s C' tree = SUM_BTREE_SPEC' e a s (2 * ldepth tree) C' tree`;

val SUM_BTREE_SPEC_THM =
  SIMP_CONV (bool_ss++sep_ss) [SUM_BTREE_SPEC_def,SUM_BTREE_SPEC'_def] 
    ``SUM_BTREE_SPEC emp a s C' tree``;

val SUM_BTREE_SPEC_TR_THM =
  SIMP_CONV (bool_ss++sep_ss) [SUM_BTREE_SPEC_TR_def,SUM_BTREE_SPEC'_def] 
    ``SUM_BTREE_SPEC_TR emp a s C' tree``;

val A1_TAC = 
  STRIP_TAC \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `t1`) \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF]
  \\ Cases_on `depth t1 < depth t2`
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF]
  \\ `depth t1 < SUC (depth t2)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF];

val A2_TAC = 
  STRIP_TAC \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `t2`) \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF]
  \\ Cases_on `depth t1 < depth t2`
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF]
  \\ `depth t2 < SUC (depth t1)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF];
    
val ASSUMPTION1 = (UNDISCH o UNDISCH o Q.INST [`e`|->`emp`] o prove) (
  ``(!t'. depth t' < depth tree ==> SUM_BTREE_SPEC e a s C' t') ==>
    (tree = Node(t1,y,t2)) ==> SUM_BTREE_SPEC e a s C' t1``,A1_TAC);

val ASSUMPTION1_TR = (UNDISCH o UNDISCH o Q.INST [`e`|->`emp`] o prove) (
  ``(!t'. depth t' < depth tree ==> SUM_BTREE_SPEC_TR e a s C' t') ==>
    (tree = Node(t1,y,t2)) ==> SUM_BTREE_SPEC_TR e a s C' t1``,A1_TAC);

val ASSUMPTION2 = (UNDISCH o UNDISCH o Q.INST [`e`|->`emp`] o prove) (
  ``(!t'. depth t' < depth tree ==> SUM_BTREE_SPEC e a s C' t') ==>
    (tree = Node(t1,y,t2)) ==> SUM_BTREE_SPEC e a s C' t2``,A2_TAC);

val ASSUMPTION2_TR = (UNDISCH o UNDISCH o Q.INST [`e`|->`emp`] o prove) (
  ``(!t'. depth t' < depth tree ==> SUM_BTREE_SPEC_TR e a s C' t') ==>
    (tree = Node(t1,y,t2)) ==> SUM_BTREE_SPEC_TR e a s C' t2``,A2_TAC);

val MULT_MAX = prove(
  ``k * MAX m n = MAX (k * m) (k * n)``,
  Cases_on `k` \\ SIMP_TAC std_ss [MAX_DEF] \\ Cases_on `m < n` \\ ASM_REWRITE_TAC []);


(*
"cmp a,#0"
"moveq r15,r14"
"str a,[r13,#-4]!"
"str r14,[r13,#-4]!"
"ldr r14,[a]"
"add s,s,r14"
"ldr a,[a,#4]"
"bl sum"
"ldr a,[r13,#4]"
"ldr a,[a,#8]"
"bl sum"
"ldr r15,[r13],#8"
*)

(*
"cmp a,#0"
"moveq r15,r14"
"str a,[r13,#-4]!"
"str r14,[r13,#-4]!"
"ldr r14,[a]"
"add s,s,r14"
"ldr a,[a,#4]"
"bl sum"
"ldr a,[r13,#4]"
"ldr a,[a,#8]"
"ldr r14,[r13],#8"
"b sum"
*)


val case1 = let
  (* compose_progs' [("cmp a,#0",true),("moveq r15,r14",true)] "th" "  " *)
  val th1 = (*  cmp a,#0  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_CMP1) 
  val th2 = (*  moveq r15,r14  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`EQ`,`a`|->`14w`,`a_mode`|->`OneReg`,`x`|->`x2` ] arm_MOV_PC_GENERAL) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(sC :bool)`|->`(0w :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (0w :word32)) /\ ~(word_msb x1 = word_msb (x1 - (0w :word32)))` ] (FST_PROG2 th2))
  val th = SIMP_RULE (bool_ss++sep_ss) [] (ALIGN_VARS ["x2"] th)
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  in th end;

val case2 = let
  (* compose_progs' [("cmp a,#0",true),("moveq r15,r14",false),("str a,[r13,#-4]!",true),("str r14,[r13,#-4]!",true),("ldr r14,[a]",true),("add s,s,r14",true),("ldr a,[a,#4]",true)] "th" "  " *)
  val th1 = (*  cmp a,#0  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_CMP1) 
  val th2 = (*  moveq r15,r14  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`EQ`,`a`|->`14w`,`a_mode`|->`OneReg`,`x`|->`x2` ] arm_MOV_PC_GENERAL) 
  val th3 = (*  str a,[r13,#-4]!  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := F; Wb := T|>`,`b`|->`13w`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_STR_NONALIGNED) 
  val th4 = (*  str r14,[r13,#-4]!  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := F; Wb := T|>`,`a`|->`14w`,`b`|->`13w`,`imm`|->`4w`,`x`|->`x4`,`y`|->`y4`,`z`|->`z4` ] arm_STR_NONALIGNED) 
  val th5 = (*  ldr r14,[a]  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`14w`,`b`|->`a`,`imm`|->`0w`,`x`|->`x5`,`y`|->`y5`,`z`|->`z5` ] arm_LDR_NONALIGNED) 
  val th6 = (*  add s,s,r14  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`s`,`b`|->`14w`,`a_mode`|->`OneReg`,`x`|->`x6`,`y`|->`y6` ] arm_ADD2') 
  val th7 = (*  ldr a,[a,#4]  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`b`|->`a`,`imm`|->`4w`,`y`|->`y7`,`z`|->`z7` ] arm_LDR1_NONALIGNED) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(sC :bool)`|->`(0w :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (0w :word32)) /\ ~(word_msb x1 = word_msb (x1 - (0w :word32)))` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(sC :bool)`|->`(0w :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (0w :word32)) /\ ~(word_msb x1 = word_msb (x1 - (0w :word32)))`,`(x3 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(y4 :word32)`|->`(y3 :word32) - (4w :word32)`,`(sN :bool)`|->`word_msb ((x1 :word32) - (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(sC :bool)`|->`(0w :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (0w :word32)) /\ ~(word_msb x1 = word_msb (x1 - (0w :word32)))` ] (FST_PROG2 th4))
  val th = FRAME_COMPOSE th (Q.INST [`(x5 :word32)`|->`(x4 :word32)`,`(sN :bool)`|->`word_msb ((x1 :word32) - (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(sC :bool)`|->`(0w :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (0w :word32)) /\ ~(word_msb x1 = word_msb (x1 - (0w :word32)))`,`(y5 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th5))
  val th = FRAME_COMPOSE th (Q.INST [`(y6 :word32)`|->`(z5 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (0w :word32)) :word2))`,`(sN :bool)`|->`word_msb ((x1 :word32) - (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(sC :bool)`|->`(0w :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (0w :word32)) /\ ~(word_msb x1 = word_msb (x1 - (0w :word32)))` ] (FST_PROG2 th6))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) - (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(sC :bool)`|->`(0w :word32) <=+ (x1 :word32)`,`(sV :bool)`|->`~(word_msb (x1 :word32) = word_msb (0w :word32)) /\ ~(word_msb x1 = word_msb (x1 - (0w :word32)))`,`(y7 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th7))
  val th = SIMP_RULE (srw_ss()++sep_ss) [] (ALIGN_VARS ["y3","x1","z7"] th)
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST1_HIDE_STATUS th)
  val th = SIMP_RULE (std_ss++sep2_ss) [GSYM WORD_SUB_PLUS,word_add_n2w,GSYM M30_def] th
  in th end;

val case3 = let
  (* compose_progs' [("ldr a,[r13,#4]",true),("ldr a,[a,#8]",true)] "th" "  " *)
  val th1 = (*  ldr a,[r13,#4]  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`b`|->`13w`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED) 
  val th2 = (*  ldr a,[a,#8]  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (8w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`b`|->`a`,`imm`|->`8w`,`y`|->`y2`,`z`|->`z2` ] arm_LDR1_NONALIGNED) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(y2 :word32)`|->`(z1 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((y1 :word32) + (4w :word32)) :word2))` ] (FST_PROG2 th2))
  val th = SIMP_RULE (srw_ss()++sep_ss) [] (ALIGN_VARS ["y1","z1"] th)
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST1_HIDE_STATUS th)
  val th = SIMP_RULE (std_ss++sep2_ss) [GSYM M30_def] th
  in th end;

val case4 = let
  val th = (*  ldr r15,[r13],#8  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (8w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`13w`,`imm`|->`2w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_PC) 
  val th = SIMP_RULE (srw_ss() ++ armINST_ss) [ADDR_MODE2_WB_def,ADDR_MODE2_ADDR_def,GSYM M30_def] th
  val th = RW [EVAL ``(w2w (2w:word8) << 2):word12``,EVAL ``(w2w (2w:word8)):word30``] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS (FST_PROG2 th))
  in th end;

val case234 = let
  val g = MATCH_MP ARM_PROG_EXPAND_STACK o
          MOVE_STAR_RULE `a*b*sum*st*s*lr` `a*b*sum*s*lr*st` o
          MATCH_MP arm_BL o SPEC_ALL o 
          RW [SUM_BTREE_SPEC_def,SUM_BTREE_SPEC'_def,ARM_PROCS_def,emp_STAR]
  val h = RW [GSYM MULT_MAX,STACK_def,ms_def,emp_STAR]
  val th1 = h (Q.SPEC `2 * depth t2` (g ASSUMPTION1))
  val th2 = h (Q.SPEC `2 * depth t1` (g ASSUMPTION2))
  val th = Q.INST [`x1`|->`ax`,`y3`|->`sp`,`x4`|->`lr`,`z5`|->`v`,`x6`|->`sum`] case2
  val th = HIDE_POST1 (POST1_MOVE_STAR `a*x1*ss*lr*x11*sp*y3*y31*s` `a*x1*ss*x11*sp*y3*y31*s*lr` th)
  val th' = Q.INST [`ax`|->`z7`,`sum`|->`sum+v`,`sp`|->`sp-2w`] th1
  val th = FRAME_COMPOSE th th'
  val th' = HIDE_PRE (PRE_MOVE_STAR `a*sp*y1*z1*s` `sp*y1*z1*s*a` case3)
  val th' = Q.INST [`y1`|->`sp - 2w`,`z1`|->`ax`] th'
  val lemma = prove(``x - 2w + 1w = x:word30 - 1w``,EVAL_TAC \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w])  
  val th = FRAME_COMPOSE th (RW [lemma] th')
  val th' = Q.INST [`ax`|->`z2`,`sum`|->`sum + v + sumBTree t1`,`sp`|->`sp-2w`,`offset`|->`offset2`] th2
  val th = RW [lemma,GSYM M30_def] (ALIGN_VARS ["z2"] th)
  val th' = RW1 [MAX_COMM,lemma] th'
  val th = FRAME_COMPOSE th th'
  val th = RW [GSYM M30_def] (ALIGN_VARS ["lr"] th)
  val th = FRAME_COMPOSE th (Q.INST [`x1`|->`sp-2w`,`y1`|->`lr`] case4)
  val th = APP_FRAME `cond ((tree = Node (t1,y,t2)) /\ ~(ax:word30 = 0w))` th
  val th = RW [WORD_SUB_ADD,ms_def,emp_STAR] (Q.INST [`v`|->`y`] th)
  val th = Q.INST [`offset`|->`0w-9w`,`offset2`|->`0w-12w`] th
  val th = RW [EVAL ``(7w + (sw2sw (0w - 9w:word24) + 2w)):word30``] th
  val th = RW [EVAL ``(10w + (sw2sw (0w - 12w:word24) + 2w)):word30``] th
  val th = RW [UNION_IDEMPOT,setADD_0,EVAL ``0w - 9w:word24``,EVAL ``0w - 12w:word24``] th
  in th end;
  
val case234' = let
  val th = RW [M30_def] case234
  val th = AUTO_HIDE_POST [`M (sp - 2w)`,`M (sp - 1w)`] th
  val th = APP_WEAKEN th 
             `~R a * bt (ax,tree) * R s (sum + sumBTree tree) * 
              R30 13w sp *  blank (sp-1w) (2 * depth tree) * ~R 14w * ~S`
  (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,sumBTree_def,depth_def,WORD_ADD_ASSOC,bt_def]
   \\ REWRITE_TAC [DECIDE ``2 * SUC n = SUC (SUC (2*n))``,blank_def,STAR_ASSOC] 
   \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w] 
   \\ SIMP_TAC (bool_ss++sep2_ss) []
   \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,M30_def] \\ REPEAT STRIP_TAC
   \\ Q.EXISTS_TAC `z7` \\ Q.EXISTS_TAC `z2`
   \\ ONCE_REWRITE_TAC [prove(``s+t1+y+t2=s+y+t1+t2``,METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM])]
   \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = HIDE_PRE (PRE_MOVE_STAR `a*sp*sp1*lr*sp2*ax*s*ax1*ss*cc*b1*b2*ax2*b3*c` `a*sp*lr*sp2*ax*s*ax1*ss*cc*b1*b2*ax2*b3*c*sp1` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a*sp*lr*sp2*ax*s*ax1*ss*cc*b1*b2*ax2*b3*c*sp1` `a*sp*lr*ax*s*ax1*ss*cc*b1*b2*ax2*b3*c*sp1*sp2` th)
  val th = SIMP_RULE (bool_ss++sep2_ss) [addr32_EQ_0] th
  val th = EXISTS_PRE `z2` th
  val th = EXISTS_PRE `z7` th
  val th = APP_STRENGTHEN th 
             `R30 a ax * bt (ax,tree) * R s sum * 
              R30 13w sp *  blank (sp-1w) (2 * depth tree) * R30 14w lr * ~S *
              cond (tree = Node(t1,y,t2))`
  (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,sumBTree_def,depth_def,WORD_ADD_ASSOC,bt_def]
   \\ REWRITE_TAC [DECIDE ``2 * SUC n = SUC (SUC (2*n))``,blank_def,STAR_ASSOC] 
   \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w] 
   \\ SIMP_TAC (bool_ss++sep2_ss) []
   \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,M30_def] \\ REPEAT STRIP_TAC
   \\ Q.EXISTS_TAC `y'` \\ Q.EXISTS_TAC `y''`
   \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = PAT_DISCH ``tree = Node (t1,y,t2)`` th
  val th = RW [GSYM ARM_PROG_MOVE_COND] (RW [ARM_PROG_MOVE_COND,AND_IMP_INTRO] th)
  in th end;

val (case1',case1_tr') = let
  val th = RW [addr32_EQ_0] (ALIGN_VARS ["x1"] case1)
  val th = Q.INST [`x1`|->`ax`,`x2`|->`lr`] th
  val th = APP_FRAME `cond (ax:word30 = 0w)` th
  val th = RW [GSYM bt_def] (SIMP_RULE (bool_ss++sep2_ss) [] th)
  val th = SIMP_RULE bool_ss [] (DISCH ``Leaf = tree`` th)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) SYM_CONV) th
  val th = RW [R30_def] (UNDISCH th)
  val th = HIDE_POST (POST_MOVE_STAR `lr*a*s*b` `lr*s*b*a` th)
  val th = RW [GSYM R30_def] (POST_MOVE_STAR `lr*s*b*a` `a*lr*s*b` th)
  val th = APP_FRAME `R s (sum + sumBTree tree) * R30 13w sp * blank (sp - 1w) (2 * g tree)` th
  val th = MOVE_STAR_RULE `a*lr*s*b*(sum*sp*bl)` `a*b*sum*sp*bl*lr*s` th
  val th = RW [GSYM ARM_PROG_MOVE_COND] (DISCH_ALL th)
  val th = APP_STRENGTHEN th 
             `R30 a ax * bt (ax,tree) * R s sum * 
              R30 13w sp *  blank (sp-1w) (2 * g tree) * R30 14w lr * ~S *
              cond (tree = Leaf)`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_MOVE_COND,sumBTree_def,WORD_ADD_0,SEP_IMP_REFL])
  in (Q.INST [`g`|->`depth`] th, Q.INST [`g`|->`ldepth`] th) end;

val case1234' = let 
  val th = RW [ARM_PROG_MOVE_COND] (APP_MERGE case1' case234')
  val lemma = prove(
    ``(!t1 y t2. (tree = Leaf) \/ (tree = Node (t1,y,t2)) ==> P) ==> P``,
    Cases_on `tree` \\ REWRITE_TAC [] \\ Cases_on `p` \\ Cases_on `r` \\ SRW_TAC [] [])
  val th = (Q.GEN `t1` o Q.GEN `y` o Q.GEN `t2`) th
  val th = MATCH_MP lemma th
  in th end;

val ARM_SUM_BTREE_PROCEDURE = let
  val th = Q.INST [`lr`|->`q`] case1234'
  val th = MOVE_STAR_RULE `p*q*r` `p*r*q` th
  val th = (Q.GEN `ax` o Q.GEN `sum` o Q.GEN `sp` o Q.GEN `q`) th
  val th1 = RW [STACK_def,ms_def,emp_STAR,ARM_PROC_THM,STAR_ASSOC] ARM_PROCS_def
  val th = RW [GSYM th1] (RW1 [ARM_PROG_EXTRACT_CODE] th)
  val th2 = RW [emp_STAR] (Q.SPEC `emp` SUM_BTREE_SPEC'_def)
  val th = RW [GSYM th2,GSYM SUM_BTREE_SPEC_def] th
  val th = RW1 [INSERT_SING_UNION] th
  val th = MATCH_MP ARM_PROC_RECURSION ((Q.GEN `tree` o Q.GEN `C'` o DISCH_ALL) th)
  val th = Q.SPEC `tree` th
  in RW [SUM_BTREE_SPEC_def,SUM_BTREE_SPEC'_def,emp_STAR] th end;

(* tail rec version *)

val case5 = let
  (* compose_progs ["ldr r14,[r13],#8","b -44"] "th" "  " *)
  val th1 = (*  ldr r14,[r13],#8  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (8w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`14w`,`b`|->`13w`,`imm`|->`8w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED) 
  val th2 = (*  b -44  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(sw2sw (16777203w :word24) :word30)``] (Q.INST [`c_flag`|->`AL`,`offset`|->`16777203w` ] arm_B2) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [ ] (FST_PROG2 th2))
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  val th = RW [GSYM M30_def] (ALIGN_VARS ["y1","z1"] th)
  in th end;

val ARM_PROG_COMPOSE_0 = prove(
  ``ARM_PROG P cs C SEP_F {(Q,I)} ==> ARM_PROG Q [] C' SEP_F Z ==> 
    ARM_PROG P cs (C UNION C') SEP_F Z``,
  REWRITE_TAC [ARM_PROG_THM,pcINC_0,ARM_GPROG_FALSE_POST,ARM_GPROG_EMPTY_CODE] \\ REPEAT STRIP_TAC
  \\ `ARM_GPROG {(P,I)} ((cs,I) INSERT C) ({} UNION {(Q,I)})` by ASM_REWRITE_TAC [UNION_EMPTY]
  \\ `ARM_GPROG ({(Q,I)} UNION {}) C' Z` by ASM_REWRITE_TAC [UNION_EMPTY]
  \\ IMP_RES_TAC ARM_GPROG_COMPOSE \\ FULL_SIMP_TAC bool_ss [UNION_EMPTY,INSERT_UNION_EQ]);
  
val case234_tr = let
  val g = RW [GSYM MULT_MAX,STACK_def,ms_def,emp_STAR] o
          MOVE_STAR_RULE `a*b*sum*st*s*lr` `a*b*sum*s*lr*st` o
          MATCH_MP arm_BL o SPEC_ALL
  val h = RW [SUM_BTREE_SPEC_TR_def,SUM_BTREE_SPEC'_def,ARM_PROCS_def,emp_STAR]
  val th1 = (g o h) ASSUMPTION1_TR
  val th2 = h ASSUMPTION2_TR
  val th = Q.INST [`x1`|->`ax`,`y3`|->`sp`,`x4`|->`lr`,`z5`|->`v`,`x6`|->`sum`] case2
  val th = HIDE_POST1 (POST1_MOVE_STAR `a*x1*ss*lr*x11*sp*y3*y31*s` `a*x1*ss*x11*sp*y3*y31*s*lr` th)
  val th' = Q.INST [`ax`|->`z7`,`sum`|->`sum+v`,`sp`|->`sp-2w`] th1
  val th = FRAME_COMPOSE th th'
  val th' = HIDE_PRE (PRE_MOVE_STAR `a*sp*y1*z1*s` `sp*y1*z1*s*a` case3)
  val th' = Q.INST [`y1`|->`sp - 2w`,`z1`|->`ax`] th'
  val lemma = prove(``x - 2w + 1w = x:word30 - 1w``,EVAL_TAC \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w])  
  val th = FRAME_COMPOSE th (RW [lemma] th')
  val th = Q.INST [`offset`|->`0w-9w`] th
  val th = RW [EVAL ``(7w + (sw2sw (0w - 9w:word24) + 2w)):word30``] th
  val th = RW [UNION_IDEMPOT,setADD_0,EVAL ``0w - 9w:word24``,addr32_EQ_0] th
  val th = RW [GSYM M30_def] (ALIGN_VARS ["lr"] th)
  val th' = Q.INST [`y1`|->`sp-2w`,`z1`|->`lr`] case5  
  val th' = HIDE_PRE (PRE_MOVE_STAR `lr*sp*sp2*s` `sp*sp2*s*lr` th')
  val th = FRAME_COMPOSE th th'
  val l2 = prove(``1073741824w = 0w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val th = RW [l2,pcADD_0,WORD_SUB_ADD,M30_def] (ALIGN_VARS ["z2"] th)
  val th = HIDE_POST (POST_MOVE_STAR `lr*sp*sp2*s*a*ax2*sp1*b*sum*bl*ax1*ax` `lr*sp*s*a*ax2*sp1*b*sum*bl*ax1*ax*sp2` th)
  val th = HIDE_POST (POST_MOVE_STAR `lr*sp*s*a*ax2*sp1*b*sum*bl*ax1*ax*sp2` `lr*sp*s*a*ax2*b*sum*bl*ax1*ax*sp2*sp1` th)
  val th = POST_MOVE_STAR `lr*sp*s*a*ax2*b*sum*bl*ax1*ax*sp2*sp1` `lr*s*a*ax2*b*sum*ax1*ax*(sp*(sp1*sp2*bl))` th
  val th = HIDE_PRE (PRE_MOVE_STAR `a*sp*sp1*lr*sp2*ax*sum*ax1*s*cc*b*bl*ax2` `a*sp*lr*sp2*ax*sum*ax1*s*cc*b*bl*ax2*sp1` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a*sp*lr*sp2*ax*sum*ax1*s*cc*b*bl*ax2*sp1` `a*sp*lr*ax*sum*ax1*s*cc*b*bl*ax2*sp1*sp2` th)
  val th = PRE_MOVE_STAR `a*sp*lr*ax*sum*ax1*s*cc*b*bl*ax2*sp1*sp2` `a*lr*ax*sum*ax1*s*cc*b*ax2*(sp*(sp1*sp2*bl))` th
  val lemma = prove(``~M (sp-1w) * ~M (sp-2w) * blank (sp-2w-1w) n = blank (sp-1w) (SUC (SUC n))``,
                    SIMP_TAC std_ss [blank_def,GSYM WORD_SUB_PLUS,word_add_n2w,STAR_ASSOC])
  val th = RW [lemma,GSYM M30_def,GSYM (REWRITE_CONV [STACK_def,ms_def,emp_STAR] ``STACK sp [] n``)] th
  val th = Q.SPEC `2 * ldepth t2` (MATCH_MP ARM_PROG_EXPAND_STACK2 th)
  val lemma = prove(
  ``MAX (SUC (SUC (2 * n))) (2 * m) = 2 * MAX (SUC n) m``,
  SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC,MULT_MAX,
    GSYM ((SIMP_CONV std_ss [MULT_CLAUSES] THENC ONCE_REWRITE_CONV [ADD_COMM]) ``2 * (SUC n)``)])
  val th = RW [lemma] th
  val th' = MOVE_STAR_RULE `a*sum*sp*s*lr` `a*sum*s*lr*sp` (SPEC_ALL (RW [ARM_PROC_THM] th2))
  val th' = Q.SPEC `2 * (SUC (ldepth t1))` (MATCH_MP ARM_PROG_EXPAND_STACK2 th')
  val th' = RW [GSYM MULT_MAX] (RW1 [MAX_COMM] th')
  val th' = Q.INST [`ax`|->`z2`,`q`|->`lr`,`sum`|->`sum + v + sumBTree t1`,`z2`|->`z9`] th'
  val th' = APP_FRAME `M30 (ax + 2w) z2 * M30 (ax + 1w) z7 * bt (z7,t1) * M ax v` th'
  val th = APP_FRAME `bt (z2,t2)` th
  val th = RW [STAR_ASSOC] (SIMP_RULE (bool_ss++star_ss) [] th)  
  val th' = RW [STAR_ASSOC] (SIMP_RULE (bool_ss++star_ss) [] th')  
  val th = RW [UNION_IDEMPOT] (MATCH_MP (MATCH_MP ARM_PROG_COMPOSE_0 th) th')
  val th = APP_FRAME `cond ((tree = Node (t1,y,t2)) /\ ~(ax:word30 = 0w))` th
  in Q.INST [`v`|->`y`] th end;  

val case234_tr' = let
  val th = RW [M30_def] case234_tr
  val th = APP_WEAKEN th 
             `~R a * bt (ax,tree) * R s (sum + sumBTree tree) * 
              STACK sp [] (2 * ldepth tree) * ~R 14w * ~S`
  (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,sumBTree_def,ldepth_def,WORD_ADD_ASSOC,bt_def]
   \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,M30_def] \\ REPEAT STRIP_TAC
   \\ Q.EXISTS_TAC `z7` \\ Q.EXISTS_TAC `z2`
   \\ ONCE_REWRITE_TAC [prove(``s+t1+y+t2=s+y+t1+t2``,METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM])]
   \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = EXISTS_PRE `z2` th
  val th = EXISTS_PRE `z7` th
  val th = APP_STRENGTHEN th 
             `R30 a ax * bt (ax,tree) * R s sum * 
              STACK sp [] (2 * ldepth tree) * R30 14w lr * ~S *
              cond (tree = Node(t1,y,t2))`
  (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,sumBTree_def,ldepth_def,WORD_ADD_ASSOC,bt_def]
   \\ SIMP_TAC (bool_ss++sep2_ss) []
   \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,M30_def] \\ REPEAT STRIP_TAC
   \\ Q.EXISTS_TAC `y'` \\ Q.EXISTS_TAC `y''` \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
  val th = PAT_DISCH ``tree = Node (t1,y,t2)`` th
  val th = RW [GSYM ARM_PROG_MOVE_COND] (RW [ARM_PROG_MOVE_COND,AND_IMP_INTRO] th)
  in th end;
  
val case1234_tr' = let 
  val th = PRE_MOVE_STAR `a*b*sum*sp*bl*lr*s*cc` `a*b*sum*(sp*bl)*lr*s*cc` case1_tr'
  val th = POST_MOVE_STAR `a*b*sum*sp*bl*lr*s` `a*b*sum*(sp*bl)*lr*s` th
  val th = RW [GSYM (REWRITE_CONV [STACK_def,ms_def,emp_STAR] ``STACK sp [] n``)] th
  val th = RW [ARM_PROG_MOVE_COND] (APP_MERGE th case234_tr')
  val lemma = prove(
    ``(!t1 y t2. (tree = Leaf) \/ (tree = Node (t1,y,t2)) ==> P) ==> P``,
    Cases_on `tree` \\ REWRITE_TAC [] \\ Cases_on `p` \\ Cases_on `r` \\ SRW_TAC [] [])
  val th = (Q.GEN `t1` o Q.GEN `y` o Q.GEN `t2`) th
  val th = MATCH_MP lemma th
  in th end;

val ARM_SUM_BTREE_PROCEDURE_TR = let
  val th = Q.INST [`lr`|->`q`] case1234_tr'
  val th = MOVE_STAR_RULE `p*q*r` `p*r*q` th
  val th = (Q.GEN `ax` o Q.GEN `sum` o Q.GEN `sp` o Q.GEN `q`) th
  val th1 = RW [ARM_PROC_THM,STAR_ASSOC] ARM_PROCS_def
  val th = RW [GSYM th1] (RW1 [ARM_PROG_EXTRACT_CODE] th)
  val th2 = RW [emp_STAR] (Q.SPEC `emp` SUM_BTREE_SPEC'_def)
  val th = RW [GSYM th2,GSYM SUM_BTREE_SPEC_TR_def] th
  val th = RW1 [INSERT_SING_UNION] th
  val th = MATCH_MP ARM_PROC_RECURSION ((Q.GEN `tree` o Q.GEN `C'` o DISCH_ALL) th)
  val th = Q.SPEC `tree` th
  in RW [SUM_BTREE_SPEC_TR_def,SUM_BTREE_SPEC'_def,emp_STAR] th end;


(* export ready examples *)

val _ = save_thm("ARM_FAC_PROGRAM",ARM_FAC_PROGRAM);
val _ = save_thm("ARM_GCD_PROGRAM",ARM_GCD_PROGRAM);
val _ = save_thm("ARM_GCD_PROGRAM_FIXED",ARM_GCD_PROGRAM_FIXED);
val _ = save_thm("ARM_GCD_PROGRAM_BETTER",ARM_GCD_PROGRAM_BETTER);
val _ = save_thm("ARM_SUM_BTREE_PROCEDURE",ARM_SUM_BTREE_PROCEDURE);
val _ = save_thm("ARM_SUM_BTREE_PROCEDURE_TR",ARM_SUM_BTREE_PROCEDURE_TR);


(* ----------------------------------------------------------------------------- *)
(* Instantiation of STM and LDM instructions                                     *)
(* ----------------------------------------------------------------------------- *)

val th = SET_AM `am4_FA F` arm_STM
val th = Q.INST [`xs`|->`[(b1,y1);(b2,y2);(b3,y3)]`] th
val th = REWRITE_RULE  [blank_ms_def,LENGTH,ADDR_MODE4_ADDR_def,ADDR_MODE4_ADDR'_def,
              ADDR_MODE4_WB'_def,ADDR_MODE4_UP_def,MAP,ADDR_MODE4_WB_def,
              ADDR_MODE4_wb_def,xR_list_def,STAR_ASSOC] th
val th = REWRITE_RULE [ADD1,GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_ADD] th
val th = SIMP_RULE arith_ss [GSYM WORD_SUB_PLUS,word_add_n2w,WORD_SUB_RZERO] th
val th = SIMP_RULE (std_ss++sep_ss) [MAP,xR_list_def,STAR_ASSOC,ADDR_MODE4_CMD_def,GSYM WORD_ADD_ASSOC,word_add_n2w] th

val th = Q.INST [`b1`|->`0w`,`b2`|->`1w`,`b3`|->`2w`] th
val th = RW [EVAL ``reg_values [(0w:word4,y1); (1w,y2); (2w,y3)]``,ms_def,STAR_ASSOC,emp_STAR] th



val _ = export_theory();

