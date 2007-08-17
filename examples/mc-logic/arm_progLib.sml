structure arm_progLib :> arm_progLib =
struct

(*
  quietdec := true;
  val armDir = concat Globals.HOLDIR "/examples/ARM/v4";
  val yaccDir = concat Globals.HOLDIR "/tools/mlyacc/mlyacclib";
  loadPath := !loadPath @ [armDir,yaccDir];
*)
 
open HolKernel boolLib bossLib;
open listTheory wordsTheory pred_setTheory arithmeticTheory pairTheory wordsLib;
open set_sepTheory progTheory arm_progTheory arm_instTheory set_sepLib;
open instructionSyntax;
 
(*
  quietdec := false;
*)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val EQ_IMP_IMP = METIS_PROVE [] ``(x=y) ==> x ==> y``;

(* ============================================================================= *)
(* STABLE CORE FUNCTIONS                                                         *)
(* ============================================================================= *)

(* -- syntax -- *)

fun dest_ARM_PROG tm = let
  val (p,Z) = dest_comb tm
  val (p,Q) = dest_comb p
  val (p,C) = dest_comb p
  val (p,c) = dest_comb p
  val (p,P) = dest_comb p
  in (P,c,C,Q,Z) end;

fun pre_ARM_PROG tm       = let val (t,_,_,_,_) = dest_ARM_PROG tm in t end;
fun code_ARM_PROG tm      = let val (_,t,_,_,_) = dest_ARM_PROG tm in t end;
fun code_set_ARM_PROG tm  = let val (_,_,t,_,_) = dest_ARM_PROG tm in t end;
fun post1_ARM_PROG tm     = let val (_,_,_,t,_) = dest_ARM_PROG tm in t end;
fun post_ARM_PROG tm      = let val (_,_,_,_,t) = dest_ARM_PROG tm in t end;
fun post2_ARM_PROG tm = 
 (fst o dest_pair o snd o dest_comb o fst o dest_comb o post_ARM_PROG) tm;

val ARM_PROG_PRE_CONV = RATOR_CONV o RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV;
val ARM_PROG_CODE_CONV = RATOR_CONV o RATOR_CONV o RAND_CONV;
val ARM_PROG_POST1_CONV = RATOR_CONV o RAND_CONV;
val ARM_PROG_POST2_CONV = RAND_CONV o RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV;
val ARM_PROG_POST_CONV = RAND_CONV; (* needs to be smarter *)

fun PRE_CONV_RULE c = CONV_RULE (ARM_PROG_PRE_CONV c);
fun CODE_CONV_RULE c = CONV_RULE (ARM_PROG_CODE_CONV c);
fun POST1_CONV_RULE c = CONV_RULE (ARM_PROG_POST1_CONV c);
fun POST2_CONV_RULE c = CONV_RULE (ARM_PROG_POST2_CONV c);
fun POST_CONV_RULE c = CONV_RULE (ARM_PROG_POST2_CONV c);

fun PRE_MOVE_STAR t1 t2 = CONV_RULE (ARM_PROG_PRE_CONV (MOVE_STAR_CONV t1 t2));
fun POST_MOVE_STAR t1 t2 = CONV_RULE (ARM_PROG_POST_CONV (MOVE_STAR_CONV t1 t2));
fun POST1_MOVE_STAR t1 t2 = CONV_RULE (ARM_PROG_POST1_CONV (MOVE_STAR_CONV t1 t2));

fun SPLIT_PROG2 th = let
  val (x,y) = (CONJ_PAIR o RW [ARM_PROG2_def]) th
  val f = RW [PASS_CASES,emp_STAR,F_STAR]
  in (f x,f (Q.ISPEC `(sN:bool,sZ:bool,sC:bool,sV:bool)` y)) end;

val FST_PROG2 = fst o SPLIT_PROG2;
val SND_PROG2 = snd o SPLIT_PROG2;

(* -- simpsets -- *)

val n2w_x_eq_0w = prove(
  ``1073741824w = 0w:word30``,
  ONCE_REWRITE_TAC [GSYM n2w_mod] \\ SIMP_TAC (std_ss++SIZES_ss) []);

val armINST_ss = rewrites 
  [SND,FST,ADDR_MODE1_VAL_def,ADDR_MODE1_CMD_def,ADDR_MODE2_CASES',PASS_CASES,emp_STAR];

val pcINC_ss = rewrites 
  [pcADD_pcADD,pcADD_pcINC,pcINC_pcADD,pcINC_pcINC,pcADD_0,pcINC_0,pcSET_ABSORB];

val setINC_ss = rewrites 
  [setAPP_setAPP,setAPP_UNION,setADD_setADD,setADD_UNION,setAPP_I,setADD_0,
   setINC_def,wLENGTH_def,LENGTH,word_add_n2w,setADD_CLAUSES];

val compose_ss = simpLib.merge_ss [setINC_ss,pcINC_ss,rewrites 
  [UNION_EMPTY,setINC_CLAUSES,setSTAR_CLAUSES,APPEND,
   wLENGTH_def,LENGTH,F_STAR,n2w_x_eq_0w]];

(* -- frame -- *)

val APP_BASIC_FRAME = RW [setSTAR_CLAUSES,F_STAR] o MATCH_MP ARM_PROG_FRAME;
fun APP_FRAME x = RW [F_STAR] o Q.SPEC x o APP_BASIC_FRAME;

(* -- hide pre -- *)

val HIDE_PRE_LEMMA = MATCH_MP EQ_IMP_IMP (SPEC_ALL ARM_PROG_HIDE_PRE);
fun HIDE_PRE th = let 
  val (P,_,_,_,_) = dest_ARM_PROG (concl th)
  val v = (snd o dest_comb o snd o dest_comb) P
  in MATCH_MP HIDE_PRE_LEMMA (GEN v th) end;

(* -- hide post -- *)

val HIDE_POST1_LEMMA = 
  (GEN_ALL o RW [emp_STAR] o Q.INST [`Q`|->`emp`] o SPEC_ALL) ARM_PROG_HIDE_POST1
fun HIDE_POST1 th = let
  val (_,_,_,q,_) = dest_ARM_PROG (concl th)
  val (tm,lemma) = (snd (dest_STAR q),ARM_PROG_HIDE_POST1)
                   handle e =>(q,HIDE_POST1_LEMMA)
  in if is_SEP_HIDE (fst (dest_comb tm))
     then raise ERR "HIDE_POST1" "Has '~' already."
     else MATCH_MP lemma th end;

val HIDE_POST_LEMMA = 
  (GEN_ALL o RW [emp_STAR] o Q.INST [`Q'`|->`emp`] o SPEC_ALL) ARM_PROG_HIDE_POST
fun HIDE_POST th = let
  val (_,_,_,_,q) = dest_ARM_PROG (concl th)
  val q = (fst o dest_pair o snd o dest_comb o fst o dest_comb) q
  val (tm,lemma) = (snd (dest_STAR q),ARM_PROG_HIDE_POST)
                   handle e =>(q,HIDE_POST_LEMMA)
  in if is_SEP_HIDE (fst (dest_comb tm))
     then raise ERR "HIDE_POST" "Has '~' already."
     else MATCH_MP lemma th end;

(* -- move out e.g. `R a` will do ``R b y * R a x * R c z`` -> ``R b y * R c z * R a x`` -- *)

fun MOVE_PRE   t = PRE_CONV_RULE (MOVE_OUT_CONV t);
fun MOVE_POST1 t = POST1_CONV_RULE (MOVE_OUT_CONV t);
fun MOVE_POST  t = POST2_CONV_RULE (MOVE_OUT_CONV t);

fun MOVE_PREL   t = PRE_CONV_RULE (MOVE_OUT_LIST_CONV t);
fun MOVE_POST1L t = POST1_CONV_RULE (MOVE_OUT_LIST_CONV t);
fun MOVE_POSTL  t = POST2_CONV_RULE (MOVE_OUT_LIST_CONV t);

fun MOVE_PRE_TERM   t = PRE_CONV_RULE (MOVE_OUT_TERM_CONV t);
fun MOVE_POST1_TERM t = POST1_CONV_RULE (MOVE_OUT_TERM_CONV t);
fun MOVE_POST_TERM  t = POST2_CONV_RULE (MOVE_OUT_TERM_CONV t);

fun MOVE_PREL_TERM   t = PRE_CONV_RULE (MOVE_OUT_LIST_TERM_CONV t);
fun MOVE_POST1L_TERM t = POST1_CONV_RULE (MOVE_OUT_LIST_TERM_CONV t);
fun MOVE_POSTL_TERM  t = POST2_CONV_RULE (MOVE_OUT_LIST_TERM_CONV t);

(* -- auto hide methods -- *)

fun GENERIC_AUTO_HIDE r c [] th = th
  | GENERIC_AUTO_HIDE r c (t::ts) th =
      GENERIC_AUTO_HIDE r c ts (r (c t th));

val AUTO_HIDE_PRE   = GENERIC_AUTO_HIDE HIDE_PRE   MOVE_PRE;
val AUTO_HIDE_POST  = GENERIC_AUTO_HIDE HIDE_POST  MOVE_POST;
val AUTO_HIDE_POST1 = GENERIC_AUTO_HIDE HIDE_POST1 MOVE_POST1;

val AUTO_HIDE_PRE_TERM   = GENERIC_AUTO_HIDE HIDE_PRE   MOVE_PRE_TERM;
val AUTO_HIDE_POST_TERM  = GENERIC_AUTO_HIDE HIDE_POST  MOVE_POST_TERM;
val AUTO_HIDE_POST1_TERM = GENERIC_AUTO_HIDE HIDE_POST1 MOVE_POST1_TERM;

(* -- add exists to pre -- *)

fun parse_in_thm q th = Parse.parse_in_context (free_varsl (concl th::hyp th)) q;

val EXISTS_PRE_LEMMA = MATCH_MP EQ_IMP_IMP (SPEC_ALL ARM_PROG_EXISTS_PRE);
fun EXISTS_PRE var th = let 
  val v = parse_in_thm var th 
  val th = PRE_CONV_RULE (UNBETA_CONV v) th
  val th = MATCH_MP EXISTS_PRE_LEMMA (GEN v th)   
  val th = PRE_CONV_RULE (RAND_CONV (ALPHA_CONV v)) th
  in BETA_RULE th end;

(* -- align variables -- *)

fun ALIGN_VAR tm = let 
  val x32 = mk_var (tm,``:word32``) 
  val x30 = mk_var (tm,``:word30``) in
  RW [addr30_addr32,GSYM R30_def,addr32_and_3w,addr32_ABSORB_CONST,
      ADDRESS_ROTATE,GSYM addr32_ADD,GSYM addr32_SUB] o 
      INST [x32|->subst [``x:word30``|->x30] ``addr32 x``] end;

fun ALIGN_VARS tms th = foldr (uncurry ALIGN_VAR) th tms;

(* -- hide status -- *)

val HIDE_STATUS_LEMMA = MATCH_MP EQ_IMP_IMP (SPEC_ALL ARM_PROG_HIDE_STATUS)
val HIDE_STATUS_LEMMA_ALT = RW [emp_STAR] (Q.INST [`P`|->`emp`] HIDE_STATUS_LEMMA)
fun HIDE_STATUS th = 
  let val th = GENL [``sN:bool``,``sZ:bool``,``sC:bool``,``sV:bool``] th in
    MATCH_MP HIDE_STATUS_LEMMA th handle e => MATCH_MP HIDE_STATUS_LEMMA_ALT th end;

val STATUS_MOVE = prove(
  ``!P Q x. (S x * P = P * S x) /\ (P * S x * Q = P * Q * S x)``,
  SIMP_TAC (bool_ss++star_ss) []);

val AUTO_PRE_HIDE_STATUS   = HIDE_STATUS o MOVE_PRE `S`;
val AUTO_POST1_HIDE_STATUS = HIDE_POST1 o MOVE_POST1 `S`;
val AUTO_POST_HIDE_STATUS  = HIDE_POST o MOVE_POST `S`;

fun AUTO_HIDE_STATUS th = let
  val th = AUTO_POST1_HIDE_STATUS th handle e => th
  val th = AUTO_POST_HIDE_STATUS th handle e => th
  val th = AUTO_PRE_HIDE_STATUS th handle e => th
  in th end;

(* -- compose -- *)

val RW_COMPOSE = SIMP_RULE (std_ss ++ compose_ss) [];

val MATCH_COMPOSE_LEMMA = (RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_SYM]) ARM_PROG_COMPOSE;
val MATCH_COMPOSE_ALT_LEMMA = RW [GSYM AND_IMP_INTRO] ARM_PROG_COMPOSE;
fun MATCH_COMPOSE th1 th2 = 
  RW_COMPOSE (MATCH_MP (MATCH_MP MATCH_COMPOSE_LEMMA th2) th1) handle e =>
  RW_COMPOSE (MATCH_MP (MATCH_MP MATCH_COMPOSE_ALT_LEMMA th1) th2);

val ARRANGE_COMPOSE_LEMMA = prove(
  ``!P M M' Q cs cs' C C' Z Z'.
      ARM_PROG P cs C M Z /\ ARM_PROG M' cs' C' Q Z' ==> (M = M') ==> 
      ARM_PROG P (cs ++ cs') (C UNION setINC cs C') Q (Z UNION setINC cs Z')``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ARM_PROG_COMPOSE 
  \\ Q.EXISTS_TAC `M'` \\ FULL_SIMP_TAC std_ss []);

fun ARRANGE_COMPOSE th1 th2 = let
  val th = MATCH_MP ARRANGE_COMPOSE_LEMMA (CONJ th1 th2)
  val th = CONV_RULE (RATOR_CONV (RAND_CONV (SIMP_CONV (bool_ss++star_ss) []))) th
  val th = RW_COMPOSE (MP th TRUTH)
  in th end;

fun FRAME_COMPOSE th1 th2 = let
  val (_,_,_,Q,_) = dest_ARM_PROG (concl th1)
  val (P,_,_,_,_) = dest_ARM_PROG (concl th2)
  val QL = list_dest_STAR Q
  val PL = list_dest_STAR P
  val Qfill = filter (fn x => not (mem x QL)) PL
  val Pfill = filter (fn x => not (mem x PL)) QL
  fun frame [] th = th
    | frame xs th = (RW [STAR_ASSOC] o SPEC (list_mk_STAR xs) o APP_BASIC_FRAME) th
  val th1 = frame Qfill th1
  val th2 = frame Pfill th2
  in ARRANGE_COMPOSE th1 th2 end;

val ARM_PROG_COMPOSE_FRAME = prove(
  ``ARM_PROG (Q1 * P2) c2 cc2 Q3 Z2 ==>
    ARM_PROG P1 c1 cc1 (Q1 * Q2) Z1 ==> 
    ARM_PROG (P1 * P2) (c1 ++ c2) 
      (cc1 UNION setINC c1 cc2) (Q3 * Q2) 
      (setSTAR P2 Z1 UNION setINC c1 (setSTAR Q2 Z2))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ARM_PROG_COMPOSE
  \\ Q.EXISTS_TAC `Q1 * P2 * Q2` \\ STRIP_TAC
  << [MOVE_STAR_TAC `q*t*p` `(q*p)*t`,ALL_TAC] \\ METIS_TAC [ARM_PROG_FRAME]);

fun MOVE_COMPOSE th1 th2 xs1 xs2 ys1 ys2 = let
  val th1 = POST1_MOVE_STAR xs1 xs2 th1
  val th2 = PRE_MOVE_STAR ys1 ys2 th2
  val th2 = MATCH_MP ARM_PROG_COMPOSE_FRAME th2
  val th2 = MATCH_MP th2 th1
  val rw = REWRITE_CONV [setSTAR_CLAUSES,setINC_CLAUSES,UNION_EMPTY,APPEND]
  val c1 = RAND_CONV rw
  val c1 = c1 THENC (RATOR_CONV o RATOR_CONV o RAND_CONV) rw
  val c1 = c1 THENC (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) rw
  val th2 = RW [STAR_ASSOC,emp_STAR] (CONV_RULE c1 th2)
  in th2 end;

val FALSE_COMPOSE_LEMMA = prove(
  ``ARM_PROG P1 code1 C1 SEP_F Z1 /\ ARM_PROG P2 code2 C Q Z ==>
    ARM_PROG P1 (code1++code2) C1 SEP_F Z1``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ARM_PROG_APPEND_CODE \\ ASM_REWRITE_TAC []);

fun FALSE_COMPOSE th1 th2 =
  (RW_COMPOSE o MATCH_MP FALSE_COMPOSE_LEMMA) (CONJ th1 th2);
    

(* strengthen, weaken, weaken1 *)

fun APP_X_TERM lemma th t = (fst o dest_imp o concl o Q.SPEC t o MATCH_MP lemma) th;
val APP_STRENGTHEN_TERM = APP_X_TERM ARM_PROG_STRENGTHEN_PRE;
val APP_PART_STRENGTHEN_TERM = APP_X_TERM ARM_PROG_PART_STRENGTHEN_PRE;
val APP_WEAKEN1_TERM = APP_X_TERM ARM_PROG_WEAKEN_POST1;
val APP_PART_WEAKEN1_TERM = APP_X_TERM ARM_PROG_PART_WEAKEN_POST1;
val APP_WEAKEN_TERM = APP_X_TERM ARM_PROG_WEAKEN_POST;
val APP_PART_WEAKEN_TERM = APP_X_TERM ARM_PROG_PART_WEAKEN_POST;

fun APP_X lemma th t tac = let
  val th' = prove(APP_X_TERM lemma th t, tac)
  in MATCH_MP (Q.SPEC t (MATCH_MP lemma th)) th' end;
val APP_STRENGTHEN = APP_X ARM_PROG_STRENGTHEN_PRE;
val APP_PART_STRENGTHEN = APP_X ARM_PROG_PART_STRENGTHEN_PRE;
val APP_WEAKEN1 = APP_X ARM_PROG_WEAKEN_POST1;
val APP_PART_WEAKEN1 = APP_X ARM_PROG_PART_WEAKEN_POST1;
val APP_WEAKEN = APP_X ARM_PROG_WEAKEN_POST;
val APP_PART_WEAKEN = APP_X ARM_PROG_PART_WEAKEN_POST;

fun SPEC_STRENGTHEN th tm = Q.SPEC tm (MATCH_MP ARM_PROG_STRENGTHEN_PRE th);
fun SPEC_WEAKEN1 th tm = Q.SPEC tm (MATCH_MP ARM_PROG_WEAKEN_POST1 th);
fun SPEC_WEAKEN th tm = Q.SPEC tm (MATCH_MP ARM_PROG_WEAKEN_POST th);
fun SEP_IMP_RULE conv = 
  RW [] o (CONV_RULE ((RATOR_CONV o RAND_CONV) 
   (conv THENC SIMP_CONV (bool_ss++star_ss) [SEP_IMP_REFL])));

(* append code *)

fun APP_APPEND th list = let 
  val th = MATCH_MP ARM_PROG_APPEND_CODE th
  in RW [APPEND] (SPEC list th) end;

(* merge specs *)

fun mk_var_list 0 ty = listSyntax.mk_nil ty
  | mk_var_list n ty = listSyntax.mk_cons(genvar ty,mk_var_list (n-1) ty);

fun APP_MERGE th1 th2 =
  let
    val (_,cs1,_,_,_) = dest_ARM_PROG (concl th1) 
    val (_,cs2,_,_,_) = dest_ARM_PROG (concl th2) 
    val len1 = (length o fst o listSyntax.dest_list) cs1 handle e => 0
    val len2 = (length o fst o listSyntax.dest_list) cs2 handle e => 0
    val diff = abs (len1 - len2)    
    val list = mk_var_list diff ``:word32``
    val (th1,th2) = 
      if len1 = len2 then (th1,th2) else
      if len1 < len2 then (APP_APPEND th1 list,th2) else (th1,APP_APPEND th2 list)
    val (_,cs1,_,_,_) = dest_ARM_PROG (concl th1) 
    val (_,cs2,_,_,_) = dest_ARM_PROG (concl th2) 
    val (i,m) = if len1 < len2 then (match_term cs1 cs2) else (match_term cs2 cs1)
    val (th1,th2) = if len1 < len2 then (INST i (INST_TYPE m th1),th2) else 
                                        (th1,INST i (INST_TYPE m th2))
    val th = MATCH_MP ARM_PROG_MERGE (CONJ th1 th2)
    val th = SIMP_RULE (pure_ss++sep_ss) [UNION_IDEMPOT,UNION_EMPTY,
               STAR_OVER_DISJ,EXCLUDED_MIDDLE,RW1[DISJ_COMM]EXCLUDED_MIDDLE] th
  in th end;

val ARM_PROG_DUPLICATE_COND_LEMMA = prove(
  ``ARM_PROG (P * cond h) code C Q Z ==>
    ARM_PROG (P * cond h) code C (Q * cond h) (setSTAR (cond h) Z)``,
  REPEAT STRIP_TAC \\ POP_ASSUM 
   (ASSUME_TAC o RW [GSYM STAR_ASSOC,SEP_cond_CLAUSES] o APP_FRAME `cond h`)
  \\ ASM_REWRITE_TAC [])
  
fun DUPLICATE_COND th = let
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = MATCH_MP ARM_PROG_DUPLICATE_COND_LEMMA th
  val th = RW [emp_STAR] (APP_FRAME `emp` th)
  in th end;  

(* in preparation for application of FRAME_COMPOSE *)

fun GENERIC_MATCH_INST sel1 sel2 ts th1 th2 = let
  val ctxt = free_varsl ((hyp th1)@(hyp th2)@[concl th1,concl th2])
  val tms = map (Parse.parse_in_context ctxt) ts
  fun MATCH_INST_ONCE th1 (tm,th2) = let
    fun finder t1 = (aconv tm o fst o dest_comb) t1 handle e => false
    val tm1 = find_term finder (sel1 (concl th1))
    val tm2 = find_term finder (sel2 (concl th2))
    val (i,m) = match_term tm2 tm1
    in (INST i o INST_TYPE m) th2 end;
  in foldr (MATCH_INST_ONCE th1) th2 tms end;

val MATCH_INST1 = GENERIC_MATCH_INST post1_ARM_PROG pre_ARM_PROG;
val MATCH_INST  = GENERIC_MATCH_INST post_ARM_PROG  pre_ARM_PROG;

(* in preparation for application of induction *)

fun EXTRACT_CODE th = let 
  val th = RW1 [ARM_PROG_EXTRACT_POST] th
  val th = RW1 [ARM_PROG_EXTRACT_CODE] th
  val th = CONV_RULE ((RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV) 
             (SIMP_CONV std_ss [pcINC_def,wLENGTH_def,LENGTH,pcADD_0])) th
  in th end;

val ARM_PROG_ABSORB_POST_LEMMA = prove(
  ``ARM_PROG P cs C SEP_F ((Q,pcADD x) INSERT Z) ==>
    (x = wLENGTH cs) ==> ARM_PROG P cs C Q Z``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [GSYM ARM_PROG_EXTRACT_POST,GSYM pcINC_def]);

fun ABSORB_POST th = let
  val th = MATCH_MP ARM_PROG_ABSORB_POST_LEMMA (SPEC_ALL th)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [wLENGTH_def,LENGTH])) th
  in RW [] th end;

fun CLOSE_LOOP th = let
  val th = SIMP_RULE std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w] th
  val (_,_,_,_,q) = dest_ARM_PROG (concl (RW [GSYM WORD_ADD_ASSOC] th))
  val t = (snd o dest_comb o snd o dest_pair o snd o dest_comb o fst o dest_comb) q
  val x = (snd o dest_comb o snd o dest_comb o fst o dest_comb) t
  val y = (snd o dest_comb o snd o dest_comb) t
  val tm = subst [``n:num``|->y] ``0w:word24 - n2w n``  
  in (RW [EVAL tm,pcADD_0] o RW [EVAL (subst [x|->tm] t)] o INST [x |-> tm]) th end;

(* others *)

val ARM_PROG_EMPTY_CODE = prove(
  ``ARM_PROG P cs (([],f) INSERT C) Q Z = ARM_PROG P cs C Q Z``,
  REWRITE_TAC [ARM_PROG_THM] \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ REWRITE_TAC [ARM_GPROG_EMPTY_CODE]);

fun PROG2PROC lr th = let
  val th = MOVE_POST `R 14w` (MOVE_POST `S` th)
  val th = MOVE_PRE `R30 14w` (MOVE_PRE `S` th)
  val th = Q.GEN lr (EXTRACT_CODE th)
  val th = RW [ARM_PROG_EMPTY_CODE] th
  val th = RW [ARM_PROG_FALSE_POST,GSYM ARM_PROC_THM] th
  in th end;

fun FORCE_PBETA_CONV tm = let
  val (tm1,tm2) = dest_comb tm
  val vs = fst (pairSyntax.dest_pabs tm1)
  fun expand_pair_conv tm = ISPEC tm (GSYM PAIR)
  fun get_conv vs = let
    val (x,y) = dest_pair vs
    in expand_pair_conv THENC (RAND_CONV (get_conv y)) end 
    handle e => ALL_CONV
  in (RAND_CONV (get_conv vs) THENC PairRules.PBETA_CONV) tm end;

fun PAT_DISCH pat th = let 
  val tm = hd (filter (can (match_term pat)) (hyp th))
  in DISCH tm th end;

fun PAIR_GEN name vs th = let 
  val ctxt = free_varsl(concl th::hyp th)
  val x = Parse.parse_in_context ctxt vs
  in pairTools.PGEN (mk_var(name,type_of x)) x th end;

fun QGENL [] th = th | QGENL (x::xs) th = Q.GEN x (QGENL xs th);

fun INST_LDM_STM do_eval c mode th list = let
  val th = Q.INST [`a_mode`|->mode,`c_flag`|->c] th
  val th = Q.INST [`xs`|->list] th
  val th = RW [LENGTH,ADDR_MODE4_ADDR_def,ADDR_MODE4_ADDR'_def,
               ADDR_MODE4_WB'_def,ADDR_MODE4_UP_def,MAP,ADDR_MODE4_WB_def,
               ADDR_MODE4_wb_def,xR_list_def,STAR_ASSOC] th
  val th = REWRITE_RULE [ADD1,GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_ADD] th
  val th = SIMP_RULE arith_ss [GSYM WORD_SUB_PLUS,word_add_n2w,WORD_SUB_RZERO] th
  val th = SIMP_RULE (std_ss++sep_ss) [MAP,xR_list_def,STAR_ASSOC,ADDR_MODE4_CMD_def,GSYM WORD_ADD_ASSOC,word_add_n2w] th
  val th = RW [PASS_CASES,emp_STAR] th
  val tm = find_term (can (match_term ``reg_values x``)) (concl th) handle e => T
  val th = if do_eval then RW [RW [GSYM (EVAL ``addr32 x``)] (EVAL tm)] th else th
  val tm = find_term (can (match_term ``reg_bitmap x``)) (concl th) handle e => T
  val th = if do_eval then RW [EVAL tm] th else th
  in th end;


(* ============================================================================= *)
(* PRETTY-PRINTER FOR ``enc (instruction)``                                      *)
(* ============================================================================= *)

val show_enc = ref false;
val show_code = ref true;

fun blanks 0 = [] | blanks n = #" "::blanks (n-1);
fun blank_str n = implode (blanks (if n < 0 then 0 else n));

fun print_enc_inst sys (gl,gc,gr) d pps t = 
  if !show_enc andalso !show_code then raise term_pp_types.UserPP_Failed else
  let open Portable term_pp_types in 
    if not (fst (dest_comb t) = ``enc:arm_instruction -> word32``) then
      raise term_pp_types.UserPP_Failed
    else 
      if not (!show_code) then () else let 
        val s = instructionSyntax.dest_instruction NONE (snd (dest_comb t))
        val s = hd (String.fields (fn s => if s = #";" then true else false) s) 
        val (s1,s2) = ("    ",blank_str (40-size s))
        in 
          begin_block pps INCONSISTENT 0; add_string pps (s1^s^s2); end_block pps
        end handle e => let
        val (x,y) = dest_comb (snd (dest_comb t))
        val t = subst [y|->``0w:word24``] t
        val s = instructionSyntax.dest_instruction NONE (snd (dest_comb t))
        val s = hd (String.fields (fn s => if s = #";" then true else false) s) 
        val s = substring(s,0,size(s)-1) ^ "<" ^ fst (dest_var y) ^ ">"
        val (s1,s2) = ("    ",blank_str (40-size s))
        in 
          begin_block pps INCONSISTENT 0; add_string pps (s1^s^s2); end_block pps
        end 
  end handle e => raise term_pp_types.UserPP_Failed;

fun pp_enc() = Parse.temp_add_user_printer ({Tyop = "cart", Thy = "fcp"}, print_enc_inst);
val _ = pp_enc();


(* ============================================================================= *)
(* EXPERIMENTAL PROOF-PRODUCING FUNCTIONS                                        *)
(* ============================================================================= *)

(* handling terms *)

fun TERM_CONV (conv:term->thm) = snd o dest_eq o concl o conv;
fun TERM_RW thms = TERM_CONV (QCONV (REWRITE_CONV thms));

fun get_term pat tm = find_term (can (match_term pat)) tm;

fun list_get_term pat tm = let
  val m = can (match_term pat)
  fun d mat tm = subst [mat|->genvar (type_of mat)] tm
  fun list_repeat f x g = 
    let val y = f x in y :: list_repeat f (g y x) g end handle e => []
  in list_repeat (find_term m) tm d end;


(* printing helpers *)

val remove_new_lines =
  String.translate (fn #"\n" => " " | x => implode [x]);

fun list_to_string f [] sep = ""
  | list_to_string f [x] sep = f x
  | list_to_string f (x::y::xs) sep = f x ^ sep ^ list_to_string f (y::xs) sep;

fun term_to_string_show_types tm = let
  val b = !show_types
  val _ = show_types := true
  val st = remove_new_lines (term_to_string tm) 
  val _ = show_types := b
  in st end; 

fun subst_to_string xs indent =
  let fun f {redex = x, residue = y} = 
      "`" ^ term_to_string_show_types x ^ "`|->`" ^ term_to_string_show_types y ^ "`"
  in "[" ^ list_to_string f xs "," ^ " ]" end;

fun subst_to_string_no_types xs indent =
  let fun f {redex = x, residue = y} = 
      "`" ^ term_to_string x ^ "`|->`" ^ term_to_string y ^ "`"
  in "[" ^ remove_new_lines (list_to_string f xs ",") ^ " ]" end;

fun mk_QINST_string i name1 name2 indent = let
  val i_string = subst_to_string i indent
  val str = indent ^ "val "^name1^" = Q.INST\n" ^ i_string ^ " " ^ name2
  in str end;

(* mk_QINST_string [``a:num``|->``5:num``] "th1" "th2" "  " *)


(* construct code for spec specialisation *)

val code_from_basic_ARM_PROG2 = 
  snd o dest_comb o snd o dest_comb o fst o dest_comb o 
  snd o dest_comb o fst o dest_comb o fst o dest_comb;

val basic_match_list = 
  [(arm_ADC1,"arm_ADC1"),(arm_ADC2,"arm_ADC2"),(arm_ADC2',"arm_ADC2'"),(arm_ADC2'',"arm_ADC2''"),(arm_ADC3,"arm_ADC3"),
   (arm_ADD1,"arm_ADD1"),(arm_ADD2,"arm_ADD2"),(arm_ADD2',"arm_ADD2'"),(arm_ADD2'',"arm_ADD2''"),(arm_ADD3,"arm_ADD3"),
   (arm_AND1,"arm_AND1"),(arm_AND2,"arm_AND2"),(arm_AND2',"arm_AND2'"),(arm_AND2'',"arm_AND2''"),(arm_AND3,"arm_AND3"),
   (arm_BIC1,"arm_BIC1"),(arm_BIC2,"arm_BIC2"),(arm_BIC2',"arm_BIC2'"),(arm_BIC2'',"arm_BIC2''"),(arm_BIC3,"arm_BIC3"),
   (arm_EOR1,"arm_EOR1"),(arm_EOR2,"arm_EOR2"),(arm_EOR2',"arm_EOR2'"),(arm_EOR2'',"arm_EOR2''"),(arm_EOR3,"arm_EOR3"),
   (arm_ORR1,"arm_ORR1"),(arm_ORR2,"arm_ORR2"),(arm_ORR2',"arm_ORR2'"),(arm_ORR2'',"arm_ORR2''"),(arm_ORR3,"arm_ORR3"),
   (arm_RSB1,"arm_RSB1"),(arm_RSB2,"arm_RSB2"),(arm_RSB2',"arm_RSB2'"),(arm_RSB2'',"arm_RSB2''"),(arm_RSB3,"arm_RSB3"),
   (arm_RSC1,"arm_RSC1"),(arm_RSC2,"arm_RSC2"),(arm_RSC2',"arm_RSC2'"),(arm_RSC2'',"arm_RSC2''"),(arm_RSC3,"arm_RSC3"),
   (arm_SBC1,"arm_SBC1"),(arm_SBC2,"arm_SBC2"),(arm_SBC2',"arm_SBC2'"),(arm_SBC2'',"arm_SBC2''"),(arm_SBC3,"arm_SBC3"),
   (arm_SUB1,"arm_SUB1"),(arm_SUB2,"arm_SUB2"),(arm_SUB2',"arm_SUB2'"),(arm_SUB2'',"arm_SUB2''"),(arm_SUB3,"arm_SUB3"),
   (arm_CMN1,"arm_CMN1"),(arm_CMN2,"arm_CMN2"),
   (arm_CMP1,"arm_CMP1"),(arm_CMP2,"arm_CMP2"),
   (arm_TST1,"arm_TST1"),(arm_TST2,"arm_TST2"),
   (arm_TEQ1,"arm_TEQ1"),(arm_TEQ2,"arm_TEQ2"),
   (arm_MOV1,"arm_MOV1"),(arm_MOV2,"arm_MOV2"),
   (arm_MVN1,"arm_MVN1"),(arm_MVN2,"arm_MVN2"),
   (arm_MUL2,"arm_MUL2"),(arm_MUL2'',"arm_MUL2''"),(arm_MUL3,"arm_MUL3"),
   (arm_MLA3,"arm_MLA3"),(arm_MLA3',"arm_MLA3'"),(arm_MLA3'',"arm_MLA3''"),(arm_MLA4,"arm_MLA4"),
   (arm_UMULL3,"arm_UMULL3"),(arm_UMULL3',"arm_UMULL3'"),(arm_UMULL3'',"arm_UMULL3''"),(arm_UMULL4,"arm_UMULL4"),
   (arm_SMULL3,"arm_SMULL3"),(arm_SMULL3',"arm_SMULL3'"),(arm_SMULL3'',"arm_SMULL3''"),(arm_SMULL4,"arm_SMULL4"),
   (arm_UMLAL3'',"arm_UMLAL3''"),(arm_UMLAL4,"arm_UMLAL4"),
   (arm_SMLAL3'',"arm_UMLAL3''"),(arm_SMLAL4,"arm_UMLAL4"),
   (arm_SWPB2,"arm_SWPB2"),(arm_SWPB3,"arm_SWPB3"),
   (arm_LDRB1,"arm_LDRB1"),(arm_LDRB,"arm_LDRB"),(arm_STRB,"arm_STRB")];

val match_list = 
  [(arm_MOV_PC_GENERAL,"arm_MOV_PC_GENERAL"),(arm_B2,"arm_B2"),(arm_LDR_PC,"arm_LDR_PC"),
   (arm_SWP2_NONALIGNED,"arm_SWP2_NONALIGNED"),(arm_SWP3_NONALIGNED,"arm_SWP3_NONALIGNED"),
   (arm_LDR1_NONALIGNED,"arm_LDR1_NONALIGNED"),(arm_LDR_NONALIGNED,"arm_LDR_NONALIGNED"),
   (arm_STR_NONALIGNED,"arm_STR_NONALIGNED")] @ basic_match_list;

val inst_str = "add r1, r2 ,r3"
val suffix = "2"

fun mk_arm_prog2_str inst_str suffix = let
  val tm = mk_instruction inst_str
  fun extract_am1 pat tm = 
    (snd o dest_comb o fst o dest_comb o TERM_RW [GSYM ADDR_MODE1_CMD_def] o get_term pat) tm
  val ii = [``a_mode:abbrev_addr1``|-> extract_am1 ``Dp_immediate m n`` tm] handle e =>
           [``a_mode:abbrev_addr1``|-> extract_am1 ``Dp_shift_immediate m n`` tm] handle e => [];
  val fix_ii = TERM_RW [ADDR_MODE1_CMD_def] o subst ii
  fun filt (th,name) = let
    val tm' = code_from_basic_ARM_PROG2 (concl th)
    val tm' = fix_ii tm'
    in can (match_term tm') tm end
  val xs = filter filt match_list
  val (th,name) = hd xs handle e => raise ERR "arm_str2prog" ("No match for: "^inst_str)
  val tm' = code_from_basic_ARM_PROG2 (concl th)
  val tm' = fix_ii tm'
  val (i,it) = match_term tm' tm
  val i = i @ ii
  val th = INST i th
  val th = SIMP_RULE (bool_ss ++ armINST_ss) [] th
  val vs = free_vars_lr (concl th)
  val vs' = free_vars_lr (code_from_basic_ARM_PROG2 (concl th))
  val vs' = vs' @ [``sN:bool``,``sZ:bool``,``sC:bool``,``sV:bool``]
  val vs = filter (fn v => not (mem v vs')) vs  
  fun app_suffix v = let val (st,ty) = dest_var v in mk_var (st^suffix,ty) end
  val vs = map (fn tm => tm |-> app_suffix tm) vs
  val i = if suffix = "" then i else i @ vs 
  val th = INST vs th
  val evals = list_get_term ``(w2w ((n2w n):'qqq word)):'zzz word`` (concl th)  
  val evals = evals @ list_get_term ``(n2w m) = ((n2w n):'qqq word)`` (concl th)
  val evals = evals @ list_get_term ``(w2n ((n2w n):'qqq word)):num`` (concl th)  
  val evals = evals @ list_get_term ``(sw2sw ((n2w n):'qqq word)):'zzz word`` (concl th)  
  val th = RW (map EVAL evals) th
  val evals = evals @ list_get_term ``(n2w m) + (n2w n):'qqq word`` (concl th)
  val th = RW (map EVAL evals) th
  val s = "EVAL ``" ^ list_to_string term_to_string_show_types evals "``, EVAL ``" ^ "``"
  val s = if evals = [] then "" else s
  val str = "SIMP_RULE (bool_ss++armINST_ss) ["^s^"] (Q.INST "^ 
             subst_to_string_no_types i "  " ^ " " ^ name ^ ")"
  in (th,str) end;

val string_to_prog = mk_arm_prog2_str

fun mk_arm_prog2_string inst_str thm_name suffix indent = let
  val (th,str) = mk_arm_prog2_str inst_str suffix
  val str = indent ^"val " ^ thm_name ^ " = ("^"*  "^inst_str^"  *"^") "^str
  in (th,str) end;

fun print_arm_prog2 str thm_name suffix indent = 
  print ("\n\n"^ snd (mk_arm_prog2_string str thm_name suffix indent) ^"\n\n");

fun mk_arm_prog2_string_list [] thm_name count indent = ([],"")
  | mk_arm_prog2_string_list (x::xs) thm_name count indent =
    let val s = int_to_string count 
        val (y,st) = mk_arm_prog2_string x (thm_name ^ s) s indent
        val (ys,st') = mk_arm_prog2_string_list xs thm_name (count + 1) indent
    in (y::ys,st ^ "\n" ^ st') end;

fun print_arm_prog2_list strs thm_name count indent = 
  print ("\n\n"^ snd (mk_arm_prog2_string_list strs thm_name count indent) ^"\n\n");


(* 
val (inst_str,thm_name,suffix,indent) = ("add a, b, #34","th","2","  ")
print_arm_prog2 "ldrb r1, [r2,#35]" "th" "3" "  " 
print_arm_prog2_list ["add a, b, c","sub b, a, d","mul c, d, e"] "th" 1 "  "
mk_arm_prog2_string_list ["add a, b, c","sub b, c, d","mul c, d, e"] "th" 1 "  "
print_arm_prog2 "ldr r15, [r2,#35]" "th" "3" "  " 
*)
    

(* make code for composing basic specs *)

fun comb_match_right tm1 tm2 = let
  val (x1,t1) = dest_comb tm1
  val (x2,t2) = dest_comb tm2      
  in if aconv x1 x2 then match_term t1 t2 else raise ERR "comb_match_right" "No match." end; 

fun std_matcher tm1 tm2 =
  let val r = ``(R a x):'a ARMset -> bool``
      val m = ``(M a x):'a ARMset -> bool`` in
  if can (match_term r) tm2 orelse can (match_term m) tm2 
    then comb_match_right tm1 tm2 else match_term tm1 tm2 end;

fun find_composition (th1,name1) (th2,name2) = let
  val (_,_,_,Q,_) = dest_ARM_PROG (concl th1)
  val (P,_,_,_,_) = dest_ARM_PROG (concl th2)
  fun number i [] = [] | number i (x::xs) = (x,i) :: number (i+1) xs
  val xs = number 1 (list_dest_STAR Q)
  val ys = number 1 (list_dest_STAR P)
  fun m x y = can (std_matcher y) x
  fun fetch_match (x,i) [] = (0,0,tl [])
    | fetch_match (x,i) ((y,j)::ys) = if m x y then (i,j,ys) else 
        let val (i1,j1,zs) = fetch_match (x,i) ys in (i1,j1,(y,j)::zs) end
  fun partition [] ys (xs1,xs2,ys1,ys2) = (xs1,xs2,ys1,ys2 @ map snd ys)
    | partition (x::xs) ys (xs1,xs2,ys1,ys2) =
        let val (i,j,zs) = fetch_match x ys in
          partition xs zs (xs1 @ [i], xs2, ys1 @ [j], ys2)
        end handle e =>
          partition xs ys (xs1, xs2 @ [snd x], ys1, ys2)
  val (xs1,xs2,ys1,ys2) = partition xs ys ([],[],[],[])
  fun mk_star_q [] = "emp"
    | mk_star_q [i] = "x" ^ int_to_string i
    | mk_star_q (i::is) = "x" ^ int_to_string i ^ "*" ^ mk_star_q is
  val xs_str1 = mk_star_q (map snd xs) 
  val xs_str2 = "(" ^ mk_star_q xs1 ^ ")*(" ^ mk_star_q xs2 ^ ")" 
  val ys_str1 = mk_star_q (map snd ys) 
  val ys_str2 = "(" ^ mk_star_q ys1 ^ ")*(" ^ mk_star_q ys2 ^ ")" 
  val (xs1,xs2) = ([QUOTE xs_str1],[QUOTE xs_str2])
  val (ys1,ys2) = ([QUOTE ys_str1],[QUOTE ys_str2])
  val th = MOVE_COMPOSE th1 th2 xs1 xs2 ys1 ys2
  val str = "MOVE_COMPOSE "^ name1 ^" "^ name2 ^" `"^ 
            xs_str1 ^"` `"^ xs_str2 ^"` `"^ ys_str1 ^"` `"^ ys_str2 ^"`"
  in (th,str) end;

fun get_unaligned tm = let
  val tm = find_term (can (match_term ``M (addr30 x)``)) tm
  val tm = (snd o dest_comb o snd o dest_comb) tm  
  val tm = (snd o dest_comb o fst o dest_comb) tm handle e => tm
  val str = (fst o dest_var) tm
  in str end;

fun align_addresses th = let
  fun find_unaligned th xs = let
    val st = get_unaligned (concl th)
    val th = ALIGN_VARS [st] th 
    in find_unaligned th (st::xs) end
    handle e => (th,xs);
  val (th,xs) = find_unaligned th []
  fun str_list_to_str [] = ""
    | str_list_to_str [x] = "\"" ^ x ^ "\""
    | str_list_to_str (x::y::xs) = "\"" ^ x ^ "\"," ^ str_list_to_str (y::xs)
  val st = "[" ^ str_list_to_str xs ^ "]"
  val st = "ALIGN_VARS "^st^" "
  val st = if xs = [] then "" else st
  in (th,st) end;

fun pad_strings [] = [] | pad_strings (x::xs) = let
  val m = foldr (fn (m,n) => if m > n then m else n) (size x) (map size xs)
  fun pad s i = if i <= 0 then s else pad (s^" ") (i-1) 
  in map (fn s => pad s (m - size s)) (x::xs) end;

fun compose_progs_string [] = (TRUTH,"")
  | compose_progs_string strs = let
  val xs = pad_strings (map fst strs)
  fun specs [] i = [] | specs (x::xs) i =
    mk_arm_prog2_str x (int_to_string i) :: specs xs (i+1)
  val xs = zip (zip (specs xs 1) xs) (map snd strs)    
  fun unwrap (((th,s),n),true)  = (FST_PROG2 th, "FST_PROG2 ("^s^")",n) 
    | unwrap (((th,s),n),false) = (SND_PROG2 th, "SND_PROG2 ("^s^")",n) 
  val xs = map unwrap xs    
  fun find_compositions th [] = ([],th) 
    | find_compositions th ((th2,name,c)::xs) = let
      val (th,s) = find_composition (th,"th") (th2,"("^name^")")
      val s = "  val th = ("^"*  "^c^"  *"^") "^s^"\n"
      val (ys,th) = find_compositions th xs
      in (s::ys,th) end
  val (th,s1,n1) = hd xs
  val (xs,th) = find_compositions th (tl xs)
  val s1 = "  val th = ("^"*  "^n1^"  *"^") "^s1^"\n"
  val str = foldl (fn (s,t) => t^s) s1 xs  
  val th = AUTO_HIDE_STATUS th
  val s1 = "AUTO_HIDE_STATUS th"
  val (th,st) = align_addresses th
  val str = if st = "" then str ^ "  val th = "^s1^"\n" 
                       else str ^ "  val th = "^st^"("^s1^")\n"
  in (th,str) end;

fun make_spec' strs = print ("\n\n"^ snd (compose_progs_string strs) ^"\n\n");
fun make_spec strs = make_spec' (map (fn name => (name,true)) strs)


(* make code for composing basic specs *)

fun comb_match_right tm1 tm2 = let
  val (x1,t1) = dest_comb tm1
  val (x2,t2) = dest_comb tm2      
  in if aconv x1 x2 then match_term t1 t2 else raise ERR "comb_match_right" "No match." end; 

fun std_matcher tm1 tm2 =
  let val r = ``(R a x):'a ARMset -> bool``
      val m = ``(M a x):'a ARMset -> bool`` in
  if can (match_term r) tm2 orelse can (match_term m) tm2 
    then comb_match_right tm1 tm2 else match_term tm1 tm2 end;

fun find_substs th1 th2 indent = let
  val (_,_,_,post1,_) = dest_ARM_PROG (concl th1)
  val (pre2,_,_,_,_) = dest_ARM_PROG (concl th2)
  val xs = list_dest_STAR post1
  val ys = list_dest_STAR pre2
  fun try_match tm (x,y) = std_matcher x tm handle e => y
  fun find_match tm xs = foldr (try_match tm) ([],[]) xs
  fun find_matches [] ys = [([],[])]
    | find_matches (x::xs) ys = 
        let val m = find_match x ys in
        m :: find_matches xs ys end;
  fun compact_step ((s,t),(s',t')) = (s @ s',t @ t')
  fun compact ms = foldr compact_step ([],[]) ms
  val i = fst (compact (find_matches xs ys))
  in i end;

fun find_composition (th1,name1) (th2,name2) name indent = let
  val i = find_substs th1 th2 (indent ^ "  ")
  val i_string = subst_to_string i indent
  val str = indent ^ "val "^name^" = FRAME_COMPOSE "^name1^" (Q.INST " ^
    subst_to_string i indent ^ " " ^ name2 ^ ")\n"
  val th = INST i th2
  val th = FRAME_COMPOSE th1 th
  in (th,str) end;  

fun find_compositions [] name indent = (TRUTH,"")
  | find_compositions [(th1,name1)] name indent = 
      if name1 = name then (th1,"") else (th1,indent ^ "val " ^name^ " = " ^name1)
  | find_compositions ((th1,name1)::(th2,name2)::thms) name indent = let 
      val (th,s) = find_composition (th1,name1) (th2,name2) name indent 
      val (th',str) = find_compositions ((th,name)::thms) name indent
      in (th',s ^ str) end;     

fun print_compositions thms name indent = 
  print ("\n\n"^snd (find_compositions thms name indent)^"\n\n")

(* for debugging:

print_arm_prog2_list ["add a, b, c","sub b, c, d","mul c, d, e"] "th" 1 "  "

  val th1 = (*  add a, b, c  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`a`,`a`|->`b`,`b`|->`c`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_ADD3) 
  val th2 = (*  sub b, c, d  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`b`,`a`|->`c`,`b`|->`d`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_SUB3) 
  val th3 = (*  mul c, d, e  *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`d`,`b`|->`e`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_MUL3) 

print_compositions [(FST_PROG2 th1,"(FST_PROG2 th1)"),(FST_PROG2 th2,"(FST_PROG2 th2)"),(FST_PROG2 th3,"(FST_PROG2 th3)")] "th" "  "

  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(z2 :word32)`|->`(x1 :word32)`,`(x2 :word32)`|->`(y1 :word32)` ] (FST_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(z3 :word32)`|->`(y1 :word32)`,`(x3 :word32)`|->`(y2 :word32)` ] (FST_PROG2 th3))

*)

(* find specs and compose *)

fun compose_progs_string' strs name index indent = let
  val (xs,s1) = mk_arm_prog2_string_list (map fst strs) name index indent
  fun g (th,true) = (FST_PROG2 th,true) | g (th,false) = (SND_PROG2 th,false)
  val xs = map g (zip xs (map snd strs))
  fun f [] n = [] | 
      f ((x,true)::xs) n  = "(FST_PROG2 "^name^(int_to_string n)^")" :: f xs (n+1) | 
      f ((x,false)::xs) n = "(SND_PROG2 "^name^(int_to_string n)^")" :: f xs (n+1)
  val xs = zip (map fst xs) (f xs index)
  val (th,s2) = find_compositions xs name indent
  in (th,s1^s2) end;

fun compose_progs'' strs name indent index = 
  print ("\n\n"^ snd (compose_progs_string' strs name index indent) ^"\n\n");

fun compose_progs' strs name indent = compose_progs'' strs name indent 1;
fun compose_progs strs name indent = compose_progs' (map (fn st => (st,true)) strs) name indent;


(*  
compose_progs ["add a, b, c","sub d, a, d","mul c, d, e"] "th" "  "
compose_progs' [("cmp a, #1",true),("moveq pc,r14",false)] "th" "  "
compose_progs ["ldr r15,[a],#4"] "th" "  "
*)


end




