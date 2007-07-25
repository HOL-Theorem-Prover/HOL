structure arm_compilerLib :> arm_compilerLib =
struct

(*
  quietdec := true;
  val armDir = concat Globals.HOLDIR "/examples/ARM/v4";
  val yaccDir = concat Globals.HOLDIR "/tools/mlyacc/mlyacclib";
  loadPath := !loadPath @ [armDir,yaccDir];
*)
 
open HolKernel boolLib bossLib Parse;
open listTheory wordsTheory pred_setTheory arithmeticTheory pairTheory wordsLib;
open set_sepTheory progTheory arm_progTheory arm_instTheory set_sepLib;
open instructionSyntax;
 
(*
  quietdec := false;
*)

val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8",
                        "r9","r10","r11","r12","r13","r14","r15"];

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val EQ_IMP_IMP = METIS_PROVE [] ``(x=y) ==> x ==> y``;

fun replace_char c str = 
  String.translate (fn x => if x = c then str else implode [x]);

val code_length_rewrites = ref ([]:thm list);

fun code_length_conv () = 
  SIMP_CONV arith_ss ([LENGTH,LENGTH_APPEND] @ !code_length_rewrites);


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

fun pre_ARM_PROG tm   = let val (t,_,_,_,_) = dest_ARM_PROG tm in t end;
fun code_ARM_PROG tm  = let val (_,t,_,_,_) = dest_ARM_PROG tm in t end;
fun post1_ARM_PROG tm = let val (_,_,_,t,_) = dest_ARM_PROG tm in t end;
fun post_ARM_PROG tm  = let val (_,_,_,_,t) = dest_ARM_PROG tm in t end;
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
fun POST_CONV_RULE c = CONV_RULE (ARM_PROG_POST_CONV c);

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
  [SND,FST,ADDR_MODE1_VAL_def,ADDR_MODE1_CMD_def,
   ADDR_MODE2_CASES',PASS_CASES,emp_STAR];

val armINST2_ss = rewrites 
  [SND,FST,ADDR_MODE1_VAL_def,ADDR_MODE1_CMD_def,
   ADDR_MODE2_CASES',PASS_CASES,emp_STAR,WORD_CMP_NORMALISE];

val pcINC_ss = rewrites 
  [pcADD_pcADD,pcADD_pcINC,pcINC_pcADD,pcINC_pcINC,pcADD_0,pcINC_0,pcSET_ABSORB,pcINC_def];

val setINC_ss = rewrites 
  [setAPP_setAPP,setAPP_UNION,setADD_setADD,setADD_UNION,setAPP_I,setADD_0,
   setINC_def,wLENGTH_def,LENGTH,word_add_n2w,setADD_CLAUSES];

val compose_ss = simpLib.merge_ss [setINC_ss,pcINC_ss,rewrites 
  [UNION_EMPTY,setINC_CLAUSES,setSTAR_CLAUSES,APPEND,
   wLENGTH_def,LENGTH,F_STAR,word_add_n2w,F_STAR,n2w_x_eq_0w]];

val compose2_ss = simpLib.merge_ss [setINC_ss,pcINC_ss,rewrites 
  [UNION_EMPTY,setINC_CLAUSES,setSTAR_CLAUSES,APPEND,WORD_CMP_NORMALISE,
   wLENGTH_def,LENGTH,F_STAR,word_add_n2w,F_STAR,n2w_x_eq_0w]];

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

(* -- hide status from anywhere *)

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
  val cc = SIMP_CONV arith_ss ([wLENGTH_def,LENGTH,LENGTH_APPEND] @ (!code_length_rewrites))
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) cc) th
  in RW [] th end;

fun CLOSE_LOOP th = let
  val th = SIMP_RULE std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w] th
  val (_,_,_,_,q) = dest_ARM_PROG (concl (RW [GSYM WORD_ADD_ASSOC] th))
  val t = (snd o dest_comb o snd o dest_pair o snd o dest_comb o fst o dest_comb) q
  val x = (snd o dest_comb o snd o dest_comb o fst o dest_comb) t
  val y = (snd o dest_comb o snd o dest_comb) t
  val tm = subst [``n:num``|->y] ``0w:word24 - n2w n``  
  in (RW [EVAL tm,pcADD_0] o RW [EVAL (subst [x|->tm] t)] o INST [x |-> tm]) th end;

(* -- compose -- *)

val RW_COMPOSE = SIMP_RULE (std_ss ++ compose_ss) [];
val RW_COMPOSE2 = SIMP_RULE (std_ss ++ compose2_ss) [];

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
  val th2 = RW_COMPOSE th2 
  in th2 end;

fun MOVE_COMPOSE2 th1 th2 xs1 xs2 ys1 ys2 = let
  val th = MOVE_COMPOSE th1 th2 xs1 xs2 ys1 ys2
  val th = RW_COMPOSE2 th
  val th = CONV_RULE (code_length_conv()) th
  val th = RW_COMPOSE2 th
  in th end;

val FALSE_COMPOSE_LEMMA = prove(
  ``ARM_PROG P1 code1 C1 SEP_F Z1 /\ ARM_PROG P2 code2 C Q Z ==>
    ARM_PROG P1 (code1++code2) C1 SEP_F Z1``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ARM_PROG_APPEND_CODE \\ ASM_REWRITE_TAC []);

fun FALSE_COMPOSE th1 th2 =
  (RW_COMPOSE o MATCH_MP FALSE_COMPOSE_LEMMA) (CONJ th1 th2);
    

(* strengthen, weaken, weaken1 *)

val STRENGTHEN_LEMMA = 
  (DISCH_ALL o Q.GEN `P'` o UNDISCH o SPEC_ALL o 
   RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_SYM]) ARM_PROG_STRENGTHEN_PRE;

val PART_STRENGTHEN_LEMMA = prove(
  ``ARM_PROG (P * P') cs C Q Z ==> !P''. SEP_IMP P'' P' ==> ARM_PROG (P * P'') cs C Q Z``,
  METIS_TAC [ARM_PROG_STRENGTHEN_PRE,SEP_IMP_FRAME,STAR_SYM]);

val WEAKEN1_LEMMA = 
  (DISCH_ALL o Q.GEN `Q'` o UNDISCH o SPEC_ALL o 
   RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_SYM]) ARM_PROG_WEAKEN_POST1;

val PART_WEAKEN1_LEMMA = prove(
  ``ARM_PROG P cs C (Q * Q') Z ==> !Q''. SEP_IMP Q' Q'' ==> ARM_PROG P cs C (Q * Q'') Z``,
  METIS_TAC [ARM_PROG_WEAKEN_POST1,SEP_IMP_FRAME,STAR_SYM]);

val WEAKEN_LEMMA = 
  (DISCH_ALL o Q.GEN `Q''` o UNDISCH o SPEC_ALL o 
   RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_SYM]) ARM_PROG_WEAKEN_POST;

val PART_WEAKEN_LEMMA = prove(
  ``ARM_PROG P cs C Q1 ((Q * Q',f) INSERT Z) ==> 
    !Q''. SEP_IMP Q' Q'' ==> ARM_PROG P cs C Q1 ((Q * Q'',f) INSERT Z)``,
  METIS_TAC [ARM_PROG_WEAKEN_POST,SEP_IMP_FRAME,STAR_SYM]);

fun APP_X_TERM lemma th t = (fst o dest_imp o concl o Q.SPEC t o MATCH_MP lemma) th;
val APP_STRENGTHEN_TERM = APP_X_TERM STRENGTHEN_LEMMA;
val APP_PART_STRENGTHEN_TERM = APP_X_TERM PART_STRENGTHEN_LEMMA;
val APP_WEAKEN1_TERM = APP_X_TERM WEAKEN1_LEMMA;
val APP_PART_WEAKEN1_TERM = APP_X_TERM PART_WEAKEN1_LEMMA;
val APP_WEAKEN_TERM = APP_X_TERM WEAKEN_LEMMA;
val APP_PART_WEAKEN_TERM = APP_X_TERM PART_WEAKEN_LEMMA;

fun APP_X lemma th t tac = let
  val th' = prove(APP_X_TERM lemma th t, tac)
  in MATCH_MP (Q.SPEC t (MATCH_MP lemma th)) th' end;
val APP_STRENGTHEN = APP_X STRENGTHEN_LEMMA;
val APP_PART_STRENGTHEN = APP_X PART_STRENGTHEN_LEMMA;
val APP_WEAKEN1 = APP_X WEAKEN1_LEMMA;
val APP_PART_WEAKEN1 = APP_X PART_WEAKEN1_LEMMA;
val APP_WEAKEN = APP_X WEAKEN_LEMMA;
val APP_PART_WEAKEN = APP_X PART_WEAKEN_LEMMA;

fun SPEC_STRENGTHEN th tm = Q.SPEC tm (MATCH_MP STRENGTHEN_LEMMA th);
fun SPEC_WEAKEN1 th tm = Q.SPEC tm (MATCH_MP WEAKEN1_LEMMA th);
fun SPEC_WEAKEN th tm = Q.SPEC tm (MATCH_MP WEAKEN_LEMMA th);
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

(* others *)

fun FORCE_PBETA_CONV tm = let
  val (tm1,tm2) = dest_comb tm
  val vs = fst (pairSyntax.dest_pabs tm1)
  fun expand_pair_conv tm = ISPEC tm (GSYM PAIR)
  fun get_conv vs = let
    val (x,y) = dest_pair vs
    in expand_pair_conv THENC (RAND_CONV (get_conv y)) end 
    handle e => ALL_CONV
  in (RAND_CONV (get_conv vs) THENC PairRules.PBETA_CONV) tm end;

fun COMPILER_FORMAT_DEF th = 
  CONV_RULE (REWRITE_CONV [LET_DEF] THENC DEPTH_CONV (FORCE_PBETA_CONV)) th;

fun PAT_DISCH pat th = let 
  val tm = hd (filter (can (match_term pat)) (hyp th))
  in DISCH tm th end;

fun PAIR_GEN name vs th = let 
  val ctxt = free_varsl(concl th::hyp th)
  val x = Parse.parse_in_context ctxt vs
  in pairTools.PGEN (mk_var(name,type_of x)) x th end;

fun QGENL [] th = th | 
    QGENL (x::xs) th = Q.GEN x (QGENL xs th);

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

fun list_dest_forall tm = let
  val (v,x) = dest_forall tm 
  val (vs,x) = list_dest_forall x
  in (v::vs,x) end handle e => ([],tm);

fun extract_assum th = let
  val tm = (repeat (snd o dest_forall) o fst o dest_imp o concl) th
  val th = (SPEC_ALL o ASSUME o fst o dest_imp) tm
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
        end 
  end handle e => raise term_pp_types.UserPP_Failed;

fun pp_enc() = Parse.temp_add_user_printer ({Tyop = "cart", Thy = "fcp"}, print_enc_inst);
val _ = pp_enc();


(* ============================================================================= *)
(* EXPERIMENTAL PROOF-PRODUCING FUNCTIONS                                        *)
(* ============================================================================= *)

(* handleing terms *)

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
  in "[" ^ list_to_string f xs "," ^ "]" end;

fun subst_to_string_no_types xs indent =
  let fun f {redex = x, residue = y} = 
      "`" ^ term_to_string x ^ "`|->`" ^ term_to_string y ^ "`"
  in "[" ^ remove_new_lines (list_to_string f xs ",") ^ "]" end;

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

val inst_str = "add r1,a,b,lsr #2"
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
  val th = SIMP_RULE (bool_ss ++ armINST2_ss) [] th
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
  val str = "SIMP_RULE (bool_ss++armINST2_ss) ["^s^"] (Q.INST "^ 
             subst_to_string_no_types i "  " ^ " " ^ name ^ ")"
  in (th,str) end;

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

(*
make_spec ["mov r0,r0","mov r0,r0"]

  val th1 = (*  mov r0,r0  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`0w`,`a_mode`|->`OneReg`,`x`|->`x1` ] arm_MOV1))
  val th2 = (*  mov r0,r0  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`0w`,`a_mode`|->`OneReg`,`x`|->`x2` ] arm_MOV1))
  val th1 = AUTO_HIDE_STATUS th1  

  val th1 = (*  ldr r1,[sp]  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`1w`,`b`|->`13w`,`imm`|->`0w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th2 = (*  ldr r1,[sp]  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`1w`,`b`|->`13w`,`imm`|->`0w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))
  val th1 = ALIGN_VARS ["y1"] th1  
  val th1 = AUTO_HIDE_STATUS th1  
  val th2 = ALIGN_VARS ["y2"] th2  

  val th1 = (*  add r1,r2,r3  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`c`|->`1w`,`a`|->`2w`,`b`|->`3w`,`a_mode`|->`OneReg`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_ADD3))
  val th2 = (*  ldr r1,[sp]   *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`1w`,`b`|->`13w`,`imm`|->`0w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))
  val th1 = AUTO_HIDE_POST1 [`R 1w`] th1
  val th2 = ALIGN_VARS ["y2"] th2
  val th2 = APP_FRAME `~R 2w` th2
  val name1 = "th1"
  val name2 = "th2"
*)

fun find_composition1 (th1,name1) (th2,name2) = let
  val (_,_,_,Q,_) = dest_ARM_PROG (concl th1)
  val (P,_,_,_,_) = dest_ARM_PROG (concl th2)
  fun number i [] = [] | number i (x::xs) = (x,i) :: number (i+1) xs
  val xs = (number 1 o list_dest_STAR) Q
  val ys = (number 1 o list_dest_STAR) P
  fun can_match x y = get_sep_domain x = get_sep_domain y handle e => x = y
  fun m x y = can_match y x
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
  val th = MOVE_COMPOSE2 th1 th2 xs1 xs2 ys1 ys2
  val str = "MOVE_COMPOSE2 "^ name1 ^" "^ name2 ^" `"^ 
            xs_str1 ^"` `"^ xs_str2 ^"` `"^ ys_str1 ^"` `"^ ys_str2 ^"`"
  in (th,str) end;

fun find_composition2 (th1,name1) (th2,name2) = let
  val (_,_,_,Q,_) = dest_ARM_PROG (concl th1)
  val (P,_,_,_,_) = dest_ARM_PROG (concl th2)
  fun f tm = (get_sep_domain tm,is_SEP_HIDE (fst (dest_comb tm))) handle e => (tm,false)
  val xs = (map f o list_dest_STAR) Q
  val ys = (map f o list_dest_STAR) P
  fun f ((d:term,false),(zs,qs)) = (zs,qs)
    | f ((d,true),(zs,qs)) = (zs,filter (fn x => d = x) zs @ qs)
  val f_xs = map fst (filter (not o snd) xs)
  val f_ys = map fst (filter (not o snd) ys)
  val hide_from_post = snd (foldr f (f_xs,[]) ys) 
  val hide_from_preS = snd (foldr f (f_ys,[]) xs) 
  val hide_from_pre = filter (fn tm => not ((fst o dest_const) tm = "S") handle e => true) hide_from_preS
  val hide_pre_status = length hide_from_pre < length hide_from_preS
  val th1 = AUTO_HIDE_POST1_TERM hide_from_post th1
  val th2 = AUTO_HIDE_PRE_TERM hide_from_pre th2
  fun to_str tm = "`" ^ term_to_string tm ^ "`"
  val name1 = if length hide_from_post = 0 then name1
    else "(AUTO_HIDE_POST1 ["^ list_to_string to_str hide_from_post "," ^"] "^name1^")"
  val name2 = if length hide_from_pre = 0 then name2
    else "(AUTO_HIDE_PRE ["^ list_to_string to_str hide_from_pre "," ^"] "^name2^")"
  in if not hide_pre_status then 
    find_composition1 (th1,name1) (th2,name2) 
  else let
    val (th2,name2) =  
          ((AUTO_PRE_HIDE_STATUS th2,"(AUTO_PRE_HIDE_STATUS "^name2^")") handle e => 
           (AUTO_HIDE_STATUS th2,"(AUTO_HIDE_STATUS "^name2^")"))
  in find_composition1 (th1,name1) (th2,name2) end end;

fun get_address_vars tm = let
  val x = Parse.parse_in_context [] `M x`
  val y = Parse.parse_in_context [] `M30 x`
  val tm = find_term (can (match_term x)) tm handle e =>
           find_term (can (match_term y)) tm
  fun list_dest_var tm = if is_var tm then [tm] else let 
    val (x,y) = dest_comb tm 
    val xs = list_dest_var x 
    val ys = list_dest_var y 
    in xs @ ys end handle e => [];
  in list_dest_var tm end handle e => [];

fun find_composition3 (th1,name1) (th2,name2) = let
  val (_,_,_,Q,_) = dest_ARM_PROG (concl th1)
  val (P,_,_,_,_) = dest_ARM_PROG (concl th2)
  val xs = (list_dest_STAR) Q
  val ys = (list_dest_STAR) P
  val vars = map get_address_vars ys
  val vars = foldr (uncurry append) [] vars
  fun g f list tm = mem (f (dest_comb tm)) list handle e => false
  val address_holders = filter (g snd vars) ys  
  fun f tm = let
    val (x,y1) = dest_comb tm
    val y2 = snd (dest_comb (hd (filter (g fst [x]) xs)))
    in [y1|->y2] end handle e => []
  val ss = foldr (uncurry append) [] (map f address_holders) 
  val th2 = INST ss th2
  val str = subst_to_string_no_types ss "  "
  val name2 = if length ss = 0 then name2
              else "(Q.INST "^str^" "^name2^")"
  in find_composition2 (th1,name1) (th2,name2) end;

fun find_composition4 (th1,name1) (th2,name2) = let
  val th = FALSE_COMPOSE th1 th2  
  val str = "FALSE_COMPOSE "^name1^" "^name2
  in (th,str) end 
  handle e => find_composition3 (th1,name1) (th2,name2);

fun find_composition5 (th1,name1) (th2,name2) = let
  val (th,str) = find_composition4 (th1,name1) (th2,name2)
  in let 
    val th = ABSORB_POST th           
    val th = if is_imp (concl th) then hd [] else th
    val str = "ABSORB_POST ("^str^")" 
    in (th,str) end handle e => (th,str) end 
  handle e => let 
    val _ = print ("\n\n\nUnable to compose: \n\n" ^ 
              thm_to_string th1 ^ "\n\n\n" ^
              thm_to_string th2 ^ "\n\n\n") 
  in raise e end;

val find_composition = find_composition5;

fun get_unaligned tm = let
  val x = Parse.parse_in_context (free_vars tm) `M (addr30 x)`
  val tm = find_term (can (match_term x)) tm
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

fun old_find_composition (th1,name1) (th2,name2) name indent = let
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
      val (th,s) = old_find_composition (th1,name1) (th2,name2) name indent 
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



(* ============================================================================= *)
(* NEW EXPERIMENTAL PROOF-PRODUCING FUNCTIONS                                    *)
(* ============================================================================= *)

(* user changeable flags *)
val optimise_code = ref true;
val abbrev_code = ref false;

(* list of compiled code (name,th,is_proc,code length,code definition) *)
val compiled_specs = ref ([]:(string * thm * bool * int * thm) list);

(* internal rewrite lists *)
val code_abbreviations = ref ([]:thm list);


fun add_code_abbrev code_def = let
  val tm = mk_comb(``LENGTH:word32 list -> num``,(fst o dest_eq o concl o SPEC_ALL) code_def)
  val cc = code_length_conv()
  val length_thm = (SIMP_CONV arith_ss [code_def,LENGTH,LENGTH_APPEND] THENC cc) tm
  val _ = code_length_rewrites := length_thm :: (!code_length_rewrites)
  val _ = code_abbreviations := code_def :: (!code_abbreviations)
  in () end;


fun transpose [] = [] | transpose (x::xs) = let
  val xs = rev (x::xs)  
  fun t [] ys = ys | t (x::xs) ys = t xs (map (uncurry cons) (zip x ys))
  in t (tl xs) (map (fn x => [x]) (hd xs)) end;

(*
val thms = (zip xs p)

val [(name1,th1),(name2,th2),(name3,th3)] = xs
val (th1,name1) = find_composition3 (th1,name1) (th2,name2)
val (th2,name2) = (th3,name3)
  find_composition3 (th1,name1) (th2,name2)
*)  

fun mk_compose_pass thms name = let
  fun h ((name,th),0) = (("SND_PROG2 "^name, SND_PROG2 th) handle e => (name,th))
    | h ((name,th),n) = (("FST_PROG2 "^name, FST_PROG2 th) handle e => (name,th))   
  val xs = map h thms
  fun find_compositions prev_name prev_th [] = ([],prev_th) 
    | find_compositions prev_name prev_th ((curr_name,curr_th)::xs) = let
      val (th,s) = find_composition (prev_th,prev_name) (curr_th,"("^curr_name^")")
      val s = "  val "^name^" = "^s^"\n"
      val (ys,th) = find_compositions name th xs
      in (s::ys,th) end
  val (prev_name,prev_th) = hd xs
  val (strs,th) = find_compositions ("("^prev_name^")") prev_th (tl xs)
  val th = AUTO_HIDE_STATUS th
  val strs = strs @ ["  val "^name^" = AUTO_HIDE_STATUS "^name^"\n"]
  in (strs,th) end;

fun make_passes_th code = let
  fun f (s,(ys,n)) = 
    if (substring(s,0,6) = "proc: ") handle e => false then let
      val i = int_to_string n
      val name = substring(s,6,size(s)-6)
      val name = replace_char #" " "" name
      fun match_name (n,_,_,_,_) = n = name 
      val (_,th,is_proc,_,_) = hd (filter match_name (!compiled_specs))
      val th = if is_proc then SIMP_RULE (std_ss++setINC_ss) [] (MATCH_MP arm_BL th) else th
      val str = if is_proc then "SIMP_RULE (std_ss++setINC_ss) [] (MATCH_MP arm_BL "^name^"_arm)" else name^"_arm"
      in ((ys @ [(s,"th"^i,str,th)]),n+1) end
    else let
      val i = int_to_string n
      val (th,str) = mk_arm_prog2_str s i
      val (th,str2) = align_addresses th 
      val str = if str2 = "" then str else str2 ^ "(" ^ str ^ ")" 
      in ((ys @ [(s,"th"^i,str,th)]),n+1) end
  val xs = pad_strings (map fst code)
  val xs = fst (foldl f ([],1) xs)  
  val paths = transpose (map snd code)
  fun to_str (s,i,str,th) = let
    val i = if size(i) < 4 then i ^ " " else i
    in "  val "^i^" = ("^"*  "^s^"  *"^") "^str^"\n" end
  val strs = map to_str xs  
  val xs = map (fn (s,name,str,th) => (name,th)) xs
  fun f (p,(i,ys,strs,pnames)) = let
    val pname = "p"^int_to_string i
    val (strs2,th) = mk_compose_pass (zip xs p) pname
    in (i+1,ys @ [th],strs @ strs2,pnames @ [pname]) end;
  val (_,th,strs,pnames) = foldl f (1,[],strs,[]) paths
  val th = zip pnames th
  val pnames = foldr (fn (x,y) => x^","^y) (last pnames) (butlast pnames)
  in (th,strs) end;

(*
  val (i,ys,strs,pnames) = (1,[],strs,[])
  val p = hd paths
*)

fun make_passes code = 
  print (foldr (uncurry concat) "" (["\n\n\n"] @ snd (make_passes_th code) @ ["\n\n\n"]));

(*
 val code = [
("add r1,r2,r3",[1,1,1,1]),
("teq r1,#0   ",[1,1,1,1]),
("beq 12      ",[1,1,0,0]),
("sub r1,r1,r3",[0,0,1,1]),
("mul r2,r3,r2",[0,0,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("mov r3,r1   ",[1,1,1,1]),
("tst r2,r1   ",[1,1,1,1]),
("bne -44   "  ,[0,1,0,1])]
*)

(* generate ARM code *)

fun string_remove_primes str = replace_char #"'" "" str;
val num_to_string = int_to_string o Arbint.toInt o Arbint.fromNat

fun code_length xs = let
  fun is_proc s = ((substring(s,0,6) = "proc: ") handle e => false)
  val (xs,procs) = (filter (not o is_proc) xs, filter is_proc xs)
  fun f st = hd (filter (fn (n,_,_,_,_) => n = substring(st,6,size(st)-6)) (!compiled_specs))
  val procs = map ((fn (n,th,p,l,_) => (p,l)) o f) procs
  fun f ((true,i),sum) = sum+1 | f ((false,i),sum) = sum + i
  in length xs + foldr f 0 procs end;

fun dest_reg_var x = let
  val name = (string_remove_primes o fst o dest_var) x
  in if substring(name,0,1) = "r" then name else hd [] end;

fun dest_mem_var x = let
  val y = (string_remove_primes o fst o dest_var) x
  fun f s = int_to_string (string_to_int (substring(s,1,size(s)-1)) * 4)
  val v = substring(y,0,1)
  in if v = "m" then f y else if v = "n" then "-"^f y else hd [] end;

fun dest_reg_var_or_const x = dest_reg_var x handle e => let
  val (x,y) = dest_comb x
  val _ = if fst (dest_const x) = "n2w" then x else hd []
  in ("#" ^ (num_to_string o numSyntax.dest_numeral) y) end;

fun dest_addr_mode1 x = dest_reg_var_or_const x handle e => let
  val (x,rhs) = dest_comb x
  val (x,lhs) = dest_comb x
  val x = fst (dest_const x)
  val lhs = dest_reg_var_or_const lhs
  val rhs = (num_to_string o numSyntax.dest_numeral) rhs
  fun g "word_lsl" = lhs^", lsl #"^rhs
    | g "word_lsr" = lhs^", lsr #"^rhs
    | g "word_asr" = lhs^", asr #"^rhs
    | g _ = hd []
  in g x end;

fun make_branch_code_main exp = let 
  (* normal binary test *)
  val (exp,rhs) = dest_comb exp
  val (exp,lhs) = dest_comb exp
  val exp = fst (dest_const exp)
  fun comma lhs rhs = " "^lhs^", "^rhs
  fun g "=" lhs rhs       = (["cmp" ^ comma lhs rhs],"eq","ne")
    | g "word_lt" lhs rhs = (["cmp" ^ comma lhs rhs],"lt","ge")
    | g "word_le" lhs rhs = (["cmp" ^ comma lhs rhs],"le","gt")
    | g "word_ls" lhs rhs = (["cmp" ^ comma lhs rhs],"ls","hi")
    | g "word_lo" lhs rhs = (["cmp" ^ comma lhs rhs],"cc","cs") 
    | g _ _ _ = (["error"],"","")
  val (xs,cond,not_cond) = g exp (dest_reg_var lhs) (dest_addr_mode1 rhs)
  in (xs,cond,not_cond) end handle e => let
  (* case of r1 && r2 = 0w *)
  val ss = match_term (Parse.parse_in_context [] `r1 && r2:word32 = 0w`) exp
  val exp = (snd o dest_comb o fst o dest_comb) exp
  val (exp,rhs) = dest_comb exp
  val (exp,lhs) = dest_comb exp
  val x = dest_reg_var lhs
  val y = dest_addr_mode1 rhs
  in (["cmp "^x^", "^y,"tst "^x^", "^y],"eq","ne") end
  (* others failed, try if the expression was negated *) 
  handle e => let
  val (xs,cond,not_cond) = make_branch_code_main (dest_neg exp) 
  in (xs,not_cond,cond) end;

fun word_cmp_normalise_term tm = let
  val th = REWRITE_CONV [WORD_CMP_NORMALISE] tm
  val tm = (snd o dest_eq o concl) th    
  in tm end handle e => tm;

fun make_branch_code exp = 
  make_branch_code_main (word_cmp_normalise_term exp) 
  handle e => let 
  val tm = word_cmp_normalise_term (mk_neg(exp))
  val (xs,not_cond,cond) = make_branch_code_main tm
  in (xs,cond,not_cond) end;

fun find_assignment_code var exp = 
  let (* binary operators *)
  val (exp,rhs) = dest_comb exp
  val (exp,lhs) = dest_comb exp
  val exp = fst (dest_const exp)
  fun comma var lhs rhs = " "^var^", "^lhs^", "^rhs
  fun g "word_add" var lhs rhs = ["add%" ^ comma var lhs rhs]
    | g "word_sub" var lhs rhs = ["sub%" ^ comma var lhs rhs]
    | g "word_mul" var lhs rhs = ["mul%" ^ comma var lhs rhs]
    | g "word_and" var lhs rhs = ["and%" ^ comma var lhs rhs]
    | g "word_or"  var lhs rhs = ["orr%" ^ comma var lhs rhs]
    | g "word_xor" var lhs rhs = ["eor%" ^ comma var lhs rhs]
    | g _ _ _ _ = ["error"] 
  val var = (string_remove_primes o fst o dest_var) var
  in g exp var (dest_reg_var lhs) (dest_addr_mode1 rhs) end 
  handle e => let (* code for mvn - move negative *) 
  val (not,exp) = dest_comb exp
  val _ = if fst (dest_const not) = "word_1comp" then not else hd []
  val var = dest_reg_var var
  in ["mvn% "^var^", "^dest_addr_mode1 exp] end 
  handle e => let (* code for mov - move *)
  val var = dest_reg_var var
  in ["mov% "^var^", "^dest_addr_mode1 exp] end 
  handle e => (* code for ldr - load register *)
    ["ldr% "^dest_reg_var var^", [sp,#"^dest_mem_var exp^"]"]
  handle e => (* code for str - store register *)
    ["str% "^dest_reg_var exp^", [sp,#"^dest_mem_var var^"]"]
  handle e => let (* code for procedure call *)
    val name = fst (dest_const (fst (dest_comb exp) handle e => exp))       
    in ["proc: "^name] end;

fun pull_out_shared_front xs ys = let
  fun share x y = (x = y) andalso not (replace_char #"%" "" (fst x) = fst x)
  fun add (x,x1) (y,y1) = (x,x1 @ y1) 
  fun f [] [] (xs',ys',zs') = (xs',ys',zs')
    | f (x::xs) [] (xs',ys',zs') = (xs' @ (x::xs),ys',zs')
    | f [] (y::ys) (xs',ys',zs') = (xs',ys' @ (y::ys),zs')
    | f (x::xs) (y::ys) (xs',ys',zs') = 
       if share x y then f xs ys (xs',ys',zs' @ [add x y]) 
       else (xs' @ (x::xs),ys' @ (y::ys),zs')
  in f xs ys ([],[],[]) end;

fun pull_out_shared_tail xs ys = let
  fun share (x,_) (y,_) =
    replace_char #"%" "" x = replace_char #"%" "" y 
  fun add (x,x1) (y,y1) = (x,x1 @ y1)
  fun f [] [] (xs',ys',zs') = (xs',ys',zs')
    | f (x::xs) [] (xs',ys',zs') = (rev (x::xs) @ xs',ys',zs')
    | f [] (y::ys) (xs',ys',zs') = (xs',rev (y::ys) @ ys',zs')
    | f (x::xs) (y::ys) (xs',ys',zs') = 
       if share x y then f xs ys (xs',ys',add x y::zs') 
       else (rev (x::xs) @ xs',rev (y::ys) @ ys',zs')
  in f (rev xs) (rev ys) ([],[],[]) end;

fun first_n 0 xs = [] | first_n n xs = hd xs :: first_n (n-1) (tl xs);
fun repeat_n 0 x = [] | repeat_n n x = x :: repeat_n (n-1) x;
fun is_bottom st = substring(st,0,8) = "$bottom$" handle e => false;
fun is_top st = substring(st,0,5) = "$top$" handle e => false;

fun make_block_conditional xs cond = let
  val _ = if length xs < 6 then true else hd []
  fun f (cmd,trace) = let
    val cmd' = replace_char #"%" cond cmd 
    in if cmd = cmd' then hd [] else (cmd',trace) end
  in (true,map f xs) end 
  handle e => (false,map (fn (cmd,t) => (replace_char #"%" "" cmd,t)) xs);

(* intial phase: choose instructions *)
fun make_inst_list1 tm = 
  let (* case: if-then-else *)
  val (g,tm1,tm2) = dest_cond tm
  val (xs,xst) = make_inst_list1 tm1
  val (ys,yst) = make_inst_list1 tm2
  val (test,cond,not_cond) = make_branch_code g
  in if not (!optimise_code) then let 
    val j_xs = ["b" ^ not_cond ^ " " ^  int_to_string (4 * (code_length xs + 1))]
    val test_trace = map (fn x => 1) test
    val xs0 = map (fn x => 0) xs
    val ys0 = map (fn x => 0) ys
    val xst = map (fn t => test_trace @ [0] @ t @ ys0) xst 
    val yst = map (fn t => test_trace @ [1] @ xs0 @ t) yst
    val code = map (replace_char #"%" "") (test @ j_xs @ xs @ ys)
    in (code,xst @ yst) end 
  else let (* optimise if-then-else *)
    val xsl = length xst
    val ysl = length yst
    val xs_zero = repeat_n xsl 0
    val xs_one = repeat_n xsl 1
    val ys_zero = repeat_n ysl 0
    val ys_one = repeat_n ysl 1
    (* zip together traces with code *)
    val xs = zip xs (transpose xst)
    val ys = zip ys (transpose yst)
    (* extract shared tails *)
    val (xs1,ys1,zs1) = pull_out_shared_tail xs ys
    val (xs1,ys1,zs2) = pull_out_shared_front xs1 ys1
    (* bug fix: if xs and ys are both empty then won't be able to 
                find the this branch, hence don't optimise in that case *)
    val (xs,ys,zs1,zs2) = if length xs1 = 0 andalso length ys1 = 0 
                          then ([hd xs],[hd ys],(tl zs1 handle e => []),(tl zs2 handle e => []))
                          else (xs1,ys1,zs1,zs2) 
    (* fix traces *)
    val xs  = map (fn (cmd,t) => (cmd,t @ ys_zero)) xs
    val ys  = map (fn (cmd,t) => (cmd,xs_zero @ t)) ys
    (* make each instruction conditional *)
    val (xs_c,xs) = make_block_conditional xs cond
    val (ys_c,ys) = make_block_conditional ys not_cond
    (* add traces for jumps *)
    val jump_over_xs_trace = xs_zero @ ys_one
    val jump_over_ys_trace = xs_one @ ys_zero
    val xs = (xs_c,(xs,(jump_over_xs_trace,cond)))
    val ys = (ys_c,(ys,(jump_over_ys_trace,not_cond)))
    (* switch the order of xs and ys in case xs will bottom out *)
    val (xs,ys) = if length(fst(snd(xs))) = 0 then (xs,ys) else 
                  (if is_bottom(fst(last(fst(snd(xs))))) then (ys,xs) else (xs,ys))
    (* switch the order of xs and ys in case ys can be made conditional but xs cannot *)
    val (xs,ys) = if not (fst xs) andalso fst ys then (ys,xs) else (xs,ys)
    (* generate jump over ys *)
    val jump_over_ys = 
      if fst ys then [] else let
        val jump_length = 4 * (code_length (map fst (fst(snd(ys)))) + 1)
        val jump_inst = "b% " ^ int_to_string jump_length
        val jump_inst = replace_char #"%" (if fst xs then snd(snd(snd(xs))) else "") jump_inst
        val jump_over_trace = fst(snd(snd(ys)))
        in [(jump_inst,jump_over_trace)] end 
    (* erase jump over ys in case xs ends in $bottom or $top *)
    val jump_over_ys = let
      val last_xs_inst = fst(last(fst(snd(xs)))) 
      in if is_bottom last_xs_inst orelse is_top last_xs_inst 
         then [] else jump_over_ys end handle e => jump_over_ys
    (* generate jump over xs *)
    val jump_over_xs = 
      if fst xs then [] else let
        val jump_length = 4 * (code_length (map fst (fst(snd(xs)))) + 1 + length jump_over_ys)
        val jump_inst = "b"^snd(snd(snd(ys)))^" " ^ int_to_string jump_length
        val jump_over_trace = fst(snd(snd(xs)))
        in [(jump_inst,jump_over_trace)] end
    (* separate code and traces *)
    val xs = jump_over_xs @ fst(snd(xs))
    val ys = jump_over_ys @ fst(snd(ys))
    val test = map (fn cmd => (cmd, xs_one @ ys_one)) test
    val qs = test @ zs2 @ xs @ ys @ zs1
    val code = map (replace_char #"%" "" o fst) qs
    val traces = transpose (map snd qs)
    in (code, traces) end end
  handle e => 
  let (* case: let *)
  val (xs,tail) = pairSyntax.dest_anylet tm  
  val (var,exp) = hd xs
  val xs = find_assignment_code var exp
  val t1 = map (fn x => 1) xs
  val (ys,ts) = make_inst_list1 tail
  in (xs @ ys,map (fn t => t1 @ t) ts) end handle e => 
  let (* case: return *)
  val xs = dest_var tm handle e => (dest_var o fst o dest_pair) tm
  in (["$bottom$%"],[[1]]) end handle e =>
  let (* case: rec call *)
  val _ = dest_comb tm
  in (["$top$%"],[[1]]) end handle e => (["error"],[[1]]);

(* second phase: make branches concrete *)
fun make_inst_list2 def = let
  val tm = (snd o dest_eq o concl o SPEC_ALL) def
  val (xs,t) = make_inst_list1 tm
  val xs = map (replace_char #"%" "") xs
  val (xs,t) = if is_bottom(last xs) then (butlast xs,map butlast t) else (xs,t)
  val l = 4 * code_length xs
  fun set_top_bottom (cmd,(xs,i)) =
    let val j = code_length [cmd] * 4 in
    if is_top(cmd) then
      (xs @ ["b"^substring(cmd,5,size(cmd) - 5)^" -"^int_to_string (i-4)],i+j)
    else if is_bottom(cmd) then
      (xs @ ["b"^substring(cmd,8,size(cmd) - 8)^" "^int_to_string (l-i+4)],i+j)
    else 
      (xs @ [cmd],i+j) end
  val xs = fst (foldl set_top_bottom ([],4) xs) 
  val t = transpose t
  in zip xs t end;


(* build spec *)

fun mk_substs_string [] name = []
  | mk_substs_string (x::xs) name = 
      ["  val "^name^" = Q.INST [" ^ foldl (fn (x,y) => x ^ "," ^ y) x xs ^ "] "^name^"\n"];

fun standardise_names name terms th = let
  (* rename variables, e.g. R 1w y3 --> R 1w r1 *)
  fun find_subst tm = let
    val (x,z) = dest_comb tm
    val z_str = fst (dest_var z)
    val (x,y) = dest_comb x 
    val n2w_to_string = num_to_string o numSyntax.dest_numeral o snd o dest_comb
    in if fst (dest_const x) = "R" then let
      val i = n2w_to_string y
      val var = mk_var("r"^i,type_of z)
      val subst = z |-> var
      val subst_str = "`"^ z_str ^"`|->`r"^i^"`"  
      in ([subst],[subst_str]) end 
    else if fst (dest_const x) = "R30" andalso y = ``13w:word4`` then 
         ([z|->``sp:word30``],["`"^ z_str ^"`|->`sp`"])
    else let
      val i = (snd o dest_comb) y handle e => ``0w:word30``
      val i = n2w_to_string i 
      val var_str = 
           if i = "0" then "m" else
           if (fst o dest_const o fst o dest_comb o fst o dest_comb) y = "word_add" 
           then "m" else "n" handle e => "m"
      val var = mk_var(var_str^i,type_of z)
      val subst = z |-> var
      val subst_str = "`"^ z_str ^"`|->`"^var_str^i^"`"  
      in ([subst],[subst_str]) end handle e => ([],[]) end
  fun renamer (tm,(th,xs,zs)) = let
      val (y,z) = find_subst tm handle e => ([],[])
      val tm = Term.subst y tm      
      val th = INST y th
      in (th, tm :: xs, z @ zs) end
  val (th,terms,substs) = foldr renamer (th,[],[]) terms
  val strs = mk_substs_string substs name
  in (th,strs) end;

fun dest_tuple tm = 
  let val (x,y) = dest_pair tm in x :: dest_tuple y end handle e => [tm];

fun get_input_list def = 
  let val tm = (fst o dest_eq o concl o SPEC_ALL) def in 
    map (fst o dest_var) ((dest_tuple o snd o dest_comb) tm) end handle e => [];
  
fun get_output_list def = let
  val tm = (snd o dest_eq o concl o SPEC_ALL) def
  fun ground_terms tm =
    let (* case: if-then-else *)
    val (_,x,y) = dest_cond tm
    in ground_terms x @ ground_terms y end handle e => 
    let (* case: let *)
    val tm = (snd o pairSyntax.dest_anylet) tm
    in ground_terms tm end handle e =>
    let (* case: return, single variable *)
    in [[fst (dest_var tm)]] end handle e =>
    let (* case: return, tuple of variables *)
    val (x,y) = dest_pair tm
    in [map (fst o dest_var) (x :: dest_tuple y)] end handle e => [];
  val gt = ground_terms tm
  val (x,xs) = (hd gt,tl gt)
  val rest = filter (fn y => not (x = y)) xs
  in if length(rest) > 0 then raise ERR "get_output_list" "Incompatible outputs." else x end;
  
(* takes e.g. ``R 1w`` produces "r1", and ``M (sp + 1w)`` produces "m1" *)
fun term_to_name tm = let
  val (x,y) = dest_comb tm  
  val f = num_to_string o numSyntax.dest_numeral o snd o dest_comb
  val i = f y handle e => (f o snd o dest_comb) y handle e => "0"         
  val x = if fst (dest_const x) = "R" then "r"^i else
          if fst (dest_const x) = "R30" andalso i = "13" then "sp" else 
          if fst (dest_const x) = "M" then "m"^i else "n"^i 
  in x end handle e => term_to_string tm;  

(* attempts to do the opposite of term_to_name *)
fun name_to_string_of_term name =
  if name = "sp" then "R30 13w" else
  if substring(name,0,1) = "r" then "R "^substring(name,1,size(name)-1)^"w" else
  if substring(name,0,1) = "m" then "M (sp + "^substring(name,1,size(name)-1)^"w)" else
  hd [];
  
fun name_to_term result_type name = 
  Parse.Term [QUOTE (name_to_string_of_term name ^ " " ^ name ^ type_to_string result_type)];

fun rename_and_fill_preconditions thms def = let
  (* extract preconditions *)
  fun is_SEP_cond tm = let
    val {Name = n, Thy = t, Ty = _} = (dest_thy_const o fst o dest_comb) tm
    in if t = "set_sep" andalso n = "cond" then true else false end handle e => false;   
  fun extract_pre_lists (name,th) = let
    val (p,_,_,_,_) = dest_ARM_PROG (concl th)
    val p = filter (not o is_SEP_cond) (list_dest_STAR p)
    in (name,p,th) end
  val thms = map extract_pre_lists thms
  (* standardise names *)
  fun f (name,pres,th) = let
    val (th,strs) = standardise_names name pres th
    val (p,_,_,_,_) = dest_ARM_PROG (concl th)
    val pres = filter (not o is_SEP_cond) (list_dest_STAR p)
    in (name,pres,th,strs) end;
  val thms = map f thms
  (* make a list of all elements that occur in a precondition *)    
  fun merge [] (ys,zs) = (ys,zs)
    | merge (x::xs) (ys,zs) = let
       val y = get_sep_domain x
       in if mem y ys then merge xs (ys,zs) else merge xs (y::ys,x::zs) end
  fun merge_pres ((name,pres,th,strs),result) = merge pres result
  val pre_elements = snd (foldl merge_pres ([],[]) thms)
  (* if no precondition mentions an element that is required then add it in *)
  val term_type = type_of (hd pre_elements)
  val in_list = get_input_list def
  val pre_names = map (term_to_name o get_sep_domain) pre_elements
  fun g x = not (mem x pre_names)
  val extras = map (name_to_term term_type) (filter g in_list)
  val pre_elements = pre_elements @ extras
  (* insert missing elements into specs *)
  fun delete xs ys = let
    val zs = map get_sep_domain ys
    in filter (fn x => not (mem (get_sep_domain x) zs)) xs end
  fun f (name,pres,th,strs) = let    
    val new = delete pre_elements pres
    val pres = pres @ new 
    in if new = [] then (name,pres,th,strs) else let
    val frame = list_mk_STAR new
    val th = RW [STAR_ASSOC] (SPEC frame (APP_BASIC_FRAME th))     
    val str = ["  val "^name^" = RW [STAR_ASSOC] (APP_FRAME `"^term_to_string frame^"` "^name^")\n"]
    in (name,pres,th,strs @ str) end end
  val thms = map f thms
  in thms end;

fun hide_pre_post_elements thms def = let
  val in_list = get_input_list def @ ["sp"]
  val out_list = get_output_list def @ ["sp"]
  (* mark which theorems exit the loop, pick out post *)
  fun f (name,pres,th,strs) = let
    val (_,_,_,q,qs) = dest_ARM_PROG (concl th)
    val g = fst (dest_const q) = "SEP_F" handle e => false
    val q = if g then (fst o dest_pair o snd o dest_comb o fst o dest_comb) qs else q
    in (name,pres,list_dest_STAR q,g,th,strs) end
  val thms = map f thms
  (* hide posts and pres *)
  fun get_hide_list xs names name func_name = let
    fun h tm = (not o is_SEP_HIDE o fst o dest_comb) tm handle e => true
    val xs = filter h xs
    fun h tm = not (mem ((term_to_name o fst o dest_comb) tm) names) handle e => false
    fun k tm = "`" ^ term_to_string tm ^ "`"
    val xs = map (fst o dest_comb) (filter h xs) 
    val ys = map k xs
    val strs = if xs = [] then [] else ["  val "^name^" = AUTO_HIDE_"^
                 func_name^" ["^ foldl (fn (x,y) => x ^","^ y) (hd ys) (tl ys)^"] "^name^"\n"]
    in (xs,strs) end
  fun hide_pre_post (name,pres,posts,loop,th,strs) = let
    val (xs,func_name,f) = if loop then (in_list,"POST",AUTO_HIDE_POST_TERM) 
                                   else (out_list,"POST1",AUTO_HIDE_POST1_TERM)
    val (xs,str1) = get_hide_list posts xs name func_name
    val th = f xs th handle e => let
      val _ = print ("\n\n\nUnable to hide from postcondition one of the following: \n\n  "^
               list_to_string term_to_string xs "   " ^
               "\n\n\n"^thm_to_string th ^"\n\n\n") in raise e end
    val (xs,str2) = get_hide_list pres in_list name "PRE"
    val th = AUTO_HIDE_PRE_TERM xs th handle e => let
      val _ = print ("\n\n\nUnable to hide from precondition one of the following: \n\n  "^
               list_to_string term_to_string xs "   " ^
               "\n\n\n"^thm_to_string th ^"\n\n\n") in raise e end
    in (name,loop,th,strs @ str1 @ str2) end 
  val thms = map hide_pre_post thms
  in thms end;      

fun flatten_pairs tm xs = let
  val (x,y) = (dest_pair o fst o dest_eq o concl o ISPEC tm) PAIR
  in flatten_pairs y (xs @ [x]) end handle e => xs @ [tm];

fun get_pre_post_terms def_name thms def strs = let
  val (_,_,th,_) = hd (filter (fn (name,b,th,strs) => not b) thms)
  val th = RW [GSYM ARM_PROG_MOVE_COND] (DISCH ``5=4`` th)  
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val (p,_,_,q,_) = dest_ARM_PROG (concl th)
  val p = fst (dest_STAR p)
  val ps = list_dest_STAR p
  val qs = list_dest_STAR q  
  (* sort the results *)
  fun sep_to_string tm = let
    val tm = (snd o dest_eq o concl o REWRITE_CONV [R30_def,M30_def]) tm handle e => tm
    val tm = get_sep_domain tm
    val is_reg = (fst o dest_const o fst o dest_comb) tm = "R" handle e => false
    in if is_reg then let
      val x = term_to_string (snd (dest_comb tm))
      in if size(x) < 3 then "AA 0"^x else "AA "^x end 
    else term_to_string tm end
  val sorter = sort (curry (fn (tm1,tm2) => sep_to_string tm1 < sep_to_string tm2))
  val ps = sorter ps
  val qs = sorter qs
  (* substitute in the result of the def function *)
  val out = get_output_list def  
  val out' = flatten_pairs ((fst o dest_eq o concl o SPEC_ALL) def) []
  val out = zip out out'
  fun f tm = let
    val tm = fst (dest_comb tm)
    val x = term_to_name tm 
    val xs = filter (fn y => fst y = x) out
    val y = snd (hd xs) 
    in mk_comb(tm,y) end handle e => tm
  val qs = map f qs
  (* wrap it up *)
  val pre_tm = list_mk_STAR ps
  val post_tm = list_mk_STAR qs
  (* print it out *)
  val s1 = "  val pre  = `" ^ replace_char #"\n" " " (term_to_string pre_tm) ^ "`\n"
  val s2 = "  val post = `" ^ replace_char #"\n" " " (term_to_string post_tm) ^ "`\n"
  val s3 = "  val def  = COMPILER_FORMAT_DEF " ^ def_name ^ "\n"
  val strs = s1::s2::s3::strs
  in (pre_tm,post_tm,strs) end;

fun RAND_SIMP_SEP_IMP def post_tm th = let
  val th = ISPEC post_tm (MATCH_MP WEAKEN1_LEMMA th)
  val cc = RAND_CONV (ONCE_REWRITE_CONV [def])
  val cc = cc THENC SIMP_CONV std_ss [SEP_IMP_MOVE_COND,LET_DEF] 
  val cc = cc THENC RATOR_CONV (ONCE_REWRITE_CONV 
      (map GSYM [WORD_NOT_LESS,WORD_NOT_LESS_EQUAL,
                 WORD_NOT_LOWER_EQUAL,WORD_NOT_LOWER]))
  val cc = cc THENC SIMP_CONV bool_ss []
  val cc = cc THENC SIMP_CONV (std_ss++star_ss) [SEP_IMP_REFL,LET_DEF]
  val th = CONV_RULE (RATOR_CONV (RAND_CONV cc)) th
  in th end;

fun RAND_SIMP_SEP_IMP2 def th = let
  val cc = RAND_CONV (ONCE_REWRITE_CONV [def])
  val cc = cc THENC SIMP_CONV std_ss [SEP_IMP_MOVE_COND,LET_DEF] 
  val cc = cc THENC RATOR_CONV (ONCE_REWRITE_CONV 
      (map GSYM [WORD_NOT_LESS,WORD_NOT_LESS_EQUAL,
                 WORD_NOT_LOWER_EQUAL,WORD_NOT_LOWER]))
  val cc = cc THENC SIMP_CONV bool_ss []
  val cc = cc THENC SIMP_CONV (std_ss++star_ss) [SEP_IMP_REFL,LET_DEF]
  val th = CONV_RULE (RATOR_CONV (RAND_CONV cc)) th
  in th end;

fun weaken_strengthen thms def pre_tm post_tm = let
  (* duplicate the condition, add cond (1+1=2) as a dummy to make sure there is a cond! *)
  fun dup (name,b,th,strs) = let
    val th = RW [GSYM ARM_PROG_MOVE_COND] (DISCH ``1+1=2`` th)
    val th = DUPLICATE_COND th
    val str1 = ["  val "^name^" = RW [GSYM ARM_PROG_MOVE_COND] (DISCH ``1+1=2`` "^name^")\n"]
    val str2 = ["  val "^name^" = DUPLICATE_COND "^name^"\n"]
    in (name,b,th,strs @ str1 @ str2) end
  val thms = map dup thms  
  (* weaken posts in base cases *)
  fun weak (name,true,th,strs) = (true,(name,true,th,strs))
    | weak (name,false,th,strs) = let
    val th = RAND_SIMP_SEP_IMP def post_tm th
    val th = MP th TRUTH
    val s1 = "  val "^name^" = Q.SPEC post (MATCH_MP WEAKEN1_LEMMA "^name^")\n"
    val s2 = "  val "^name^" = MP (RAND_SIMP_SEP_IMP2 def "^name^") TRUTH\n"
    in (true,(name,false,th,strs @ [s1,s2])) end 
    handle e => (false,(name,false,TRUTH,[]))
  val thms = map weak thms
  val l = length thms  
  val thms = map snd (filter fst thms)  
  val _ = if length thms < l then 
    print ("Dropped "^int_to_string (l - length thms)^" postconditions.\n") 
    else ()
  (* strengthen pres in all cases *)
  fun strength (name,b,th,strs) = let
    val th = PRE_CONV_RULE (ONCE_REWRITE_CONV [STAR_COMM]) th
    val th = ISPEC pre_tm (MATCH_MP PART_STRENGTHEN_LEMMA th)
    val lemma = prove((fst o dest_imp o concl) th,  
      SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
    val th = MATCH_MP th lemma
    val th = PRE_CONV_RULE (ONCE_REWRITE_CONV [STAR_COMM]) th
    val str1 = ["  val "^name^" = PRE_CONV_RULE (ONCE_REWRITE_CONV [STAR_COMM]) "^name^"\n"]
    val str2 = ["  val "^name^" = APP_PART_STRENGTHEN "^name^" pre (SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])\n"]
    val str3 = ["  val "^name^" = RW [EVAL ``1+1``] "^name^"\n"] 
    val (th,str3) = if b then (RW [EVAL ``1+1``] th,str3) else (th,[]) 
    in (name,b,th,strs @ str1 @ str2 @ str1 @ str3) end
  val thms = map strength thms
  in thms end;

fun merge_base_cases thms strs = let
  val bases = filter (fn (name,b,th,strs) => not b) thms
  val steps = filter (fn (name,b,th,strs) => b) thms
  fun f ((name1,b1,th1,strs1),(name2,b2,th2,strs2)) = let
    val th = APP_MERGE th1 th2
    val strs = strs1 @ strs2 @ ["  val "^name2^" = APP_MERGE "^name1^" "^name2^"\n"]
    in (name2,b1,th,strs) end    
  val (name,_,th,s1) = foldr f (last bases) (butlast bases)
  val spec = (concl o UNDISCH o RW [ARM_PROG_MOVE_COND]) th
  val s2 = ["  val spec = concl (UNDISCH (RW [ARM_PROG_MOVE_COND] "^name^"))\n"]
  val s2 = if length steps = 0 then [] else s2
  val th = RW [EVAL ``1+1``] th 
  val s3 = ["  val "^name^" = RW [EVAL ``1+1``] "^name^"\n"] 
  fun f ((name,_,th,strs1),(xs,strs2)) = (xs @ [(name,th)], strs2 @ strs1)
  val (steps,s4) = foldl f ([],[]) steps
  in ((name,th),steps,spec,strs @ s1 @ s2 @ s3 @ s4) end;
      
val EXPAND_PAIR = prove(
  ``!x y z. ((x,y) = z) = (x = FST z) /\ (y = SND z)``,
  Cases_on `z` \\ REWRITE_TAC [PAIR_EQ,FST,SND]);

fun instatiate_induction spec def ind s ind_str = let
  val pair = (snd o dest_comb o fst o dest_eq o concl) def
  val s = s @ ["  val pair = (snd o dest_comb o fst o dest_eq o concl) def\n"]
  val spec = (PairRules.UNPBETA_CONV pair spec)
  val s = s @ ["  val spec = (PairRules.UNPBETA_CONV pair spec)\n"]
  val spec = (fst o dest_comb o snd o dest_eq o concl) spec
  val s = s @ ["  val spec = (fst o dest_comb o snd o dest_eq o concl) spec\n"]
  val th = ISPEC spec (RW [EXPAND_PAIR] ind)
  val s = s @ ["  val ind = ISPEC spec (RW [EXPAND_PAIR] "^ind_str^")\n"]
  val th = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) th
  val s = s @ ["  val ind = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) ind\n"]
  val th = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) th
  val s = s @ ["  val ind = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) ind\n"]
  in (th,s) end;

fun extract_ind_hyps ind s = let
  val asm = RW [GSYM ARM_PROG_MOVE_COND] (extract_assum ind)
  val s = s @ ["  val asm = RW [GSYM ARM_PROG_MOVE_COND] (extract_assum ind)\n"]  
  fun extract_conjuncts th name prev_name i thms s = let
    val (th1,th2) = (CONJUNCT1 th, CONJUNCT2 th)
    val name1 = name^int_to_string i
    val name2 = name^int_to_string (i+1)
    val s = s @ ["  val ("^name1^","^name2^
                 ") = (CONJUNCT1 "^prev_name^",CONJUNCT2 "^prev_name^")\n"]
    in extract_conjuncts th2 name name2 (i+1) (thms @ [(name1,th1)]) s end 
    handle e => (thms @ [(name^int_to_string i,th)],s)
  val (hyps,s) = extract_conjuncts asm "a" "asm" 1 [] s
  val s = if length hyps = 1 then s @ ["  val a1 = asm\n"] else s
  in (hyps,s) end;

val ARM_PROG_COMPOSE_I = prove(
  ``!P code C Q1 Q2 Q4 Q5 Q6 Z1 Z2.
      ARM_PROG (Q2 * Q6) code C Q4 Z2 ==>
      ARM_PROG P code C Q1 ((Q2 * Q5,I) INSERT Z1) ==>
      SEP_IMP Q5 Q6 ==>
      ARM_PROG P code C (Q1 \/ Q4) (Z1 UNION Z2)``,
  METIS_TAC [arm_progTheory.ARM_PROG_COMPOSE_I]);

fun FIND_INST th = let 
  val cc = SIMP_CONV bool_ss [SEP_IMP_cond,WORD_CMP_NORMALISE,GSYM CONJ_ASSOC]
  val th = CONV_RULE (RATOR_CONV (RAND_CONV cc)) th
  fun g tm = let
    val tm = (fst o dest_imp o concl) th
    val tm = (snd o dest_imp) tm handle e => tm
    val tm = (fst o dest_conj) tm handle e => tm
    in tm end
  in (let val (x,y) = dest_eq (g th)
      in FIND_INST (INST [x|->y] th) end) handle e => 
     (let val (y,x) = dest_eq (g th)
      in FIND_INST (INST [x|->y] th) end) handle e => 
     th end;

fun weak_decide_implies tm1 tm2 = let
  val cc = REWRITE_CONV [WORD_CMP_NORMALISE,CONJ_ASSOC]
  val cc = cc THENC REWRITE_CONV [GSYM AND_IMP_INTRO]
  val cc = cc THENC SIMP_CONV bool_ss [] 
  val tm = mk_imp(tm1,tm2)
  val tm = (snd o dest_eq o concl o QCONV cc) tm
  in (tm = T,tm) end;

fun stronger_decide_implies tm1 tm2 = let
  val tm = snd (weak_decide_implies tm1 tm2)
  val th = METIS_PROVE [] tm
  in true end handle e => false;

fun find_case tm cases = let
  val xs = filter (fn (c,x) => fst (weak_decide_implies tm c)) cases
  in snd (hd xs) end handle e => let
  val xs = filter (fn (c,x) => stronger_decide_implies tm c) cases
  in snd (hd xs) end;

fun prove_step_cases post_tm hyps steps def strs = let
(*
  val (name,th) = hd (hyps)
*)
  fun f (name,th) = let
    val th = DUPLICATE_COND (RW [GSYM ARM_PROG_MOVE_COND] (SPEC_ALL th))
    val temp = RW [ARM_PROG_MOVE_COND,AND_IMP_INTRO] th
    val tm = (fst o dest_imp o concl) temp
    val (p,_,_,_,_) = dest_ARM_PROG (concl (UNDISCH_ALL temp))
    val ps = map get_sep_domain (list_dest_STAR p)
    fun extract_case (name,th) = let
      val (_,_,_,_,q) = dest_ARM_PROG (concl th) 
      val q = (snd o dest_comb o fst o dest_comb) q
      val q = (snd o dest_comb o snd o dest_STAR o fst o dest_pair) q
      in (q,(name,th)) end
    val cases = map extract_case steps
    val (name2,th2) = find_case tm cases 
    val th = SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_PREL_TERM ps th)
    val th2 = SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_POSTL_TERM ps th2)
    val th = MATCH_MP ARM_PROG_COMPOSE_I th 
    val th = MATCH_MP th th2
    val th = MP (FIND_INST th) TRUTH
    val th = SIMP_RULE (bool_ss++sep_ss) [UNION_EMPTY] th
    val th = ISPEC post_tm (MATCH_MP WEAKEN1_LEMMA th)
    val th = MP (RAND_SIMP_SEP_IMP2 def th) TRUTH  
    val s1  = "  val "^name^" = DUPLICATE_COND (RW [GSYM ARM_PROG_MOVE_COND] (SPEC_ALL "^name^"))\n"
    val s2  = "  val ps = ["^list_to_string (fn tm => "`" ^ term_to_string tm ^ "`") ps "," ^"]\n"
    val s3  = "  val "^name^" = SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_PREL ps "^name^")\n"
    val s4  = "  val "^name2^" = SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_POSTL ps "^name2^")\n"
    val s5  = "  val "^name^" = MATCH_MP ARM_PROG_COMPOSE_I "^name^"\n" 
    val s6  = "  val "^name^" = MATCH_MP "^name^" "^name2^"\n"
    val s7  = "  val "^name^" = MP (FIND_INST "^name^") TRUTH\n"
    val s8  = "  val "^name^" = SIMP_RULE (bool_ss++sep_ss) [UNION_EMPTY] "^name^"\n"
    val s9  = "  val "^name^" = Q.SPEC post (MATCH_MP WEAKEN1_LEMMA "^name^")\n"
    val s10 = "  val "^name^" = MP (RAND_SIMP_SEP_IMP2 def "^name^") TRUTH\n"  
    in (name,th,[s1,s2,s3,s4,s5,s6,s7,s8,s9,s10]) end
  val xs = map f hyps
  fun g ((name,th,strs),(thms,strs2)) = (thms @ [(name,th)],strs2 @ strs)   
  in foldl g ([],strs) xs end;

fun merge_all_cases (name,th) hyps ind s = let
  val th = foldr (uncurry APP_MERGE) th (map snd hyps)
  val st = "(foldr (uncurry APP_MERGE) "
  val st = st ^ name ^ " [" ^ list_to_string (fn x => x) (map fst hyps) "," ^ "])"  
  val st = if length(hyps) = 0 then name else st
  val th = RW [ARM_PROG_MOVE_COND] th
  val s = s @ ["  val th = RW [ARM_PROG_MOVE_COND] "^st^"\n"]
  val (th,s) = let
    val tac = REWRITE_TAC [GSYM WORD_NOT_LESS_EQUAL,GSYM WORD_NOT_LOWER_EQUAL] \\ METIS_TAC []
    val th = MP th (prove((fst o dest_imp o concl) th, tac))
    val s = s @ ["  val th = RW [ARM_PROG_MOVE_COND] "^st^"\n"]
    val s = s @ ["  val tac = REWRITE_TAC [GSYM WORD_NOT_LESS_EQUAL,GSYM WORD_NOT_LOWER_EQUAL] THEN METIS_TAC []\n"]
    val s = s @ ["  val th = MP th (prove((fst o dest_imp o concl) th, tac))\n"]
    in (th,s) end handle e => (th,s)
  in if length(hyps) > 0 then let
    val xs = (fst o list_dest_forall o fst o dest_imp o concl) ind
    val s = s @ ["  val xs = (fst o list_dest_forall o fst o dest_imp o concl) ind\n"]
    val th = SPECL xs (MATCH_MP ind (GENL xs (DISCH_ALL th)))
    val s = s @ ["  val th = SPECL xs (MATCH_MP ind (GENL xs (DISCH_ALL th)))\n"]
    in (th,s) end else (th,s) end;

fun append_return name th as_proc strs = 
  if not as_proc then (th,strs) else let
  val th2 = Q.INST [`a`|->`14w`,`x`|->`lr`,`c_flag`|->`AL`] arm_MOV_PC
  val th2 = AUTO_HIDE_STATUS (FST_PROG2 th2)
  val (th,str) = find_composition (th,name) (th2,"ret")
  val th = MOVE_POST `R 14w` (MOVE_POST `S` th)
  val th = Q.GEN `lr` (EXTRACT_CODE th)
  val th = RW [ARM_PROG_FALSE_POST,GSYM ARM_PROC_THM] th
  val s1 = "  val ret = Q.INST [`a`|->`14w`,`x`|->`lr`,`c_flag`|->`AL`] arm_MOV_PC\n"
  val s2 = "  val ret = AUTO_HIDE_STATUS (FST_PROG2 ret)\n"
  val s3 = "  val "^name^" = "^str^"\n"
  val s4 = "  val "^name^" = MOVE_POST `R 14w` (MOVE_POST `S` "^name^")\n"
  val s5 = "  val "^name^" = Q.GEN `lr` (EXTRACT_CODE "^name^")\n"
  val s6 = "  val "^name^" = RW [ARM_PROG_FALSE_POST,GSYM ARM_PROC_THM] "^name^"\n"
  in (th,strs @ [s1,s2,s3,s4,s5,s6]) end;

fun build_definition name tm def_name = let
  val xs = map (fn x => "("^fst (dest_var x) ^ (type_to_string (snd (dest_var x)))^")") (free_vars tm)
  val str = foldl (fn (x,y) => y ^ " " ^ x) name xs
  val _ = Parse.hide name
  val str = "("^str^")" ^ type_to_string (type_of tm) 
  val tm = mk_eq(Parse.Term [QUOTE str],tm)
  val code_def = Define [ANTIQUOTE tm]
  val str = "  val "^def_name^" = Define [ANTIQUOTE (mk_eq(``"^str^"``,tm))]\n"
  in (code_def,str) end;

fun abbreviate_code name thms strs = 
  if not (!abbrev_code) then (thms,TRUTH,strs) else let
    val (n,th) = hd thms
    val tm = code_ARM_PROG (concl th)
    val (code_def,str) = build_definition (name^"_code") tm "code_def"
    val strs2 = ["  val tm = code_ARM_PROG (concl "^n^")\n",str]
    val strs2 = strs2 @ ["  val _ = add_code_abbrev code_def\n"]
    fun f (name,th) = 
      ((name,RW [GSYM code_def] th),"  val "^name^" = RW [GSYM code_def] "^name^"\n")
    val thms = map f thms
    val strs2 = strs2 @ map snd thms
    val thms = map fst thms
    val _ = add_code_abbrev code_def
    in (thms,code_def,strs @ strs2) end;

fun calc_code_length th = let
  val tm = code_ARM_PROG (concl th)
  val tm = mk_comb(``LENGTH:word32 list -> num``,tm)
  val th2 = (code_length_conv()) tm
  in (numSyntax.int_of_term o snd o dest_eq o concl) th2 end;

fun arm_compile def ind as_proc = let
  (* guess name *)
  val tm = (fst o dest_eq o concl o SPEC_ALL) def
  val name = (fst o dest_const) ((fst o dest_comb) tm handle e => tm)
  (* generate code with path traces *)
  val code = make_inst_list2 def
  (* generate basic specs for each path *)
  val (thms,strs) = make_passes_th code 
  (* abbreviate the code using a definition *)
  val (thms,code_def,strs) = abbreviate_code name thms strs 
  (* normalise names and fill using frame *)
  val thms = rename_and_fill_preconditions thms def
  (* hide irrelevant pre and post elements *)  
  val thms = hide_pre_post_elements thms def 
  (* generate pre- and postconditions *)
  val (pre_tm,post_tm,strs) = get_pre_post_terms (name^"_def") thms def strs
  (* weaken posts, strengthen pres *)
  val def = COMPILER_FORMAT_DEF def
  val thms = weaken_strengthen thms def pre_tm post_tm
  (* merge base cases and separate step cases *)
  val (base,steps,spec,strs) = merge_base_cases thms strs
  (* instantiate induction, extract and prove step cases *)
  val (th,strs) =
    if length(steps) > 0 (* = function is recursive *) then let
      val (ind,strs) = instatiate_induction spec def ind strs (name^"_ind")
      val (hyps,strs) = extract_ind_hyps ind strs    
      val (hyps,strs) = prove_step_cases post_tm hyps steps def strs
      val (th,strs) = merge_all_cases base hyps ind strs
      in (th,strs) end 
    else let
      val (th,strs) = merge_all_cases base [] TRUTH strs
      in (th,strs) end 
  (* calculate code length *)
  val code_length = calc_code_length th
  (* if compile as procedure then wrap it up with a `mov pc, lr` *)
  val (th,strs) = append_return "th" th as_proc strs 
  (* format output *)
  val strs = map (fn s => "  "^s) strs 
  val strs = ["  val "^name^"_arm = let\n"] @ strs @ ["  in th end;\n"]
  val result = (name,th,as_proc,code_length,code_def) 
  val _ = save_thm(name^"_arm",th)
  val _ = compiled_specs := result :: !compiled_specs
  in (th,strs) end

fun reset_compiled () = let
  val _ = compiled_specs := []
  val _ = code_length_rewrites := []
  in () end;

end;



