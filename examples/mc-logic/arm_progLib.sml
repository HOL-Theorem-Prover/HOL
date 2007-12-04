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
open instructionSyntax addressTheory;
 
(*
  quietdec := false;
*)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val car = fst o dest_comb
val cdr = snd o dest_comb

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val EQ_IMP_IMP = METIS_PROVE [] ``(x:bool=y:bool) ==> x ==> y``;

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

fun PAIR_GEN name vs th = let 
  val ctxt = free_varsl(concl th::hyp th)
  val x = Parse.parse_in_context ctxt vs
  in pairTools.PGEN (mk_var(name,type_of x)) x th end;

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
val HIDE_PRE_LEMMA_ALT = RW [emp_STAR] (Q.INST [`P`|->`emp`] HIDE_PRE_LEMMA)
fun HIDE_PRE th = let 
  val (P,_,_,_,_) = dest_ARM_PROG (concl th)
  val v = (snd o dest_comb o snd o dest_comb) P
  val th = GEN v th
  in MATCH_MP HIDE_PRE_LEMMA th handle e => MATCH_MP HIDE_PRE_LEMMA_ALT th end;

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

val AUTO_HIDE_POST       = GENERIC_AUTO_HIDE HIDE_POST  MOVE_POST;
val AUTO_HIDE_POST1      = GENERIC_AUTO_HIDE HIDE_POST1 MOVE_POST1;
val AUTO_HIDE_POST_TERM  = GENERIC_AUTO_HIDE HIDE_POST  MOVE_POST_TERM;
val AUTO_HIDE_POST1_TERM = GENERIC_AUTO_HIDE HIDE_POST1 MOVE_POST1_TERM;

fun list_dest_pair tm = let val (x,y) = dest_pair tm 
  in list_dest_pair x @ list_dest_pair y end handle e => [tm];

fun AUTO_HIDE_PRE_AUX th = let
  val th = RW [STAR_ASSOC] th
  val (P,_,_,_,_) = dest_ARM_PROG (concl th)
  val v = (snd o dest_STAR) P handle e => P
  val v = cdr v handle e => v     
  val vs = list_dest_pair v
  fun intersect xs ys = filter (fn y => mem y xs) ys
  fun g x = not (intersect vs (free_vars (cdr x)) = []) handle e => false
  val th = repeat (HIDE_POST o POST2_CONV_RULE (MOVE_OUT_AUX_CONV g)) th   
  val th = repeat (HIDE_POST1 o POST1_CONV_RULE (MOVE_OUT_AUX_CONV g)) th   
  val th = PAIR_GEN ((fst o dest_var o genvar o type_of) v) [ANTIQUOTE v] th
  in MATCH_MP HIDE_PRE_LEMMA th handle e => MATCH_MP HIDE_PRE_LEMMA_ALT th end;

val AUTO_HIDE_PRE      = GENERIC_AUTO_HIDE AUTO_HIDE_PRE_AUX MOVE_PRE;
val AUTO_HIDE_PRE_TERM = GENERIC_AUTO_HIDE AUTO_HIDE_PRE_AUX MOVE_PRE_TERM;

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

(* -- modify second post -- *)

val ARM_PROG_ABSORB_POST_LEMMA = prove(
  ``ARM_PROG (P:'a ARMset -> bool) cs C SEP_F ((Q,pcADD x) INSERT Z) ==>
    (x = wLENGTH cs) ==> ARM_PROG P cs C Q Z``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [GSYM ARM_PROG_EXTRACT_POST,GSYM pcINC_def]);

fun ABSORB_POST th = let
  val th = MATCH_MP ARM_PROG_ABSORB_POST_LEMMA (SPEC_ALL th)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [wLENGTH_def,LENGTH])) th
  in RW [] th end;

(* -- hide status -- *)

val HIDE_STATUS_LEMMA = MATCH_MP EQ_IMP_IMP (SPEC_ALL ARM_PROG_HIDE_STATUS)
val HIDE_STATUS_LEMMA_ALT = RW [emp_STAR] (Q.INST [`P`|->`emp`] HIDE_STATUS_LEMMA)
fun HIDE_STATUS th = 
  let val th = GENL [``sN:bool``,``sZ:bool``,``sC:bool``,``sV:bool``] th in
    MATCH_MP HIDE_STATUS_LEMMA th handle e => MATCH_MP HIDE_STATUS_LEMMA_ALT th end;

val STATUS_MOVE = prove(
  ``!P Q x. (S x * P = P * S x) /\ (P * S x * Q = P * Q * (S x):'a ARMset -> bool)``,
  SIMP_TAC (bool_ss++star_ss) []);

val AUTO_PRE_HIDE_STATUS   = HIDE_STATUS o MOVE_PRE `S`;
val AUTO_POST1_HIDE_STATUS = HIDE_POST1 o MOVE_POST1 `S`;
val AUTO_POST_HIDE_STATUS  = HIDE_POST o MOVE_POST `S`;

fun AUTO_HIDE_STATUS th = let
  val th = AUTO_POST1_HIDE_STATUS th handle e => th
  val th = AUTO_POST_HIDE_STATUS th handle e => th
  val th = AUTO_PRE_HIDE_STATUS th handle e => th
  in th end;

(* -- conversion for simplifying address arithmetic such as ``x - 4w + 6w`` -- *)

val word_arith_lemma1 = prove(
  ``!n m. (n2w n + n2w m = n2w (n + m):'a word) /\
          (x + n2w n + n2w m = x + n2w (n + m):'a word) /\
          (x - n2w n - n2w m = x - n2w (n + m):'a word)``,
  REWRITE_TAC [GSYM WORD_SUB_PLUS,word_add_n2w,GSYM WORD_ADD_ASSOC]);

val word_arith_lemma2 = prove(
  ``!n m. n2w n - (n2w m) :'a word = if n < m then $- (n2w (m-n)) else n2w (n-m)``,
  REPEAT STRIP_TAC \\ Cases_on `n < m` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [NOT_LESS,LESS_EQ]
  \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,ADD1,DECIDE ``n+1+p-n = 1+p:num``]
  \\ REWRITE_TAC [GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_REFL] 
  \\ REWRITE_TAC [GSYM WORD_SUB_PLUS] 
  \\ REWRITE_TAC [word_sub_def,WORD_ADD_0,DECIDE ``m+p-m=p:num``]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [GSYM word_sub_def,WORD_SUB_ADD]);
  
val word_arith_lemma3 = prove(
  ``!x n m. x - n2w m + n2w n :'a word = if n < m then x - (n2w (m-n)) else x + n2w (n-m)``,
  REWRITE_TAC [word_sub_def,GSYM WORD_ADD_ASSOC]
  \\ REWRITE_TAC [GSYM (RW1 [WORD_ADD_COMM] word_sub_def),word_arith_lemma2] 
  \\ REPEAT STRIP_TAC \\ Cases_on `n<m` \\ ASM_REWRITE_TAC []);

val word_arith_lemma4 = prove(
  ``!x n m. x + n2w n - n2w m :'a word = if n < m then x - (n2w (m-n)) else x + n2w (n-m)``,
  REWRITE_TAC [word_sub_def,GSYM WORD_ADD_ASSOC]
  \\ REWRITE_TAC [GSYM word_sub_def,word_arith_lemma2]
  \\ REPEAT STRIP_TAC \\ Cases_on `n<m` \\ ASM_REWRITE_TAC [word_sub_def]);

val word_arith_conv =   
  SIMP_CONV arith_ss [word_arith_lemma1,word_arith_lemma2,word_arith_lemma3,
    word_arith_lemma4,WORD_ADD_0,WORD_SUB_RZERO,addr32_ABSORB_CONST,addr30_addr32,ADDRESS_ROTATE];

(* -- compose -- *)

val RW_COMPOSE = SIMP_RULE (std_ss ++ compose_ss) [];

val MATCH_COMPOSE_LEMMA = (RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_SYM]) ARM_PROG_COMPOSE;
val MATCH_COMPOSE_ALT_LEMMA = RW [GSYM AND_IMP_INTRO] ARM_PROG_COMPOSE;
fun MATCH_COMPOSE th1 th2 = 
  RW_COMPOSE (MATCH_MP (MATCH_MP MATCH_COMPOSE_LEMMA th2) th1) handle e =>
  RW_COMPOSE (MATCH_MP (MATCH_MP MATCH_COMPOSE_ALT_LEMMA th1) th2);

val ARRANGE_COMPOSE_LEMMA = prove(
  ``!P:('a ARMset -> bool) M M' Q cs cs' C C' Z Z'.
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

val FALSE_COMPOSE_LEMMA = prove(
  ``ARM_PROG (P1:('a ARMset -> bool)) code1 C1 SEP_F Z1 /\ 
    ARM_PROG (P2:('b ARMset -> bool)) code2 C Q Z ==>
    ARM_PROG P1 (code1++code2) C1 SEP_F Z1``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ARM_PROG_APPEND_CODE \\ ASM_REWRITE_TAC []);

fun FALSE_COMPOSE th1 th2 =
  (RW_COMPOSE o MATCH_MP FALSE_COMPOSE_LEMMA) (CONJ th1 th2);

(* -- a "smart" composition finder -- *)

fun TRY_ABSORB_POST th = 
  let val th' = ABSORB_POST th in 
  if is_imp (concl th') then th else th' end handle e => th;

fun AUTO_COMPOSE th1 th2 = let
  (* preprocessing *)
  val th1 = CONV_RULE word_arith_conv (RW [R30_def,M30_def] th1)
  val th2 = CONV_RULE word_arith_conv (RW [R30_def,M30_def] th2)
  (* extract post and preconditions of interest *)
  fun extract_pre_post_part tm = let
    val (x,y) = dest_comb tm 
    in if is_SEP_HIDE x then (y,NONE) else (x,SOME y) end
  val posts = (map extract_pre_post_part o list_dest_STAR o post1_ARM_PROG o concl) th1
  val pres  = (map extract_pre_post_part o list_dest_STAR o pre_ARM_PROG o concl) th2
  fun is_R_or_M tm = mem ((fst o dest_const o fst o dest_comb) tm) ["R","M"] handle e => false 
  val posts = filter (is_R_or_M o fst) posts
  val pres = filter (is_R_or_M o fst) pres
  (* match individual post-pre pairs *)
  fun conv_to_tm2tm conv tm = (snd o dest_eq o concl o conv) tm handle e => tm
  fun is_NONE NONE = true | is_NONE (SOME _) = false
  fun get_SOME NONE = hd [] | get_SOME (SOME x) = x
  fun attempt f x = f x handle e => x
  fun address_match_term post_exp pre_exp = let
    val vs = filter (fn tm => type_of tm = ``:word32``) (free_vars post_exp)
    val i = map (fn v => v |-> mk_comb(``addr32``,mk_var(fst (dest_var v),``:word30``))) vs
    val post_exp = conv_to_tm2tm (word_arith_conv) (subst i post_exp) 
    in ((i,[]),match_term pre_exp post_exp,I,I) end    
  fun match_post_pre (x,xv) (y,yv) =
    if not (x = y) then hd [] else
      if is_NONE xv 
      then if is_NONE yv then (([],[]),([],[]),I,I) 
                         else (([],[]),([],[]),I,attempt (AUTO_HIDE_PRE_TERM [y]))
      else if is_NONE yv then (([],[]),([],[]),attempt (AUTO_HIDE_POST1_TERM [x]),I) 
                         else ((([],[]),match_term (get_SOME yv) (get_SOME xv),I,I) handle e =>
                               (match_term (get_SOME xv) (get_SOME yv),([],[]),I,I) handle e =>
                               address_match_term (get_SOME xv) (get_SOME yv))
  (* match list *)
  fun find_post_pre_match q [] old_pres = NONE 
    | find_post_pre_match q (p::pres) old_pres = 
       SOME (match_post_pre q p,old_pres @ pres) handle e => find_post_pre_match q pres (old_pres @ [p])
  (* find composition *)
  fun apply_opt f (x,NONE) = (f x,NONE)
    | apply_opt f (x,SOME y) = (f x,SOME (f y))
  fun fix (i,j) = conv_to_tm2tm word_arith_conv o subst i o inst j
  fun compose th1 th2 [] pres old_posts matched_pairs = (th1,th2)
    | compose th1 th2 (q::posts) pres old_posts matched_pairs = let
      val res = find_post_pre_match q pres []
      in if is_NONE res then 
           compose th1 th2 posts pres (old_posts @ [q]) matched_pairs
         else let
           val (((i1,j1),(i2,j2),f1,f2),pres) = get_SOME res
           val th1 = (CONV_RULE word_arith_conv o INST i1 o INST_TYPE j1 o f1) th1
           val th2 = (CONV_RULE word_arith_conv o INST i2 o INST_TYPE j2 o f2) th2
           val (posts,pres,matched_pairs) =
             if (i1,i2) = ([],[]) then (posts,pres,matched_pairs)
             else (posts @ matched_pairs,pres @ matched_pairs,[])
           val posts = map (apply_opt (fix (i1,j1))) (old_posts @ posts)
           val pres = map (apply_opt (fix (i2,j2))) pres
           val q = apply_opt (fix (i1,j1)) q
           in compose th1 th2 posts pres [] (q::matched_pairs) end end
  (* perform composition *)
  val (thA,thB) = compose th1 th2 posts pres [] []
  val th = FRAME_COMPOSE thA thB
  (* postprocessing *)
  val th = RW [GSYM R30_def,GSYM M30_def,GSYM addr32_ADD,GSYM addr32_SUB] th
  in th end handle e => TRY_ABSORB_POST (FALSE_COMPOSE th1 th2);  

(*
val (q::posts) = posts
val matched_pairs = []
val old_posts = []
*)

val ARM_PROG_COMPOSE_FRAME = prove(
  ``ARM_PROG (Q1 * P2:('a ARMset -> bool)) c2 cc2 Q3 Z2 ==>
    ARM_PROG P1 c1 cc1 (Q1 * Q2) Z1 ==> 
    ARM_PROG (P1 * P2) (c1 ++ c2) 
      (cc1 UNION setINC c1 cc2) (Q3 * Q2) 
      (setSTAR P2 Z1 UNION setINC c1 (setSTAR Q2 Z2))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ARM_PROG_COMPOSE
  \\ Q.EXISTS_TAC `Q1 * P2 * Q2` \\ STRIP_TAC
  << [MOVE_STAR_TAC `q*t*p` `(q*p)*t`,ALL_TAC] \\ METIS_TAC [ARM_PROG_FRAME]);

val MOVE_COMPOSE_rw = REWRITE_CONV [setSTAR_CLAUSES,setINC_CLAUSES,UNION_EMPTY,APPEND];
val MOVE_COMPOSE_rw1 = RW [STAR_ASSOC,emp_STAR]

fun MOVE_COMPOSE th1 th2 xs1 xs2 ys1 ys2 = let
  val th1 = POST1_MOVE_STAR xs1 xs2 th1
  val th2 = PRE_MOVE_STAR ys1 ys2 th2
  val th2 = MATCH_MP ARM_PROG_COMPOSE_FRAME th2
  val th2 = MATCH_MP th2 th1
  val c1 = RAND_CONV MOVE_COMPOSE_rw
  val c1 = c1 THENC (RATOR_CONV o RATOR_CONV o RAND_CONV) MOVE_COMPOSE_rw
  val c1 = c1 THENC (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) MOVE_COMPOSE_rw
  val th2 = MOVE_COMPOSE_rw1 (CONV_RULE c1 th2)
  in th2 end;

    

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
  ``ARM_PROG (P * cond h) code C (Q:('a ARMset -> bool)) Z ==>
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
  ``ARM_PROG P cs (([],f) INSERT C) Q Z = ARM_PROG P cs C (Q:('a ARMset -> bool)) Z``,
  REWRITE_TAC [ARM_PROG_THM] \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ REWRITE_TAC [ARM_GPROG_EMPTY_CODE]);

fun PROG2PROC th = let
  val th = RW [R30_def] th
  val th = MOVE_POST `S` th
  val th = AUTO_HIDE_POST [`R 14w`] th handle e => MOVE_POST `R 14w` th
  val th = RW [GSYM R30_def] th
  val th = MOVE_PRE `R30 14w` (MOVE_PRE `S` th)
  val v = (snd o dest_comb o snd o dest_STAR o pre_ARM_PROG o concl) th
  val th = GEN v (EXTRACT_CODE th)
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

fun QGENL [] th = th | QGENL (x::xs) th = Q.GEN x (QGENL xs th);

fun INST_LDM_STM do_eval th = let
  val th = RW [LENGTH,ADDR_MODE4_ADDR_def,ADDR_MODE4_ADDR'_def,
               ADDR_MODE4_WB'_def,ADDR_MODE4_UP_def,MAP,ADDR_MODE4_WB_def,
               ADDR_MODE4_wb_def,xR_list_def,STAR_ASSOC,blank_ms_def,
               ADDR_MODE4_ADDR32_def,ADDR_MODE4_ADDR32'_def,
               ADDR_MODE4_WB32_def,ADDR_MODE4_WB32'_def,seq_addresses_def] th
  val th = REWRITE_RULE [ADD1,GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_ADD] th
  val th = CONV_RULE (DEPTH_CONV BETA_CONV) th  
  val th = RW [PASS_CASES,emp_STAR,FST,SND,xR_list_def,STAR_ASSOC] th
  val tm = find_term (can (match_term ``QSORT (g:'a->'a->bool) h``)) (concl th) handle e =>
           find_term (can (match_term ``reg_values (xs:(word4 # word32) list)``)) (concl th) handle e => T
  val th = if do_eval then RW [RW [GSYM (EVAL ``addr32 x``)] (EVAL tm),ms_def,STAR_ASSOC,emp_STAR] th else th
  val tm = find_term (can (match_term ``reg_bitmap x``)) (concl th) handle e => T
  val th = if do_eval then RW [EVAL tm,list_read_def,ZIP,list_update_def] th else th
  val th = RW [WORD_SUB_ADD,WORD_SUB_RZERO] th
  val th = SIMP_RULE arith_ss [GSYM WORD_SUB_PLUS,word_add_n2w,seq_addresses_def,
              WORD_SUB_RZERO,ADDR_MODE4_CMD_def,MAP,FST,SND,xR_list_def,STAR_ASSOC,emp_STAR] th
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

val match_list_select_seq = 
  [(arm_SWP2_SEQ,"arm_SWP2_SEQ"),(arm_SWP3_SEQ,"arm_SWP3_SEQ"),
   (arm_LDR1_SEQ,"arm_LDR1_SEQ"),(arm_LDR_SEQ,"arm_LDR_SEQ"),
   (arm_STR_SEQ,"arm_STR_SEQ")] @ match_list;


(*
val inst_str = "strne a,[b]"
val inst_str = "stmeqia r3!, {r1, r2, r4}"
val inst_str = "ldmia  r0!, {r3, r4, r5, r6, r7}"
val suffix = "2"
val select_seq = true

show_types := true;
*)

fun mk_arm_prog2_str_STM_LDM inst_str suffix select_seq = let
  val add_sidecond = select_seq
  fun take_until p [] ys = ([],ys) 
    | take_until p (x::xs) ys = if p x then (x::xs,ys) else take_until p xs (ys @ [x]) 
  val (tm,vs,do_eval) = let 
    val (v1,v2) = dest_comb (mk_instruction inst_str) 
    fun foo n i = if n = 0 then [] else 
                  if n mod 2 = 1 then i :: foo (n div 2) (i+1) 
                                 else foo (n div 2) (i+1)
    val xs = foo ((numSyntax.int_of_term o snd o dest_comb) v2) 0
    in (v1,map (fn n => "r" ^ int_to_string n) xs,true) end handle e => let 
    val (vs,str) = take_until (fn x => x = #"{") (explode inst_str) []
    val tm = (fst o dest_comb o mk_instruction) (implode str ^ "{r1,r2}")
    fun too([],s,ys) = ys@[s]
      | too(x::xs,s,ys) = if x = #"," then too(xs,"",ys@[s]) else too(xs,s^implode[x],ys)   
    val vs = too ((rev o tl o rev o tl) vs,"",[])
    in (tm,vs,false) end
  fun fix_name "sp" = "r13" 
    | fix_name "lr" = "r14"
    | fix_name "pc" = "r15"
    | fix_name x = x  
  val vs = map fix_name vs                    
  fun hoo n = subst [``n:num`` |->numSyntax.term_of_int n, 
                     ``x:word32``|->mk_var("x"^int_to_string n^"x"^suffix,``:word32``)] 
              ``((n2w n):word4,x:word32)``                
  fun mk_var_pair st = if substring(st,0,1) = "r" 
    then hoo (string_to_int(substring(st,1,size(st)-1)))    
    else pairSyntax.mk_pair(mk_var(st,``:word4``),mk_var("x"^st^suffix,``:word32``))
  val i = fst (match_term ``STM c_flag F mode v1234`` tm) handle e =>
          fst (match_term ``LDM c_flag F mode v1234`` tm)
  fun delete x xs = filter (fn n => not (n = x)) xs
  fun list_extract [] x = hd [] 
    | list_extract ({redex = x,residue=z}::xs) y = if x = y then z else list_extract xs y
  val varname = "r"^((int_to_string o numSyntax.int_of_term o snd o dest_comb o list_extract i) ``v1234:word4``)
                handle e => fst (dest_var (list_extract i ``v1234:word4``))
  val (form_th,th_str) = if substring(inst_str,0,3) = "stm" then (if select_seq then (arm_STM_SEQ,"arm_STM_SEQ") else (arm_STM,"arm_STM"))
    else (if mem "r15" vs then (if mem varname vs then (arm_LDM_PC_ADDR,"arm_LDM_PC_ADDR") 
                                                  else (arm_LDM_PC,"arm_LDM_PC"))
                          else (if mem varname vs then (arm_LDM_ADDR,"arm_LDM_ADDR") 
                                                  else (if select_seq then (arm_LDM_SEQ,"arm_LDM_SEQ") else (arm_LDM,"arm_LDM"))))
  val vs = delete varname (delete "r15" vs)
  val vs = map mk_var_pair vs
  val j = [``a:word4``|->list_extract i ``v1234:word4``]
  val j = [``c_flag:condition``|->list_extract i ``c_flag:condition``] @ j    
  val m = list_extract i ``mode:transfer_options``    
  val opt = snd (TypeBase.dest_record m)
  fun list_extract2 [] x = hd []
    | list_extract2 ((y,z)::xs) x = if x = y then z else list_extract2 xs x  
  fun g (false,false) = ``am4_DA``
    | g (false,true)  = ``am4_IA``
    | g (true,false)  = ``am4_DB``
    | g (true,true)   = ``am4_IB``
  val x = g (list_extract2 opt "Pre" = ``T``,list_extract2 opt "Up" = ``T``) 
  val m = mk_comb(x,list_extract2 opt "Wb")
  val j = [``a_mode:abbrev_addr4``|->m] @ j
  val select_seq = if substring(inst_str,0,3) = "stm" then false else select_seq
  val xs = if not select_seq then listSyntax.mk_list(vs,``:word4 # word32``)
           else listSyntax.mk_list((map (fst o dest_pair)) vs,``:word4``)
  val j = if select_seq then [``xs:word4 list``|-> xs] @ j
          else [``xs:(word4 # word32) list``|-> xs] @ j
  val fff = free_vars (concl form_th)
  val fff = filter (fn n => not (mem ((fst o dest_var)n) ["sV","sC","sZ","sN","a_mode","c_flag","xs","a"])) fff
  val j = j @ map (fn x => x |-> let val (v,t) = dest_var x in mk_var(v^suffix,t) end) fff
  val th = (INST j form_th)
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = if add_sidecond then RW [GSYM sidecond_def] th else th
  val th = INST_LDM_STM do_eval th
  val str = if do_eval then "true" else "false"
  val str = "INST_LDM_STM "^ str ^" (Q.INST "^ 
             subst_to_string_no_types j "  " ^ " " ^ th_str ^ ")"
  in (th,str) end

fun mk_arm_prog2_str inst_str suffix select_seq = let
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
  val xs = filter filt (if select_seq then match_list_select_seq else match_list)
  val (th,name) = hd xs handle e => raise ERR "arm_str2prog" ("No match for: "^inst_str)
  val tm' = code_from_basic_ARM_PROG2 (concl th)
  val tm' = fix_ii tm'
  val (i,it) = match_term tm' tm
  val i = i @ ii
  val th = INST i th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = if select_seq then RW [GSYM sidecond_def] th else th
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
  in (th,str) end handle e => mk_arm_prog2_str_STM_LDM inst_str suffix select_seq;

(*
string_to_prog_seq "ldr r1,[r2],#4 | ys" "2"
val str = "ldr r1,[r2],#4 | ys"
val suffix = "sdfg"
*)

fun string_split c str = let
  fun f [] ys = hd []
    | f (x::xs) ys = if x = c then (implode (rev ys),implode xs) else f xs (x::ys)
  in f (explode str) [] end

val remove_blanks = implode o filter (fn x => not (x = #" ")) o explode;

fun string_to_prog_seq str suffix = let
  val (str,xs) = string_split #"|" str handle e => (str,"x")
  val xs = remove_blanks xs
  val (th,str) = mk_arm_prog2_str str suffix true
  in let 
    val tm = ((car o car o concl) th)
    val tm = find_term (can (match_term ``(seq a xs):'a ARMset -> bool``)) tm
    val i = [cdr tm|->mk_var(xs^"s",type_of (cdr tm))]
    val i = [(cdr o car) tm|->mk_var(xs,type_of (cdr (car tm)))] @ i
    val th = INST i th    
    in (th,str) end 
  handle e => (th,str) end;

fun string_to_prog str suffix     = mk_arm_prog2_str str suffix false;

fun mk_arm_prog2_string inst_str thm_name suffix indent = let
  val (th,str) = string_to_prog inst_str suffix
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

fun find_composition (th1,name1) (th2,name2) = 
  (AUTO_COMPOSE th1 th2,"AUTO_COMPOSE "^name1^" "^name2);  

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

fun compose_progs_string init [] = (TRUTH,"")
  | compose_progs_string init strs = let
  val xs = pad_strings (map fst strs)
  fun specs [] i = [] | specs (x::xs) i =
    string_to_prog x (int_to_string i) :: specs xs (i+1)
  val xs = zip (zip (specs xs init) xs) (map snd strs)    
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
  val _ = (print "\n\n"; print_thm th)
  in (th,str) end;

fun make_spec' counter strs = print ("\n\n"^ snd (compose_progs_string counter strs) ^"\n\n");
fun make_spec counter strs = make_spec' counter (map (fn name => (name,true)) strs)

(* -- term sorter - makes it easier to read pre and postconditions -- *)

val term_sorter = let
  fun sep_to_string tm = let
    val tm = (snd o dest_eq o concl o REWRITE_CONV [R30_def,M30_def]) tm handle e => tm
    val tm = get_sep_domain tm
    val is_reg = (fst o dest_const o fst o dest_comb) tm = "R" handle e => false
    in if is_reg then let
      val x = term_to_string (snd (dest_comb tm))
      in if size(x) < 3 then "AA 0"^x else "AA "^x end 
    else term_to_string tm end
  in sort (curry (fn (tm1,tm2) => sep_to_string tm1 < sep_to_string tm2)) end

val tm = ``R 1w x * R 7w j * M 5w u * R 2w i``

val sort_conv = let
  fun part_sort_conv tm = let
    val (x,y) = dest_STAR tm
    val xs = list_dest_STAR x @ [y]
    val goal = mk_eq(tm,list_mk_STAR (term_sorter xs))
    in EQT_ELIM (SIMP_CONV (bool_ss++star_ss) [] goal) end
  in ONCE_DEPTH_CONV part_sort_conv end;

val REG_SORT_CONV = sort_conv
val REG_SORT_RULE = CONV_RULE REG_SORT_CONV;
   

end
