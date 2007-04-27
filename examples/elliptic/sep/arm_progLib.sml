structure arm_progLib :> arm_progLib =
struct

(*
  quietdec := true;
  val armDir = concat Globals.HOLDIR "/examples/elliptic/arm";
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

fun dest_ARM_PROG tm =
  let
    val (p,Z) = dest_comb tm
    val (p,Q) = dest_comb p
    val (p,C) = dest_comb p
    val (p,c) = dest_comb p
    val (p,P) = dest_comb p
  in (P,c,C,Q,Z) end;

val ARM_PROG_PRE_CONV = RATOR_CONV o RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV;
val ARM_PROG_POST1_CONV = RATOR_CONV o RAND_CONV;
val ARM_PROG_POST_CONV = RAND_CONV; (* needs to be smarter *)

fun PRE_CONV_RULE c = CONV_RULE (ARM_PROG_PRE_CONV c);
fun POST1_CONV_RULE c = CONV_RULE (ARM_PROG_POST1_CONV c);
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

val armINST_ss = rewrites 
  [SND,FST,ADDR_MODE1_VAL_def,ADDR_MODE1_CMD_def,ADDR_MODE2_CASES',PASS_CASES,emp_STAR];

val pcINC_ss = rewrites 
  [pcADD_pcADD,pcADD_pcINC,pcINC_pcADD,pcINC_pcINC,pcADD_0,pcINC_0,pcSET_ABSORB];

val setINC_ss = rewrites 
  [setAPP_setAPP,setAPP_UNION,setADD_setADD,setADD_UNION,setAPP_I,setADD_0,
   setINC_def,wLENGTH_def,LENGTH,word_add_n2w];

val compose_ss = simpLib.merge_ss [setINC_ss,pcINC_ss,rewrites 
  [UNION_EMPTY,setINC_CLAUSES,setSTAR_CLAUSES,APPEND,wLENGTH_def,LENGTH,F_STAR]];

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
fun HIDE_POST1 th = 
  MATCH_MP ARM_PROG_HIDE_POST1 th handle e => MATCH_MP HIDE_POST1_LEMMA th;
 
val HIDE_POST_LEMMA = 
  (GEN_ALL o RW [emp_STAR] o Q.INST [`Q'`|->`emp`] o SPEC_ALL) ARM_PROG_HIDE_POST
fun HIDE_POST th = 
  MATCH_MP ARM_PROG_HIDE_POST th handle e => MATCH_MP HIDE_POST_LEMMA th;

(* -- move out e.g. ``R a`` will do ``R b y * R a x * R c z`` -> ``R b y * R c z * R a x`` -- *)

fun MOVE_OUT_CONV t tm = let
  val xs = list_dest_STAR tm
  fun list_search f [] ys = hd [] 
    | list_search f (x::xs) ys = if f x then (ys,x,xs) else list_search f xs (ys @ [x])
  fun is_nil x = (x = [])
  fun f x = (is_nil o fst o match_term t o fst o dest_comb) x handle e => false
  val (ys,x,zs) = list_search f xs []
  val tm' = list_mk_STAR (ys @ zs @ [x])
  val tm = mk_eq (tm,tm')
  val th = SIMP_CONV (bool_ss++star_ss) [] tm
  val th = EQ_MP (GSYM th) TRUTH
  in th end;

fun MOVE_PRE   t = PRE_CONV_RULE (MOVE_OUT_CONV t);
fun MOVE_POST  t = POST_CONV_RULE (MOVE_OUT_CONV t);
fun MOVE_POST1 t = POST1_CONV_RULE (MOVE_OUT_CONV t);

(* -- auto hide methods -- *)

fun GENERIC_AUTO_HIDE r c [] th = th
  | GENERIC_AUTO_HIDE r c (t::ts) th =
      GENERIC_AUTO_HIDE r c ts (r (c t th));

val AUTO_HIDE_PRE   = GENERIC_AUTO_HIDE HIDE_PRE   MOVE_PRE;
val AUTO_HIDE_POST  = GENERIC_AUTO_HIDE HIDE_POST  MOVE_POST;
val AUTO_HIDE_POST1 = GENERIC_AUTO_HIDE HIDE_POST1 MOVE_POST1;

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
      ADDRESS_ROTATE,GSYM addr32_ADD] o INST [x32|->subst [``x:word30``|->x30] ``addr32 x``] end;

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

val AUTO_PRE_HIDE_STATUS = 
  HIDE_STATUS o PRE_CONV_RULE (REWRITE_CONV [STATUS_MOVE]);

val AUTO_POST1_HIDE_STATUS = 
  HIDE_POST1 o POST1_CONV_RULE (REWRITE_CONV [STATUS_MOVE])

val AUTO_POST_HIDE_STATUS = 
  HIDE_POST o POST_CONV_RULE (REWRITE_CONV [STATUS_MOVE])

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

fun ARRANGE_COMPOSE th1 th2 = 
  let
    val th = MATCH_MP ARRANGE_COMPOSE_LEMMA (CONJ th1 th2)
    val th = CONV_RULE (RATOR_CONV (RAND_CONV (SIMP_CONV (bool_ss++star_ss) []))) th
    val th = RW_COMPOSE (MP th TRUTH)
  in th end;

fun FRAME_COMPOSE th1 th2 =
  let
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
  in MATCH_MP ((Q.SPEC t o MATCH_MP lemma) th) th' end;
val APP_STRENGTHEN = APP_X STRENGTHEN_LEMMA;
val APP_PART_STRENGTHEN = APP_X PART_STRENGTHEN_LEMMA;
val APP_WEAKEN1 = APP_X WEAKEN1_LEMMA;
val APP_PART_WEAKEN1 = APP_X PART_WEAKEN1_LEMMA;
val APP_WEAKEN = APP_X WEAKEN_LEMMA;
val APP_PART_WEAKEN = APP_X PART_WEAKEN_LEMMA;

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
    val len1 = (length o fst o listSyntax.dest_list) cs1
    val len2 = (length o fst o listSyntax.dest_list) cs2
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
    val th = SIMP_RULE (pure_ss++sep_ss) [UNION_IDEMPOT,UNION_EMPTY,STAR_OVER_DISJ] th
  in th end;

(* others *)

fun PAT_DISCH pat th = let 
  val tm = hd (filter (can (match_term pat)) (hyp th))
  in DISCH tm th end;

fun PAIR_GEN name vs th = let 
  val ctxt = free_varsl(concl th::hyp th)
  val x = Parse.parse_in_context ctxt vs
  in pairTools.PGEN (mk_var(name,type_of x)) x th end;


(* ============================================================================= *)
(* PRETTY-PRINTER FOR ``enc (instruction)``                                      *)
(* ============================================================================= *)

val show_enc = ref false;
val show_code = ref true;
val show_code_verbosely = ref false;

fun blanks 0 = [] | blanks n = #" "::blanks (n-1);
fun blank_str n = implode (blanks (if n < 0 then 0 else n));

fun print_enc_inst sys (gl,gc,gr) d pps t = 
  if !show_enc andalso !show_code then raise term_pp_types.UserPP_Failed else
  let open Portable term_pp_types in 
    if not (fst (dest_comb t) = ``enc:arm_instruction -> word32``) then
      raise term_pp_types.UserPP_Failed
    else 
      if not (!show_code) andalso not (!show_code_verbosely) then () else let 
        val s = instructionSyntax.dest_instruction NONE (snd (dest_comb t))
        val s = hd (String.fields (fn s => if s = #";" then true else false) s) 
        val (s1,s2) = if !show_code_verbosely then 
                      ("    ",blank_str (40-size s)) else ("<<",">>")
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

fun mk_arm_prog2_string inst_str thm_name suffix indent = let
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
  val evals = evals @ list_get_term ``(sw2sw ((n2w n):'qqq word)):'zzz word`` (concl th)  
  val th = RW (map EVAL evals) th
  val s = "EVAL ``" ^ list_to_string term_to_string_show_types evals "``, EVAL ``" ^ "``"
  val s = if evals = [] then "" else s
  val str = indent ^"val " ^ thm_name ^ " = ("^"*  "^inst_str^"  *"^
             ") SIMP_RULE (bool_ss ++ armINST_ss) ["^s^"] (Q.INST "^ 
             subst_to_string_no_types i indent ^ " " ^ name ^ ") "
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
print_arm_prog2_list ["add a, b, c","sub b, c, d","mul c, d, e"] "th" 1 "  "
mk_arm_prog2_string_list ["add a, b, c","sub b, c, d","mul c, d, e"] "th" 1 "  "
print_arm_prog2 "ldr r15, [r2,#35]" "th" "3" "  " 
*)
    

(* make code for composing basic specs *)

fun comb_match_right tm1 tm2 = let
  val (x1,t1) = dest_comb tm1
  val (x2,t2) = dest_comb tm2      
  in if aconv x1 x2 then match_term t1 t2 else raise ERR "comb_match_right" "No match." end; 

fun std_matcher tm1 tm2 =
  let val r = ``(R a x):('a,'b,'c,'d,'e,'f,'g,'h,'i,'j,'k,'l,'m,'n,'o) ARMset -> bool``
      val m = ``(M a x):('a,'b,'c,'d,'e,'f,'g,'h,'i,'j,'k,'l,'m,'n,'o) ARMset -> bool`` in
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




