
(*
  val armDir = concat Globals.HOLDIR "/examples/elliptic/arm";
  val yaccDir = concat Globals.HOLDIR "/tools/mlyacc/mlyacclib";
  loadPath := !loadPath @ [armDir,yaccDir];
*)

open HolKernel boolLib bossLib;
open pred_setTheory res_quanTheory arithmeticTheory wordsLib wordsTheory bitTheory pairTheory;
open listTheory rich_listTheory relationTheory pairTheory;

open set_sepTheory set_sepLib progTheory arm_progTheory arm_instTheory;


val _ = new_theory "examples";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* Syntax related ML functions                                                   *)
(* ----------------------------------------------------------------------------- *)

val STAR = prim_mk_const {Name="STAR",Thy="set_sep"};
val dest_STAR = dest_binop STAR (ERR"dest_STAR" "not a *");
val is_STAR = can dest_STAR;

fun list_dest_STAR tm =
  let val (v1,v2) = dest_STAR tm in list_dest_STAR v1 @ list_dest_STAR v2 end
  handle e => [tm];

fun mk_STAR(t1,t2) = (fst o dest_eq o concl o ISPECL [t1,t2]) STAR_def;

fun list_mk_STAR [] = raise ERR "list_mk_STAR" "Invalid argument"
  | list_mk_STAR [x] = x
  | list_mk_STAR (x::y::xs) = list_mk_STAR (mk_STAR(x,y)::xs);

fun dest_ARM_PROG tm =
  let
    val (p,Z) = dest_comb tm
    val (p,Q) = dest_comb p
    val (p,C) = dest_comb p
    val (p,cs) = dest_comb p
    val (p,P) = dest_comb p
    val _ = if dest_term(p) = dest_term(``ARM_PROG``) then p else fst (dest_comb ``\x.x``)
  in (P,cs,C,Q,Z) end;


(* ----------------------------------------------------------------------------- *)
(* Various proof tools                                                           *)
(* ----------------------------------------------------------------------------- *)

fun PAT_DISCH pat th =
  let val tm = hd (filter (can (match_term pat)) (hyp th))
  in DISCH tm th end;

fun PGEN name vs th =
  let 
    val ctxt = free_varsl(concl th::hyp th)
    val x = Parse.parse_in_context ctxt vs
  in pairTools.PGEN (mk_var(name,type_of x)) x th end;


(* ----------------------------------------------------------------------------- *)
(* Specialising basic instruction specifications                                 *)
(* ----------------------------------------------------------------------------- *)

val AM1_AM2_PASS_ss = rewrites 
  [ADDR_MODE2_ADDR_def,ADDR_MODE2_WB_def,ADDR_MODE2_CMD1_def,ADDR_MODE2_CMD2_def,
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
  val th = REWRITE_RULE [ARM_PROG2_def,ARM_NOP_def] th  
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
(* Lemmas about set operations                                                   *)
(* ----------------------------------------------------------------------------- *)

val EXPAND_STAR_RIGHT = prove(
  ``!x Q' f'.
      ({ (x * Q,f) |(Q,f)| (Q,f) IN {} } = {}) /\ 
      ({ (x * Q,f) |(Q,f)| (Q,f) IN ((Q',f') INSERT Z) } = 
         (x * Q',f') INSERT { (x * Q,f) |(Q,f)| (Q,f) IN Z })``,
  REPEAT STRIP_TAC
  THEN1 SRW_TAC [] [EXTENSION]
  \\ ONCE_REWRITE_TAC [EXTENSION]  
  \\ SRW_TAC [] []
  \\ EQ_TAC \\ SRW_TAC [] [] \\ METIS_TAC []);

val EXPAND_FRAME = prove(
  ``!R Q' f'.
      ({ (Q * R,f) |(Q,f)| (Q,f) IN {} } = {}) /\ 
      ({ (Q * R,f) |(Q,f)| (Q,f) IN ((Q',f') INSERT Z) } = 
         (Q' * R,f') INSERT { (Q * R,f) |(Q,f)| (Q,f) IN Z })``,
  ONCE_REWRITE_TAC [STAR_SYM] \\ REWRITE_TAC [EXPAND_STAR_RIGHT]);

val setINC_STEP = prove(
  ``!xs Q f.
      (setINC xs {} = {}) /\ 
      (setINC xs ((Q,f) INSERT Z) = (Q,f o pcINC xs) INSERT (setINC xs Z))``,
  REWRITE_TAC [setAPP_def,setADD_def,setINC_def,GSYM pcINC_def]
  \\ REPEAT STRIP_TAC
  THEN1 SRW_TAC [] [EXTENSION]
  \\ ONCE_REWRITE_TAC [EXTENSION]  
  \\ SRW_TAC [] []
  \\ EQ_TAC \\ SRW_TAC [] []
  \\ METIS_TAC []);

val pcADD_pcADD = prove(
  ``!k k'. pcADD k o pcADD k' = pcADD (k + k')``,
  SIMP_TAC std_ss [FUN_EQ_THM,pcADD_def,wLENGTH_def,WORD_ADD_ASSOC]);

val pcADD_pcINC = prove(
  ``!k xs:word32 list. pcADD k o pcINC xs = pcADD (k + wLENGTH xs)``,
  REWRITE_TAC [GSYM pcADD_pcADD,pcINC_def]);

val pcINC_pcADD = prove(
  ``!k xs:word32 list. pcINC xs o pcADD k = pcADD (k + wLENGTH xs)``,
  ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ REWRITE_TAC [GSYM pcADD_pcADD,pcINC_def]);

val pcINC_pcINC = prove(
  ``!xs:word32 list ys. pcINC ys o pcINC xs = pcINC (xs++ys)``,
  REWRITE_TAC [pcINC_def,pcADD_pcADD] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [wLENGTH_def,word_add_n2w,LENGTH_APPEND]);
  
val pcSET_ABSORB = prove(
  ``!x f. pcSET x o f = pcSET x``,
  SIMP_TAC std_ss [pcSET_def,FUN_EQ_THM]);

val pcADD_0 = prove(``pcADD 0w = I``,SRW_TAC [] [WORD_ADD_0,pcADD_def,FUN_EQ_THM]);
val pcINC_0 = prove(``pcINC [] = I``,SRW_TAC [] [pcINC_def,wLENGTH_def,LENGTH,pcADD_0]);

val pcINC_ss = rewrites 
  [pcADD_pcADD,pcADD_pcINC,pcINC_pcADD,pcINC_pcINC,pcADD_0,pcINC_0,pcSET_ABSORB];

val setAPP_setAPP = prove(
  ``!f g x. setAPP f (setAPP g x) = setAPP (g o f) x``,
  SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,setAPP_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ Cases_on `x''` \\ FULL_SIMP_TAC std_ss [] << [
    Cases_on `x''` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q',r')` \\ FULL_SIMP_TAC std_ss [],
    Q.EXISTS_TAC `(q,r o g)` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []]);

val setAPP_UNION = prove(
  ``!f x y. setAPP f (x UNION y) = setAPP f x UNION setAPP f y``,
  SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,setAPP_def,IN_UNION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ Cases_on `x''` \\ FULL_SIMP_TAC std_ss []   
  THEN1 (DISJ1_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [])
  THEN1 (DISJ2_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [])
  \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []);

val setADD_setADD = prove(
  ``!k k' x. setADD k (setADD k' x) = setADD (k + k') x``,
  SIMP_TAC std_ss [setADD_def,setAPP_setAPP,pcADD_pcADD]
  \\ REWRITE_TAC [Once WORD_ADD_COMM]);

val setADD_UNION = prove(
  ``!k x y. setADD k (x UNION y) = setADD k x UNION setADD k y``,
  REWRITE_TAC [setADD_def,setAPP_UNION]);

val setAPP_I = prove(
  ``setAPP I = I``,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC std_ss [setAPP_def,EXTENSION,GSPECIFICATION] 
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  THEN1 (Cases_on `x''` \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []);

val setADD_0 = prove(``setADD 0w x = x``,SRW_TAC [] [setADD_def,FUN_EQ_THM,pcADD_0,setAPP_I]);

val setINC_ss = rewrites [setAPP_setAPP,setAPP_UNION,setADD_setADD,setADD_UNION,
                  setAPP_I,setADD_0,setINC_def,wLENGTH_def,LENGTH,word_add_n2w];
  

(* ----------------------------------------------------------------------------- *)
(* Functions for modifying ARM_PROGs                                             *)
(* ----------------------------------------------------------------------------- *)

val EQ_IMP_IMP = METIS_PROVE [] ``(x=y) ==> x ==> y``;

val APP_BASIC_FRAME = RW [setSTAR_CLAUSES,F_STAR] o MATCH_MP ARM_PROG_FRAME;
fun APP_FRAME x = RW [F_STAR] o Q.SPEC x o APP_BASIC_FRAME;

val HIDE_STATUS_LEMMA = MATCH_MP EQ_IMP_IMP (SPEC_ALL ARM_PROG_HIDE_STATUS)
val HIDE_STATUS_LEMMA_ALT = RW [emp_STAR] (Q.INST [`P`|->`emp`] HIDE_STATUS_LEMMA)
fun HIDE_STATUS th = 
  let val th = GENL [``sN:bool``,``sZ:bool``,``sC:bool``,``sV:bool``] th in
    MATCH_MP HIDE_STATUS_LEMMA th handle e => MATCH_MP HIDE_STATUS_LEMMA_ALT th end;

(* composition *)

val COMPOSE_ss = simpLib.merge_ss [setINC_ss,pcINC_ss,rewrites 
  [UNION_EMPTY,setINC_CLAUSES,setSTAR_CLAUSES,APPEND,wLENGTH_def,LENGTH,F_STAR]];
val RW_COMPOSE = SIMP_RULE (std_ss ++ COMPOSE_ss) [];

val MATCH_COMPOSE_LEMMA = (RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_SYM]) ARM_PROG_COMPOSE;
fun MATCH_COMPOSE th1 th2 = RW_COMPOSE (MATCH_MP (MATCH_MP MATCH_COMPOSE_LEMMA th2) th1);

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


(* ----------------------------------------------------------------------------- *)
(* Generating composition proofs (for at least basic instruction specs)          *)
(* ----------------------------------------------------------------------------- *)

fun comb_match_right tm1 tm2 = let
  val (x1,t1) = dest_comb tm1
  val (x2,t2) = dest_comb tm2      
  in if aconv x1 x2 then match_term t1 t2 else raise ERR "comb_match_right" "No match." end; 

fun std_matcher tm1 tm2 =
  if can (match_term ``R a x``) tm2 orelse can (match_term ``M a x``) tm2 
    then comb_match_right tm1 tm2 else match_term tm1 tm2;

fun list_to_string f [] sep = ""
  | list_to_string f [x] sep = f x
  | list_to_string f (x::y::xs) sep = f x ^ sep ^ list_to_string f (y::xs) sep;

fun term_to_string_show_types tm = let
  val b = !show_types
  val _ = show_types := true
  val st = term_to_string tm 
  val _ = show_types := b
  in st end; 

fun subst_to_string xs st =
  let fun f {redex = x, residue = y} = 
      "`" ^ term_to_string_show_types x ^ "` |-> `" ^ term_to_string_show_types y ^ "`"
  in st^"[" ^ list_to_string f xs (",\n "^st) ^ " ]" end;

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
  val i_as_string = subst_to_string i indent
  in (i,i_as_string) end;

fun find_composition (th1,name1) (th2,name2) name indent = let
  val (i,i_string) = find_substs th1 th2 (indent ^ "  ")
  val str = indent ^ "val "^name^"' = Q.INST\n" ^ i_string ^ " " ^ name2
  val str = str ^ "\n" ^ indent ^ "val "^name^" = FRAME_COMPOSE "^name1^" "^name^"'\n"
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

val th1 = SPEC_ARM_RULE arm_ADD2 [`a`,`b`] [`ax`,`bx`] (SOME `OneReg`)
val th2 = SPEC_ARM_RULE arm_ADD2 [`b`,`c`] [`bx`,`cx`] (SOME `OneReg`)
val th3 = SPEC_ARM_RULE arm_SUB2 [`c`,`d`] [`cx`,`dx`] (SOME `OneReg`)
val th4 = SPEC_ARM_RULE arm_SUB2 [`c`,`d`] [`cx`,`dx`] (SOME `OneReg`)
val th5 = SPEC_ARM_RULE arm_SUB2 [`c`,`d`] [`cx`,`dx`] (SOME `OneReg`)

print_compositions [(th1,"th1"),(th2,"th2"),(th3,"th3"),(th4,"th4"),(th5,"th5")] "th" "  "

  val th' = Q.INST
    [`(bx :word32)` |-> `(ax :word32) + (bx :word32)` ] th2
  val th = FRAME_COMPOSE th1 th'
  val th' = Q.INST
    [`(cx :word32)` |-> `(ax :word32) + (bx :word32) + (cx :word32)` ] th3
  val th = FRAME_COMPOSE th th'
  val th' = Q.INST
    [`(cx :word32)` |-> `(ax :word32) + (bx :word32) + (cx :word32)`,
     `(dx :word32)` |-> `(ax :word32) + (bx :word32) + (cx :word32) - (dx :word32)` ] th4
  val th = FRAME_COMPOSE th th'
  val th' = Q.INST
    [`(cx :word32)` |-> `(ax :word32) + (bx :word32) + (cx :word32)`,
     `(dx :word32)` |-> `(ax :word32) + (bx :word32) + (cx :word32) -
(ax + bx + cx - (dx :word32))` ] th5
  val th = FRAME_COMPOSE th th'

*)


(* ----------------------------------------------------------------------------- *)
(* Setting the environment                                                       *)
(* ----------------------------------------------------------------------------- *)

val AM1_ss = rewrites [ADDR_MODE1_VAL_def,ADDR_MODE1_CMD_def];
val AM2_ss = rewrites [ADDR_MODE2_ADDR_def,ADDR_MODE2_WB_def,ADDR_MODE2_CMD1_def,ADDR_MODE2_CMD2_def];
val PASS_ss = rewrites [PASS_CASES];
val ARM_PROG_ss = bool_ss++AM1_ss++AM2_ss++sep_ss++PASS_ss;

fun SET_SC s c = SIMP_RULE ARM_PROG_ss [] o Q.INST [`s_flag:bool`|->s,`c_flag:condition`|->c];
fun SET_AM x = SIMP_RULE ARM_PROG_ss [] o Q.INST [`a_mode`|->x];

fun SPLIT_PROG2 th = 
  let
    val (x,y) = (CONJ_PAIR o RW [ARM_PROG2_def,ARM_NOP_def]) th
    val f = SIMP_RULE (pure_ss++PASS_ss) []
  in
    (f x,f (Q.ISPEC `(sN:bool,sZ:bool,sC:bool,sV:bool)` y))
  end;

val FST_PROG2 = fst o SPLIT_PROG2;
val SND_PROG2 = snd o SPLIT_PROG2;


(* ----------------------------------------------------------------------------- *)
(* Derived loop rules                                                            *)
(* ----------------------------------------------------------------------------- *)

val ARM_PROG_LOOP_MEASURE = prove(
  ``!m:'a->num P cs C Z. 
      (!v0. ARM_PROG (P v0) cs C Q (((SEP_EXISTS v. P v * cond (m v < m v0)),I) INSERT Z)) ==>
      (!v0. ARM_PROG (P v0) cs C Q Z)``,
  REWRITE_TAC [GSYM (SIMP_CONV std_ss [prim_recTheory.measure_def,relationTheory.inv_image_def]
                               ``measure m (v:'a) v0``)]
  \\ REPEAT STRIP_TAC 
  \\ MATCH_MP_TAC ARM_PROG_LOOP
  \\ Q.EXISTS_TAC `measure m` 
  \\ ASM_REWRITE_TAC [prim_recTheory.WF_measure]);
  
val ARM_PROG_LOOP_LO =
  (RW [GSYM WORD_LO] o Q.ISPEC `w2n`) ARM_PROG_LOOP_MEASURE;

val ARM_PROG_LOOP_DEC = prove(
  ``!P cs C Z. 
      (!v:'a word. ARM_PROG (P v * cond ~(v = 0w)) cs C Q 
                     ((P (v - 1w) * cond ~(v - 1w = 0w),I) INSERT Z)) ==>
      (!v. ARM_PROG (P v * cond ~(v = 0w)) cs C Q Z)``,
  ONCE_REWRITE_TAC [(GSYM o BETA_CONV) ``(\x. P x * cond ~(x:'a word = 0w)) v``]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC ARM_PROG_LOOP_LO
  \\ FULL_SIMP_TAC std_ss []
  \\ SRW_TAC [] [ARM_PROG_MOVE_COND]  
  \\ PAT_ASSUM ``!v. b`` 
         (ASSUME_TAC o UNDISCH o RW [ARM_PROG_MOVE_COND] o Q.SPEC `v0`)
  \\ MATCH_MP_TAC ARM_PROG_WEAKEN_POST
  \\ Q.EXISTS_TAC `(P (v0 - 1w) * cond ~(v0 - 1w = 0w))`
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [sep_ss] [SEP_IMP_def,SEP_EXISTS_THM,GSYM STAR_ASSOC]
  \\ Q.EXISTS_TAC `v0 - 1w`
  \\ ONCE_REWRITE_TAC [STAR_SYM]
  \\ ASM_MOVE_STAR_TAC `x*y` `y*x`
  \\ FULL_SIMP_TAC std_ss [cond_STAR]
  \\ METIS_TAC [WORD_LO,WORD_PRED_THM]);


(* ----------------------------------------------------------------------------- *)
(* Count down loop                                                               *)
(* ----------------------------------------------------------------------------- *)

val SUB_LEMMA = prove(``(x = 1w:word32) = (x - 1w = 0w)``,METIS_TAC [WORD_EQ_SUB_ZERO]);

val COUNT_DOWN_POST = prove(
  ``!x. SEP_IMP (Inv (x - 1w) * R a (x - 1w) * ~S * cond (x - 1w = 0w))
                (Inv 0w * R a 0w * ~S)``,
  REWRITE_TAC [SEP_IMP_MOVE_COND,GSYM SUB_LEMMA]
  \\ SIMP_TAC std_ss [WORD_SUB_REFL,SEP_IMP_REFL]);

val ARM_DOWN_LOOP = let
  val sub = SET_AM `Imm 1w` (SET_SC `T` `AL` arm_SUB1)
  val sub = RW [EVAL ``(w2w (1w:word8)):word32``,SUB_LEMMA] sub
  val sub = HIDE_STATUS (FST_PROG2 sub)
  val b = SET_SC `F` `NE` arm_B
  val b = RW1 [STAR_SYM] b
  val b = MATCH_MP ARM_PROG_HIDE_POST b
  val b = MATCH_MP ARM_PROG_HIDE_POST1 b
  val b = RW1 [STAR_SYM] b
  val b = APP_FRAME `R a (x - 1w)` b
  val sub_b = MATCH_COMPOSE sub (RW1 [STAR_COMM] b)
  val sub_b = APP_FRAME `Inv (x - 1w:word32)` sub_b
  val sub_b = RW1 [STAR_SYM] sub_b
  val sub_b = RW [STAR_ASSOC] sub_b
  val form = (SPEC_ALL o ASSUME)
                ``!x. ARM_PROG (Inv x * R a x * ~S * cond ~(x = 0w)) code C 
                               (Inv (x - 1w) * R a x * ~S) {}``
  val form = MATCH_COMPOSE form sub_b
  val form = DISCH ``sw2sw(offset:word24)+2w+1w+n2w (LENGTH (code:word32 list))=0w:word30`` form
  val form = SIMP_RULE bool_ss [pcADD_0] form
  val form = UNDISCH form
  val wkn = RW [GSYM AND_IMP_INTRO] ARM_PROG_WEAKEN_POST1
  val wkn = MATCH_MP wkn (SPEC_ALL COUNT_DOWN_POST)
  val form = MATCH_MP wkn form
  val th = (BETA_RULE o Q.ISPEC `\x. Inv x * R a x * ~S `) ARM_PROG_LOOP_DEC
  val form = Q.GEN `v` (Q.INST [`x`|->`v`] form)
  val form = MATCH_MP th form
  val form = DISCH_ALL (PAT_DISCH ``x=y:'a`` form)
in form end;


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

val FAC_INV_thm = SIMP_CONV std_ss [FAC_INV_def] ``FAC_INV a n x``;

val FAC_INV_INTRO = prove(
  ``SEP_IMP 
      (R a (n2w (RFAC n (w2n x)) * x) * cond (w2n x <= n) * cond ~(x = 0w))
      (FAC_INV a n (x - 1w))``,
  SRW_TAC [] [SEP_IMP_MOVE_COND,FAC_INV_def]
  \\ `w2n (x - 1w) <= n`  
      by METIS_TAC [WORD_PRED_THM,LESS_LESS_EQ_TRANS,LESS_IMP_LESS_OR_EQ]
  \\ ASM_SIMP_TAC (std_ss++sep_ss) []
  \\ MATCH_MP_TAC (METIS_PROVE [SEP_IMP_REFL] ``(x = y) ==> SEP_IMP x y``)
  \\ CONV_TAC ((RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV) 
               (ONCE_REWRITE_CONV [GSYM n2w_w2n]))
  \\ REWRITE_TAC [word_mul_n2w]
  \\ `w2n (x-1w) = w2n x - 1` by METIS_TAC [DECIDE ``SUC n - 1 = n``,SUC_WORD_PRED]
  \\ ASM_SIMP_TAC std_ss [FAC_STEP_LEMMA,RFAC_def,w2n_eq_0]);

val POST_SIMP_LEMMA = prove(
  ``SEP_IMP (R a x * R b 1w * ~S * cond (x = 0w)) 
            (R a 0w * R b (wFAC x) * ~S)``,
  SRW_TAC [] [SEP_IMP_MOVE_COND,FAC_def,wFAC_def,SEP_IMP_REFL]);

val POST_MERGE = prove(
  ``(w = wLENGTH xs) ==> ({(x,pcADD w)} UNION {(x,pcINC xs)} = {(x,pcINC xs)})``,
  SRW_TAC [] [pcINC_def]);

val ARM_PROG_PRE_CONV = RATOR_CONV o RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV;
val ARM_PROG_POST1_CONV = RATOR_CONV o RAND_CONV;
val ARM_PROG_POST_CONV = RAND_CONV; (* needs to be smarter *)

fun PRE_CONV_RULE c = CONV_RULE (ARM_PROG_PRE_CONV c);
fun POST1_CONV_RULE c = CONV_RULE (ARM_PROG_POST1_CONV c);
fun POST_CONV_RULE c = CONV_RULE (ARM_PROG_POST_CONV c);

fun PRE_MOVE_STAR t1 t2 = CONV_RULE (ARM_PROG_PRE_CONV (MOVE_STAR_CONV t1 t2));
fun POST_MOVE_STAR t1 t2 = CONV_RULE (ARM_PROG_POST_CONV (MOVE_STAR_CONV t1 t2));
fun POST1_MOVE_STAR t1 t2 = CONV_RULE (ARM_PROG_POST1_CONV (MOVE_STAR_CONV t1 t2));

(* ------------ *)

val ARM_BASIC_FAC = let
  val mul = FST_PROG2 (SET_SC `F` `AL` arm_MUL2)
  val mul = MATCH_MP ARM_PROG_HIDE_POST1 mul
  val mul = HIDE_STATUS mul
  val mul = APP_FRAME `cond (w2n (x:word32) <= n) * cond ~(x = 0w)` mul
  val mul = RW1 [WORD_MULT_COMM] mul
  val mul = Q.INST [`y`|->`n2w (RFAC n (w2n x))`] mul
  val mul = MOVE_STAR_RULE `a*b*s*(c1*c2)` `(b*c1*c2)*a*s` mul
  val mul = RW [STAR_ASSOC,GSYM FAC_INV_thm] mul
  val imp = Q.SPEC `R b x * ~S` (MATCH_MP SEP_IMP_FRAME FAC_INV_INTRO)
  val imp = RW [STAR_ASSOC] imp
  val wkn = RW [GSYM AND_IMP_INTRO] ARM_PROG_WEAKEN_POST1
  val wkn = MATCH_MP wkn imp
  val mul = MATCH_MP wkn mul
  val mul = MOVE_STAR_RULE `b*c*a*s` `b*a*s*c` mul
  val fac = MATCH_MP ARM_DOWN_LOOP (Q.GEN `x` mul)
  val fac = Q.INST [`offset`|->`0w-4w`] fac
  val fac = SIMP_RULE std_ss [APPEND] (CONV_RULE (RATOR_CONV EVAL) fac)
  val fac = Q.SPEC `x` fac
  val fac = Q.INST [`n`|->`w2n (x:word32)`] fac
  val fac = SIMP_RULE (std_ss++sep_ss) 
            [RFAC_EQ_1,EVAL ``w2n (0w:word32)``,RFAC_0,GSYM wFAC_def,FAC_INV_thm] fac
  val fac = PRE_MOVE_STAR `b*a*s*c` `a*b*s*c` fac
  val fac = POST1_MOVE_STAR `b*a*s` `a*b*s` fac
in fac end;

val ARM_FAC1_PROGRAM = let
  val mov = FST_PROG2 (SET_AM `Imm 1w` (SET_SC `F` `AL` arm_MOV1))
  val mov = SIMP_RULE (srw_ss()) [EVAL ``(w2w (1w:word8)):word32``] mov
  val mov = MATCH_MP ARM_PROG_HIDE_POST1 mov
  val mov = HIDE_STATUS mov
  val mov = (RW [ARM_PROG_HIDE_PRE] o Q.GEN `x` o RW1 [STAR_SYM]) mov
  val mov = Q.INST [`a`|->`b`,`b`|->`a`] mov
  val mov1 = APP_FRAME `R a x * cond ~(x = 0w)` mov
  val mov1 = MOVE_STAR_RULE `s*rb*(ra*c)` `ra*rb*s*c` mov1
  val fac1 = MATCH_COMPOSE mov1 ARM_BASIC_FAC
in fac1 end;

val ARM_FAC_PROGRAM = let
  val mov = FST_PROG2 (SET_AM `Imm 1w` (SET_SC `F` `AL` arm_MOV1))
  val mov = SIMP_RULE (srw_ss()) [EVAL ``(w2w (1w:word8)):word32``] mov
  val mov = MATCH_MP ARM_PROG_HIDE_POST1 mov
  val mov = HIDE_STATUS mov
  val mov = (RW [ARM_PROG_HIDE_PRE] o Q.GEN `x` o RW1 [STAR_SYM]) mov
  val mov = Q.INST [`a`|->`b`,`b`|->`a`] mov
  val cmp = FST_PROG2 (SET_AM `Imm 0w` (SET_SC `T` `AL` arm_CMP1))
  val cmp = HIDE_STATUS cmp
  val cmp = RW [EVAL ``(w2w (0w:word8)):word32``] cmp
  val b = SET_SC `T` `EQ` arm_B
  val b = RW1 [STAR_SYM] b 
  val b = MATCH_MP ARM_PROG_HIDE_POST1 b
  val b = MATCH_MP ARM_PROG_HIDE_POST b
  val b = APP_FRAME `R a x` b
  val b = CONV_RULE ((RATOR_CONV o RATOR_CONV) (MOVE_STAR_CONV `x*y` `y*x`)) b
  val b = MOVE_STAR_RULE `x*y*z` `z*y*x` b
  val b = MATCH_COMPOSE cmp b
  val b = APP_FRAME `R b 1w` b
  val b = PRE_MOVE_STAR `a*s*b` `a*b*s` b
  val b = MOVE_STAR_RULE `a*s*c*b` `a*b*s*c` b
  val b = MATCH_MP ARM_PROG_WEAKEN_POST (CONJ POST_SIMP_LEMMA b)
  val mov2 = APP_FRAME `R a x` mov
  val mov2 = MOVE_STAR_RULE `s*b*a` `a*b*s` mov2 
  val b = MATCH_COMPOSE mov2 b
  val fac2 = MATCH_COMPOSE b ARM_BASIC_FAC
  val fac2 = Q.INST [`offset`|->`2w`] fac2 
  val lemma = prove(
    ``pcINC [enc (MOV AL F b (Dp_immediate 0w 1w));
             enc (CMP AL a (Dp_immediate 0w 0w)); enc (B EQ 2w);
             enc (MUL AL F b a b); enc (SUB AL T a a (Dp_immediate 0w 1w));
             enc (B NE (0w - 4w))] = pcADD (sw2sw (2w:word24) + 2w + 1w + 1w:word30)``,
    REWRITE_TAC [pcINC_def,wLENGTH_def,LENGTH] \\ EVAL_TAC)
  val fac2 = RW [GSYM lemma,ARM_PROG_ABSORB_POST,SEP_DISJ_CLAUSES] fac2
in fac2 end;


(* verified implementations:

fac1:

  MOV    a,  #1
  MUL    a,  b,  a
  SUBS   b,  b,  #1
  BNE    -2

fac2:

  MOV    a,  #1
  CMP    b,  #0
  BEQ    +3
  MUL    a,  b,  a
  SUBS   b,  b,  #1
  BNE    -2

*)


(* ----------------------------------------------------------------------------- *)
(* GCD program                                                                   *)
(* ----------------------------------------------------------------------------- *)


(* cond gathering conversion and rule *)

val cond_ELIM = prove(
  ``!c c' P . (cond c * cond c' = cond (c /\ c')) /\ 
              (P * cond c * cond c' = P * cond (c /\ c'))``,
  REWRITE_TAC [GSYM STAR_ASSOC,SEP_cond_CLAUSES]);

val cond_MOVE = prove(
  ``!c P Q. (cond c * P = P * cond c) /\
            (P * cond c * Q = P * Q * cond c)``,
  SIMP_TAC (bool_ss++star_ss) []);

val cond_CONV =
  REWRITE_CONV [STAR_ASSOC] THENC
  REPEATC (REWRITE_CONV [cond_ELIM] THENC ONCE_REWRITE_CONV [cond_MOVE]) THENC
  REWRITE_CONV [GSYM CONJ_ASSOC];

fun SIMP_cond ss ths = CONV_RULE (cond_CONV THENC SIMP_CONV ss ths);


(* composition rules *)

val ALT_PROG_COMPOSE = RW [GSYM AND_IMP_INTRO] ARM_PROG_COMPOSE;
fun COMPOSE th1 th2 = RW_COMPOSE (MATCH_MP (MATCH_MP ALT_PROG_COMPOSE th1) th2);


(* merge rules *)

val INSERT_APPEND = prove(
  ``!x t s. ({} UNION s = s) /\ ((x INSERT t) UNION s = x INSERT (t UNION s))``,
  SRW_TAC [] [EXTENSION] \\ METIS_TAC []);

fun APP_MERGE th th' =
  SIMP_RULE (bool_ss++sep_ss) 
  [INSERT_APPEND,ARM_PROG_MERGE_POST,STAR_OVER_DISJ] 
  (MATCH_MP ARM_PROG_MERGE (CONJ th th'))


(* pre-strengthen rule *)

val STRENGTHEN_LEMMA = 
  (DISCH_ALL o Q.GEN `P'` o UNDISCH o SPEC_ALL o 
   RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_SYM]) ARM_PROG_STRENGTHEN_PRE;

fun APP_STRENGTHEN_TERM th t = 
  (fst o dest_imp o concl o Q.SPEC t o MATCH_MP STRENGTHEN_LEMMA) th;

fun APP_STRENGTHEN th t tac = 
  let
    val th' = prove(APP_STRENGTHEN_TERM th t, tac)
  in
    MATCH_MP ((Q.SPEC t o MATCH_MP STRENGTHEN_LEMMA) th) th'
  end;


(* post1-weakening rule *)

val WEAKEN1_LEMMA = 
  (DISCH_ALL o Q.GEN `Q'` o UNDISCH o SPEC_ALL o 
   RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_SYM]) ARM_PROG_WEAKEN_POST1;

fun APP_WEAKEN1_TERM th t = 
  (fst o dest_imp o concl o Q.SPEC t o MATCH_MP WEAKEN1_LEMMA) th;

fun APP_WEAKEN1 th t tac = 
  let
    val th' = prove(APP_WEAKEN1_TERM th t, tac)
  in
    MATCH_MP ((Q.SPEC t o MATCH_MP WEAKEN1_LEMMA) th) th'
  end;


(* post-weakening rule *)

val WEAKEN_LEMMA = 
  (DISCH_ALL o Q.GEN `Q''` o UNDISCH o SPEC_ALL o 
   RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_SYM]) ARM_PROG_WEAKEN_POST;

fun APP_WEAKEN_TERM th t = 
  (fst o dest_imp o concl o Q.SPEC t o MATCH_MP WEAKEN_LEMMA) th;

fun APP_WEAKEN th t tac = 
  let
    val th' = prove(APP_WEAKEN_TERM th t, tac)
  in
    MATCH_MP ((Q.SPEC t o MATCH_MP WEAKEN_LEMMA) th) th'
  end;


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
    Cases_on `n` THEN1 DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [GCD_def,LESS_MOD],
    Cases_on `m` THEN1 DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [GCD_def,LESS_MOD]]);
    
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

val WORD_GT = 
  let 
    val th = SIMP_RULE std_ss 
               [nzcv_def,LET_DEF,GSYM word_add_def,GSYM word_sub_def] word_gt_def
    val th = SPEC_ALL th
    val th = CONV_RULE (funpow 5 RAND_CONV SYM_CONV) th
  in RW [WORD_EQ_SUB_ZERO] (GSYM th) end;

val WORD_LT = 
  let 
    val th = SIMP_RULE std_ss 
               [nzcv_def,LET_DEF,GSYM word_add_def,GSYM word_sub_def] word_lt_def
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
  val subGT1 = SIMP_cond std_ss [subGT_SIMP] subGT1
  val subLT1 = SIMP_cond std_ss [subLT_SIMP] subLT1
  val bne1 = SIMP_cond std_ss [bne1_SIMP,SEP_cond_CLAUSES,F_STAR] bne1
  val bne1 = RW [ARM_PROG_FALSE_POST] (RW1 [INSERT_COMM] bne1)
  val reorder = MOVE_STAR_RULE `s*a*b*c` `a*b*s*c`

  val th1 = cmp1
  val th1 = COMPOSE th1 (reorder subGT1)
  val th1 = COMPOSE th1 (reorder subLT1)
  val th1 = COMPOSE th1 (reorder bne1)

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
  val subGT2 = SIMP_cond std_ss [] subGT2
  val subLT2 = SIMP_cond std_ss [subLT2_SIMP] subLT2
  val bne2 = SIMP_cond std_ss [bne2_SIMP,SEP_cond_CLAUSES,F_STAR,ARM_PROG_FALSE_POST] bne2
  val reorder = MOVE_STAR_RULE `s*a*b*c` `a*b*s*c`
  
  val th2 = cmp2
  val th2 = COMPOSE th2 subGT2
  val th2 = COMPOSE th2 (reorder subLT2)
  val th2 = COMPOSE th2 (reorder bne2)

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
  val subGT3 = SIMP_cond std_ss [subGT3_SIMP] subGT3
  val subLT3 = SIMP_cond std_ss [] subLT3
  val bne3 = SIMP_cond std_ss [bne3_SIMP,SEP_cond_CLAUSES,F_STAR,ARM_PROG_FALSE_POST] bne3
  val reorder = MOVE_STAR_RULE `s*a*b*c` `a*b*s*c`
  
  val th3 = cmp3
  val th3 = COMPOSE th3 (reorder subGT3)
  val th3 = COMPOSE th3 subLT3
  val th3 = COMPOSE th3 (reorder bne3)

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
  val th123 = SIMP_RULE (bool_ss++sep_ss) [lemma] th123
  val th123 = PGEN "x" `(x,y)` th123
  val th123 = Q.INST [`offset`|->`0w-5w`] th123
  val th123 = RW [EVAL ``sw2sw (0w-5w:word24) + 2w + 3w:word30``,pcADD_0] th123
  val th123 = MATCH_MP ARM_PROG_LOOP_MEASURE th123
  val th123 = Q.SPEC `(x,y)` th123
  val th123 = RW [GCD_INV_def] (Q.INST [`x0`|->`x`,`y0`|->`y`] th123)

in th123 end;


val HIDE_PRE_LEMMA = MATCH_MP EQ_IMP_IMP (SPEC_ALL ARM_PROG_HIDE_PRE);
fun HIDE_PRE th = 
  let 
    val (P,_,_,_,_) = dest_ARM_PROG (concl th)
    val v = (snd o dest_comb o snd o dest_comb) P
  in MATCH_MP HIDE_PRE_LEMMA (GEN v th) end;

val HIDE_POST1_LEMMA = 
  (GEN_ALL o RW [emp_STAR] o Q.INST [`Q`|->`emp`] o SPEC_ALL) ARM_PROG_HIDE_POST1
fun HIDE_POST1 th = 
  MATCH_MP ARM_PROG_HIDE_POST1 th handle e => MATCH_MP HIDE_POST1_LEMMA th;
 
val HIDE_POST_LEMMA = 
  (GEN_ALL o RW [emp_STAR] o Q.INST [`Q'`|->`emp`] o SPEC_ALL) ARM_PROG_HIDE_POST
fun HIDE_POST th = 
  MATCH_MP ARM_PROG_HIDE_POST th handle e => MATCH_MP HIDE_POST_LEMMA th;



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
    val th = SET_AM `RegOff (T,F,T,1w)` (PROG_INST arm_STR)  
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
  val ldr = PROG_INST (SET_AM `RegOff (F,T,T,n2w n)` arm_LDR)
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
  val ldr = MATCH_MP ARM_PROG_WEAKEN_POST1 (CONJ th ldr)
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
  `SUM_BTREE_SPEC' a b sum d C' tree =
      !x s. ARM_PROCS d
        (R30 a x * ~ R b * bt (x,tree) * R sum s) 
        (~ R a * ~ R b * bt (x,tree) * R sum (s + sumBTree tree)) C'`;

val SUM_BTREE_SPEC_def = Define 
  `SUM_BTREE_SPEC a b sum C' tree = SUM_BTREE_SPEC' a b sum (2 * depth tree) C' tree`;

val SUM_BTREE_SPEC_TR_def = Define 
  `SUM_BTREE_SPEC_TR a b sum C' tree = SUM_BTREE_SPEC' a b sum (2 * ldepth tree) C' tree`;

val A1_TAC = 
  STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `t1`)
  \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF]
  \\ Cases_on `depth t1 < depth t2`
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF]
  \\ `depth t1 < SUC (depth t2)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF];

val A2_TAC = 
  STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `t2`)
  \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF]
  \\ Cases_on `depth t1 < depth t2`
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF]
  \\ `depth t2 < SUC (depth t1)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [depth_def,MAX_DEF];
    
val ASSUMPTION1 = (UNDISCH o UNDISCH o prove) (
  ``(!t'. depth t' < depth tree ==> SUM_BTREE_SPEC a b sum C' t') ==>
    (tree = Node(t1,y,t2)) ==> SUM_BTREE_SPEC a b sum C' t1``,A1_TAC);

val ASSUMPTION1_TR = (UNDISCH o UNDISCH o prove) (
  ``(!t'. depth t' < depth tree ==> SUM_BTREE_SPEC_TR a b sum C' t') ==>
    (tree = Node(t1,y,t2)) ==> SUM_BTREE_SPEC_TR a b sum C' t1``,A1_TAC);

val ASSUMPTION2 = (UNDISCH o UNDISCH o prove) (
  ``(!t'. depth t' < depth tree ==> SUM_BTREE_SPEC a b sum C' t') ==>
    (tree = Node(t1,y,t2)) ==> SUM_BTREE_SPEC a b sum C' t2``,A2_TAC);

val ASSUMPTION2_TR = (UNDISCH o UNDISCH o prove) (
  ``(!t'. depth t' < depth tree ==> SUM_BTREE_SPEC_TR a b sum C' t') ==>
    (tree = Node(t1,y,t2)) ==> SUM_BTREE_SPEC_TR a b sum C' t2``,A2_TAC);

val MULT_MAX = prove(
  ``k * MAX m n = MAX (k * m) (k * n)``,
  Cases_on `k`
  \\ SIMP_TAC std_ss [MAX_DEF]
  \\ Cases_on `m < n` \\ ASM_REWRITE_TAC []);



fun mk_var_list 0 ty = listSyntax.mk_nil ty
  | mk_var_list n ty = listSyntax.mk_cons(genvar ty,mk_var_list (n-1) ty);

fun APP_APPEND th list = 
  let 
    val th = MATCH_MP ARM_PROG_APPEND_CODE th
  in RW [APPEND] (SPEC list th) end;

fun APP_MERGE th1 th2 =
  let
    val (_,cs1,_,_,_) = dest_ARM_PROG (concl th1) 
    val (_,cs2,_,_,_) = dest_ARM_PROG (concl th2) 
    val len1 = (length o fst o listSyntax.dest_list) cs1
    val len2 = (length o fst o listSyntax.dest_list) cs2
    val diff = abs (len1 - len2)    
    val list = mk_var_list diff ``:word32``
    val (th1,th2) = if len1 < len2 then (APP_APPEND th1 list,th2) else (th1,APP_APPEND th2 list)
    val (_,cs1,_,_,_) = dest_ARM_PROG (concl th1) 
    val (_,cs2,_,_,_) = dest_ARM_PROG (concl th2) 
    val (i,m) = if len1 < len2 then (match_term cs1 cs2) else (match_term cs2 cs1)
    val (th1,th2) = if len1 < len2 then (INST i (INST_TYPE m th1),th2) else 
                                        (th1,INST i (INST_TYPE m th2))
    val th = MATCH_MP ARM_PROG_MERGE (CONJ th1 th2)
    val th = SIMP_RULE (pure_ss++sep_ss) [UNION_IDEMPOT,UNION_EMPTY] th
  in th end;


val (ARM_SUM_BTREE_PROCEDURE,ARM_SUM_BTREE_PROCEDURE_TR) = let

  val cmp = FST_PROG2 (SET_AM `Imm 0w` (SET_SC `T` `AL` arm_CMP1))
  val cmp = RW [GSYM R30_def] (Q.INST [`x`|->`addr32 x`] cmp)
  val cmp = RW [EVAL ``(w2w (0w:word8)):word32``] cmp
  val cmp = HIDE_STATUS cmp  
  val cmp1 = APP_FRAME `cond (addr32 x = 0w)` cmp
  val cmp2 = APP_FRAME `cond ~(addr32 x = 0w)` cmp

  val mov_pc = SET_SC `T` `EQ` arm_MOV_PC
  val mov_pc = Q.INST [`a`|->`14w`,`x`|->`lr`] mov_pc
  val mov_pc1 = HIDE_POST (FST_PROG2 mov_pc)
  val mov_pc2 = HIDE_POST1 (SND_PROG2 mov_pc)
  
  (* case 1 *)

  val cmp1 = APP_FRAME `R30 14w lr` cmp1
  val th = APP_FRAME `R30 a x` mov_pc1
  val th = MOVE_STAR_RULE `x*y1*y2*z` `z*y1*y2*x` th  
  val th = MATCH_COMPOSE cmp1 th
  val th = RW [addr32_0] th
  val th = APP_FRAME `bt (x,tree) * R sum (s + sumBTree tree)` th
  val th = SIMP_cond bool_ss [AND_CLAUSES] th
  val th = DISCH ``tree = Leaf`` th
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_STRENGTHEN th 
           `R30 a x * ~S * R30 14w lr * bt (x,tree) * R sum s * cond (tree = Leaf)`
    (SIMP_TAC (std_ss++sep_ss) [SEP_IMP_MOVE_COND,bt_def,sumBTree_def]
     \\ CONV_TAC cond_CONV
     \\ SIMP_TAC (std_ss++star_ss) [WORD_ADD_0,SEP_IMP_REFL])
  val c1 = UNDISCH (RW [ARM_PROG_MOVE_COND] th)
  val c1 = APP_FRAME `STACK sp [] n * ~R b` c1
  val c1 = RW [GSYM ARM_PROG_MOVE_COND] (DISCH_ALL c1)
  val c1 = PRE_MOVE_STAR `a*s*lr*t*sum*(sp*b)*c` `a*b*t*sum*sp*s*lr*c` c1
  val c1 = POST_MOVE_STAR `lr*s*a*t*sum*(sp*b)` `b*t*sum*sp*s*lr*a` c1
  val c1 = RW [GSYM R30_def] (HIDE_POST (RW [R30_def] c1))
  val case1 = POST_MOVE_STAR `b*t*sum*sp*s*lr*a` `a*b*t*sum*sp*s*lr` c1
 
  (* case 2 *)

  val th = (RW [STAR_ASSOC] o RW1 [STAR_COMM] o APP_FRAME `R30 a x`) mov_pc2
  val th = MATCH_COMPOSE cmp2 th
  val th = RW [addr32_0] th
  val th = APP_FRAME `bt (x,tree) * R30 14w lr * R sum s` th
  val th = DISCH ``tree = Node (t1,y,t2)`` th
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_STRENGTHEN th 
           `R30 a x * ~S * R30 14w lr * bt (x,tree) * R sum s * cond (tree = Node(t1,y,t2))`
    (SIMP_TAC (std_ss++sep_ss) [SEP_IMP_MOVE_COND,bt_def,sumBTree_def]
     \\ CONV_TAC cond_CONV
     \\ SIMP_TAC (std_ss++star_ss) [WORD_ADD_0,SEP_IMP_REFL])
  val th = UNDISCH (RW [ARM_PROG_MOVE_COND] th)

  (* push on to stack *)

  val th = APP_FRAME `STACK sp xs (SUC (SUC n))` th
  val th = POST1_MOVE_STAR `a*s*(t*lr*sum)*st` `(a*st*s)*(t*lr*sum)` th
  val th' = RW [GSYM R30_def] (Q.INST [`x`|->`addr32 x`] STACK_PUSH)
  val th' = APP_FRAME `bt (x,tree) * R30 14w lr * R sum s` th'
  val th = MATCH_COMPOSE th th'
  val th = POST1_MOVE_STAR `(a*st*s)*(t*lr*sum)` `(lr*st*s)*(t*a*sum)` th
  val th' = RW [GSYM R30_def] (Q.INST [`x`|->`addr32 lr`,`a`|->`14w`] STACK_PUSH)
  val th' = APP_FRAME `bt (x,tree) * R30 a x * R sum s` th'
  val th = MATCH_COMPOSE th th'
  val th = MOVE_STAR_RULE `(lr*st*s)*(t*a*sum)` `(st*s)*(t*a*sum)*lr` th
  val th = HIDE_POST1 (RW [R30_def] th)
  val th = MOVE_STAR_RULE `(st*s)*(t*a*sum)*lr` `(lr*st*s)*(t*a*sum)` (RW [GSYM R30_def] th)
    
  (* open definitions *)

  val th = UNDISCH (SIMP_RULE std_ss [] (DISCH_ALL th))
  val th = APP_FRAME `~ R b` th
  val th = POST1_MOVE_STAR `(lr*st*s)*(t*a*sum)*b` `t*(lr*st*s*a*sum*b)` th
  val case2 = POST1_CONV_RULE (REWRITE_CONV [bt_Node]) th
  val case2 = RW1 [STACK_EXTRACT] case2
  val case2 = Q.INST [`xs`|->`[]`] case2
  val case2 = SIMP_RULE (std_ss++sep_ss) [ms_def,WORD_SUB_ADD,STAR_ASSOC] case2

  (* add *)

  val ldr = SET_AM `RegOff (T,T,F,0w)` (PROG_INST arm_LDR)  
  val ldr = RW [EVAL ``(w2w (0w:word8)):word30``,WORD_ADD_0] ldr
  val ldr = Q.INST [`a`|->`b`,`b`|->`a`,`y`|->`x`,`x`|->`y`] ldr
  val ldr = MOVE_STAR_RULE `x*y*z*q` `y*z*q*x` ldr
  val ldr = RW [ARM_PROG_HIDE_PRE] (Q.GEN `y` ldr)
  val ldr = APP_FRAME `R sum s` ldr
  val ldr = MOVE_STAR_RULE `a*x*s*b*sum` `b*sum*s*a*x` ldr
  val add = PROG_INST (SET_AM `OneReg` arm_ADD2)  
  val add = Q.INST [`a`|->`b`,`b`|->`sum`] add
  val add = APP_FRAME `R30 a z * M z q` add
  val add = MATCH_COMPOSE ldr (RW [STAR_ASSOC] add)
  val add = RW1 [WORD_ADD_COMM] add
  val add = MOVE_STAR_RULE `x1*x2*x3*x4*x5` `x2*x3*x4*x5*x1` add
  val add = Q.INST [`z`|->`y`] (HIDE_POST1 add)

  (* call 1 *)
  
  val ldr = PROG_INST (SET_AM `RegOff (T,T,F,1w)` arm_LDR1)  
  val ldr = RW [EVAL ``(w2w (1w:word8)):word30``] ldr
  val ldr = RW [GSYM R30_def] (Q.INST [`b`|->`a`,`y`|->`x`,`z`|->`addr32 a1`] ldr)
  val th = ASSUME ``ARM_PROCS n (R30 a x * ~R b * bt (x,t1) * R sum s)
                                (~R a * ~R b * bt (x,t1) * R sum (s + sumBTree t1)) C'``
  val th = SPEC_ALL (RW [ARM_PROCS_def] th)
  val th = MOVE_STAR_RULE `a*b*t*sum*sp*s` `a*b*t*sum*s*sp` th
  val th = MATCH_MP ARM_PROC_EXPAND_STACK th
  val th = Q.SPEC `m` th
  val th = MOVE_STAR_RULE `a*b*t*sum*s*sp` `a*b*t*sum*sp*s` th
  val th' = MATCH_MP (RW [GSYM AND_IMP_INTRO] ARM_PROC_CALL) arm_BL
  val th' = Q.INST [`offset`|->`offset1`] th'
  val th = MATCH_MP th' th
  val th = Q.INST [`x`|->`a1`] th
  val th = APP_FRAME `M (x + 1w) (addr32 a1)` th
  val ldr = APP_FRAME `~R b * bt (a1,t1) * R sum s * STACK sp [] (MAX n m) * ~R 14w` ldr
  val call1 = ARRANGE_COMPOSE ldr th

  (* load for call 2 *)

  val ldr1 = PROG_INST (SET_AM `RegOff (T,T,F,1w)` arm_LDR)  
  val ldr1 = RW [EVAL ``(w2w (1w:word8)):word30``] ldr1
  val ldr1 = MOVE_STAR_RULE `a*sp*y*s` `sp*y*s*a` ldr1
  val ldr1 = HIDE_PRE ldr1
  val ldr1 = RW [GSYM R30_def] (Q.INST [`b`|->`13w`,`y`|->`sp`,`z`|->`addr32 x`] ldr1)
  val ldr2 = PROG_INST (SET_AM `RegOff (T,T,F,2w)` arm_LDR1)  
  val ldr2 = RW [EVAL ``(w2w (2w:word8)):word30``] ldr2
  val ldr2 = RW [GSYM R30_def] (Q.INST [`b`|->`a`,`y`|->`x`,`z`|->`addr32 a2`] ldr2)
  val ldr1 = APP_FRAME `M (x + 2w) (addr32 a2)` ldr1  
  val ldr2 = APP_FRAME `R30 13w sp * M (sp + 1w) (addr32 x)` ldr2
  val ldr12 = ARRANGE_COMPOSE ldr1 ldr2
  val ldr12 = APP_FRAME `ms sp [] * blank (sp-1w) n` ldr12  
  val ldr12 = MOVE_STAR_RULE `a*x2*s*(sp*sp1)*(m*b)` `a*x2*s*sp1*(sp*m*b)` ldr12
  val ldr12 = MOVE_STAR_RULE `sp*sp1*s*a*x2*(m*b)` `sp1*s*a*x2*(sp*m*b)` ldr12
  val ldr12 = RW [GSYM STACK_def] ldr12
  val ldr12 = Q.INST [`n`|->`MAX n m`] ldr12

  (* compose: add, call 1 and load for call 2 *)

  val th = FRAME_COMPOSE add (Q.INST [`s`|->`s+y`] call1)
  val add_call1_ldr = FRAME_COMPOSE th ldr12

  (* === proof of simple version === *)

  (* call 2 and load lr into pc *)

  val th = ASSUMPTION2
  val th = SPEC_ALL (RW [SUM_BTREE_SPEC_def,SUM_BTREE_SPEC'_def,ARM_PROCS_def] th)
  val th = MOVE_STAR_RULE `a*b*t*sum*sp*s` `a*b*t*sum*s*sp` th
  val th = MATCH_MP ARM_PROC_EXPAND_STACK th
  val th = Q.SPEC `2 * depth t1` th
  val th = RW [GSYM MULT_MAX] (RW1 [MAX_COMM] th)
  val th = MOVE_STAR_RULE `a*b*t*sum*s*sp` `a*b*t*sum*sp*s` th
  val th' = MATCH_MP (RW [GSYM AND_IMP_INTRO] ARM_PROC_CALL) arm_BL
  val th' = Q.INST [`offset`|->`offset2`] th'
  val th = MATCH_MP th' th
  val th = Q.INST [`x`|->`a2`,`sp`|->`sp -1w-1w`] th
  val call2 = APP_FRAME `M (x + 2w) (addr32 a2)` th

  val ldr = (SET_SC `F` `AL` o SET_AM `RegOff (F,T,T,2w)`) arm_LDR_PC
  val ldr = (HIDE_STATUS o HIDE_POST o FST_PROG2) ldr
  val ldr = Q.INST [`a`|->`13w`,`y`|->`lr`,`x`|->`sp-1w-1w`] ldr
  val lemma = prove(``x-1w-1w+2w=x:word30``,
                    REWRITE_TAC [GSYM WORD_SUB_PLUS,EVAL ``1w+1w:word30``,WORD_SUB_ADD])
  val ldr = RW [EVAL ``(w2w (2w:word8)):word30``,lemma] ldr
  val ldr = APP_FRAME `ms (sp-1w-1w+1w) (addr32 x::xs) * blank (sp - 1w - 1w - 1w) n` ldr
  val ldr = MOVE_STAR_RULE `sp*m*s*(mss*b)` `sp*(m*mss)*b*s` ldr
  val ldr = RW [GSYM ms_def,GSYM STACK_def] ldr
  val ldr = RW [ms_def] ldr
  val ldr = MOVE_STAR_RULE `sp*(m*(mm*mss))*b*s` `sp*m*mss*b*s*mm`  ldr
  val ldr = HIDE_POST ldr
  val ldr = RW [WORD_SUB_ADD] ldr
  val ldr = MOVE_STAR_RULE `sp*m*mss*b*s*mm` `sp*mss*(mm*(m*b))*s` ldr
  val ldr = RW [GSYM blank_def,GSYM STACK_def] ldr
  val ldr = Q.INST [`n`|->`2 * (MAX (depth t1) (depth t2))`] ldr
  val ldr = RW [DECIDE ``SUC (SUC (2 * m)) = 2 * SUC m``] ldr

  val ldr = RW1 [STACK_EXTRACT] (Q.INST [`xs`|->`[]`] ldr)
  val ldr = POST_CONV_RULE (SIMP_CONV (bool_ss++sep_ss) [ms_def]) ldr
  val th = FRAME_COMPOSE th ldr
  val th = APP_FRAME 
     `M x y * M (x + 1w) (addr32 a1) * bt(a1,t1) * cond ~(x = 0w) * M (x + 2w) (addr32 a2)` th
  val th = APP_WEAKEN th 
    `bt(x,Node(t1,y,t2)) * (~R a * ~R b * STACK sp [] (2 * SUC (MAX (depth t1) (depth t2))) * 
     R sum (s+sumBTree t2) * ~S * ~R 14w)` 
       (REWRITE_TAC [bt_Node] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS]
        \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `a1` \\ Q.EXISTS_TAC `a2` 
        \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = RW [STAR_ASSOC] th
  val ret1 = MOVE_STAR_RULE `tree*a*b*stack*sum*s*lr` `a*b*tree*sum*stack*s*lr` th

  (* finish proof 1 *)

  val th1 = Q.INST [`sp`|->`sp-1w-1w`,`n`|->`2 * (depth t1)`,`m`|->`2 * (depth t2)`] add_call1_ldr
  val th1 = SIMP_RULE (bool_ss++sep_ss) [WORD_SUB_ADD,GSYM MULT_MAX] th1
  val asm = Q.SPECL [`a1`,`s+y`] (RW [SUM_BTREE_SPEC_def,SUM_BTREE_SPEC'_def] ASSUMPTION1)
  val th1 = Q.SPEC `t2` (MATCH_MP (DISCH_ALL (Q.GEN `t2` th1)) asm)
  val th2 = Q.INST [`s`|->`s + y + sumBTree t1`] ret1  
  val th2 = SIMP_RULE (bool_ss++sep_ss) [ms_def,WORD_SUB_ADD] th2
  val th12 = FRAME_COMPOSE th1 th2
  val lemma = prove(``s + y + sumBTree t1 + sumBTree t2 = s + sumBTree (Node (t1,y,t2))``,
                    REWRITE_TAC [sumBTree_def] \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM])
  val th12 = RW [lemma] th12
  val th12 = EXISTS_PRE `a2` th12
  val th12 = EXISTS_PRE `a1` th12
  val c2 = Q.INST [`n`|->`2 * (MAX (depth t1) (depth t2))`] case2
  val c2 = RW [DECIDE ``SUC (SUC (2 * m)) = 2 * SUC m``] c2  
  val th = ARRANGE_COMPOSE c2 th12
  val th = Q.INST [`offset1`|->`0w-9w`,`offset2`|->`0w-12w`] th
  val rw1 = EVAL ``4w + (2w + (1w + (sw2sw (0w - 9w:word24) + 2w))):word30``  
  val rw2 = EVAL ``4w + (6w + (sw2sw (0w - 12w:word24) + 2w)):word30``  
  val th = RW [rw1,rw2,setADD_0,UNION_IDEMPOT] th

  val th = DISCH ``SUC (MAX (depth t1) (depth t2)) = depth (Node (t1,y,t2))`` th
  val th = SIMP_RULE std_ss [] th
  val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [depth_def])) th
  val th = SIMP_RULE std_ss [] th

  val th = DISCH ``tree = Node (t1,y,t2)`` th
  val th = RW1 [EQ_SYM_EQ] th
  val th = SIMP_RULE bool_ss [] th
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = PRE_MOVE_STAR `a*s*lr*t*sum*sp*b*c` `a*b*t*sum*sp*s*lr*c` th

  val th = APP_MERGE (Q.INST [`n`|->`2*depth tree`] case1) th 
  val th = RW [STAR_OVER_DISJ,SEP_cond_CLAUSES] th
  val th = RW [ARM_PROG_MOVE_COND] th
  val th' = CONV_RULE (RAND_CONV (UNBETA_CONV ``tree:BTree``)) th
  val th' = (Q.GEN `t1` o Q.GEN `y` o Q.GEN `t2`) th'

  val lemma = prove(
    ``(!t1 x t2. (tree = Leaf) \/ (Node (t1,x,t2) = tree) ==> P tree) ==> P tree``,
    Cases_on `tree` \\ SIMP_TAC std_ss [] \\ Cases_on `p` \\ Cases_on `r` \\ METIS_TAC [])
  
  val th' = BETA_RULE (MATCH_MP lemma th')
  val th' = RW1 [ARM_PROG_EXTRACT_CODE] th'
  val th' = RW [GSYM ARM_PROC_THM] (Q.GEN `lr` th')
  val th' = RW [GSYM ARM_PROCS_def] (Q.GEN `sp` th')
  val th' = RW [GSYM SUM_BTREE_SPEC_def,GSYM SUM_BTREE_SPEC'_def] (Q.GEN `x` (Q.GEN `s` th'))
  val th' = RW1 [INSERT_SING_UNION] th'
  val th' = Q.GEN `tree` (Q.GEN `C'` (DISCH_ALL th'))
  val th' = MATCH_MP ARM_PROC_RECURSION th'
  val th' = Q.SPEC `tree` th'  
  val rws = [EVAL ``(w2w (0w:word8)):word12 << 2``,
             EVAL ``(w2w (1w:word8)):word12 << 2``,
             EVAL ``(w2w (2w:word8)):word12 << 2``]
  val result = RW rws th'

  (* === proof of tail-rec version === *)

  val ARM_PROG_COMPOSE_0 = prove(
    ``ARM_PROG P cs {} SEP_F {(P',pcADD k)} ==> 
      ARM_PROG (P'' * P') [] C SEP_F Z ==>
      ARM_PROG (P'' * P) cs (setADD k C) SEP_F (setADD k Z)``,
    STRIP_TAC
    \\ POP_ASSUM (ASSUME_TAC o RW1 [STAR_COMM] o APP_FRAME `P''`)
    \\ FULL_SIMP_TAC bool_ss [ARM_PROG_THM,ARM_GPROG_FALSE_POST,ARM_GPROG_EMPTY_CODE] 
    \\ REPEAT STRIP_TAC
    \\ (CONV_TAC o RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [INSERT_SING_UNION])
    \\ (ASSUME_TAC o GEN_ALL o Q.SPECL [`Y`,`{}`,`X`,`C`,`C'`,`{}`,`Z`]) ARM_GPROG_COMPOSE
    \\ FULL_SIMP_TAC bool_ss [UNION_EMPTY,UNION_IDEMPOT]
    \\ PAT_ASSUM ``!Z:'a. b`` (MATCH_MP_TAC)
    \\ Q.EXISTS_TAC `setADD k {(P'' * P',I)}` 
    \\ STRIP_TAC
    THEN1 ASM_SIMP_TAC (bool_ss++COMPOSE_ss) 
            [prove(``I o f = f``,SRW_TAC [] [FUN_EQ_THM]),setADD_CLAUSES]
    \\ REWRITE_TAC [setADD_def]
    \\ METIS_TAC [ARM_GPROG_SHIFT])

  val th1 = RW [MAX_IDEM] (Q.INST [`m`|->`n`] add_call1_ldr)
  val th1 = Q.INST [`sp`|->`sp-1w-1w`,`n`|->`2 * (ldepth t1)`] th1
  val th1 = SIMP_RULE (bool_ss++sep_ss) [WORD_SUB_ADD,GSYM MULT_MAX] th1
  val asm = Q.SPECL [`a1`,`s+y`] (RW [SUM_BTREE_SPEC_TR_def,SUM_BTREE_SPEC'_def] ASSUMPTION1_TR)
  val th1 = MATCH_MP (DISCH_ALL th1) asm
  val th1 = PRE_MOVE_STAR `sum*s*a*x*b*x1*t1*sp*lr*sp1*x2` 
                          `sum*s*a*x*b*x1*t1*lr*sp1*x2*sp` th1
  val th1 = POST1_MOVE_STAR `a*x2*s*sp1*sp*b*t1*sum*lr*x1*x` 
                            `a*x2*s*sp1*b*t1*sum*lr*x1*x*sp` th1
  val th1 = Q.SPEC `2 * ldepth t2 - 2` (MATCH_MP ARM_PROG_EXPAND_STACK th1)
  val th1 = RW [GSYM WORD_SUB_PLUS,EVAL ``1w+1w:word30``] th1

  val ldr = MULTI_POP_STACK  
  val ldr = Q.SPECL [`addr32 lr`,`[addr32 x]`,`14w`,`2 * (ldepth t1)`,`2 * (ldepth t2)`] ldr
  val ldr = SIMP_RULE std_ss [LENGTH,DECIDE ``2 * m + 2 = 2 * SUC m``] ldr
  val ldr = RW [ms_def,emp_STAR,STAR_ASSOC,GSYM R30_def] (RW1 [STACK_EXTRACT] ldr)
  val ldr = RW [GSYM MULT_MAX] ldr
  val ldr = DISCH ``MAX (SUC (ldepth t1)) (ldepth t2) = ldepth (Node(t1,y,t2))`` ldr
  val ldr = SIMP_RULE bool_ss [] ldr
  val ldr = RW [] (CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [ldepth_def]))) ldr)
  val lemma = prove(``x-2w+1w = x-1w:word30``,
                    REWRITE_TAC [(GSYM o EVAL) ``1w+1w:word30``,WORD_SUB_PLUS,WORD_SUB_ADD])
  val ldr = RW [lemma] ldr

  val c2 = RW [SUM_BTREE_SPEC_TR_def,SUM_BTREE_SPEC'_def] ASSUMPTION2_TR
  val c2 = Q.SPECL [`a2`,`s + y + sumBTree t1`] c2
  val c2 = Q.SPEC `2 * SUC (ldepth t1)` (MATCH_MP ARM_PROCS_EXPAND_STACK c2)
  val c2 = RW [GSYM MULT_MAX] (RW1 [MAX_COMM] c2)
  val c2 = DISCH ``MAX (SUC (ldepth t1)) (ldepth t2) = ldepth (Node(t1,y,t2))`` c2
  val c2 = SIMP_RULE bool_ss [] c2
  val c2 = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [ldepth_def]))) c2
  val c2 = Q.SPECL [`sp`,`lr`] (RW [ARM_PROCS_def,ARM_PROC_THM] c2)
  val c2 = APP_FRAME `M x y * M (x+1w) (addr32 a1) * M (x+2w) (addr32 a2) * bt (a1,t1) * cond ~(x = 0w)` c2
  val c2 = APP_WEAKEN c2 `bt (x,Node(t1,y,t2)) * 
       (~R a * ~R b * R sum (s + sumBTree(Node(t1,y,t2))) *
        STACK sp [] (2 * ldepth (Node (t1,y,t2))) * ~S * ~R 14w)`
    (SIMP_TAC std_ss [bt_Node,SEP_IMP_def,SEP_EXISTS,sumBTree_def]
     \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `a1` \\ Q.EXISTS_TAC `a2`
     \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_COMM WORD_ADD_ASSOC])
  val c2 = POST_MOVE_STAR `t*(a*b*sum*sp*s*lr)` `a*b*t*sum*sp*s*lr` c2
  val b = (HIDE_STATUS o HIDE_POST o SET_SC `F` `AL`) arm_B
  val b = MATCH_MP ARM_PROG_COMPOSE_0 b 
  val c2 = PRE_MOVE_STAR `a*b*t2*sum*sp*s*lr*x*a1*a2*t1*c` 
                         `a*b*t2*sum*sp*lr*x*a1*a2*t1*c*s` (RW [STAR_ASSOC] c2)
  val c2 = RW [setADD_CLAUSES,pcSET_ABSORB] (MATCH_MP b c2)

  val c2 = FRAME_COMPOSE ldr c2
  val c2 = FRAME_COMPOSE th1 c2
  val call2 = EXISTS_PRE `a2` c2
  val call2 = EXISTS_PRE `a1` call2

  val c2 = RW [GSYM WORD_SUB_PLUS,EVAL ``1w+1w:word30``] case2
  val c2 = Q.INST [`n`|->`MAX (2 * ldepth t1) (2 * ldepth t2 - 2)`] c2
  val c2_call2 = ARRANGE_COMPOSE c2 call2
  val lemma = prove(
    ``SUC (SUC (MAX (2 * m) (2 * n - 2))) = 2 * (MAX (SUC m) n)``,
    SRW_TAC [] [MAX_DEF] \\ DECIDE_TAC)
  val th = RW [lemma] c2_call2
  val th = DISCH ``MAX (SUC (ldepth t1)) (ldepth t2) = ldepth (Node(t1,y,t2))`` th
  val th = SIMP_RULE bool_ss [] th
  val th = RW [] (CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [ldepth_def]))) th)
  val th = PAT_DISCH ``tree = Node(t1,y,t2)`` th
  val th = CONV_RULE (RATOR_CONV (RAND_CONV (SYM_CONV))) th
  val th = SIMP_RULE std_ss [lemma] th
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = Q.INST [`offset1`|->`0w-9w`,`offset`|->`0w-13w`] th
  val rw1 = EVAL ``4w + (2w + (1w + (sw2sw (0w - 9w:word24) + 2w))):word30``
  val rw2 = EVAL ``4w + (6w + (1w + (sw2sw (0w - 13w:word24) + 2w))):word30``
  val th = RW [rw1,rw2,setADD_0,UNION_IDEMPOT] th
  val cNode = PRE_MOVE_STAR `a*s*lr*t*sum*sp*b*c` `a*b*t*sum*sp*s*lr*c` th
  val cLeaf = Q.INST [`n`|->`2 * ldepth tree`] case1
  
  val cTree = APP_MERGE cLeaf cNode
  val th = RW [STAR_OVER_DISJ,SEP_cond_CLAUSES] cTree
  val th = RW [ARM_PROG_MOVE_COND] th
  val th' = CONV_RULE (RAND_CONV (UNBETA_CONV ``tree:BTree``)) th
  val th' = (Q.GEN `t1` o Q.GEN `y` o Q.GEN `t2`) th'

  val lemma = prove(
    ``(!t1 x t2. (tree = Leaf) \/ (Node (t1,x,t2) = tree) ==> P tree) ==> P tree``,
    Cases_on `tree` \\ SIMP_TAC std_ss [] \\ Cases_on `p` \\ Cases_on `r` \\ METIS_TAC [])
  
  val th' = BETA_RULE (MATCH_MP lemma th')
  val th' = RW1 [ARM_PROG_EXTRACT_CODE] th'
  val th' = RW [GSYM ARM_PROC_THM] (Q.GEN `lr` th')
  val th' = RW [GSYM ARM_PROCS_def] (Q.GEN `sp` th')
  val th' = RW [GSYM SUM_BTREE_SPEC_TR_def,GSYM SUM_BTREE_SPEC'_def] (Q.GEN `x` (Q.GEN `s` th'))
  val th' = RW1 [INSERT_SING_UNION] th'
  val th' = Q.GEN `tree` (Q.GEN `C'` (DISCH_ALL th'))
  val th' = MATCH_MP ARM_PROC_RECURSION th'
  val th' = Q.SPEC `tree` th'  
  val rws = [EVAL ``(w2w (0w:word8)):word12 << 2``,
             EVAL ``(w2w (1w:word8)):word12 << 2``,
             EVAL ``(w2w (2w:word8)):word12 << 2``,
             EVAL ``(2w:word12) << 2``]
  val result_TR = RW rws th'
 
  val rw = RW [SUM_BTREE_SPEC_TR_def,SUM_BTREE_SPEC_def,SUM_BTREE_SPEC'_def]

in (rw result,rw result_TR) end;
  

(* export ready examples *)

val _ = save_thm("ARM_FAC1_PROGRAM",ARM_FAC1_PROGRAM);
val _ = save_thm("ARM_FAC_PROGRAM",ARM_FAC_PROGRAM);
val _ = save_thm("ARM_GCD_PROGRAM",ARM_GCD_PROGRAM);
val _ = save_thm("ARM_SUM_BTREE_PROCEDURE",ARM_SUM_BTREE_PROCEDURE);
val _ = save_thm("ARM_SUM_BTREE_PROCEDURE_TR",ARM_SUM_BTREE_PROCEDURE_TR);

(*

val show_code = ref true

show_code := false

fun print_ARM_PROG sys (gl,gc,gr) d pps t = 
  let
    val _ = if !show_code then raise term_pp_types.UserPP_Failed else d
    open Portable term_pp_types
    val (P,cs,C,Q,Z) = dest_ARM_PROG t
    val dgrav = Prec (29,"")
    val dgravs = (dgrav,dgrav,dgrav)
  in
    begin_block pps INCONSISTENT 0;
    add_string pps "ARM_PROG";
    add_break pps (1,0);
    sys dgravs (d - 1) P;
    add_break pps (1,0);
    add_string pps "<code>";
    add_break pps (1,0);
    sys dgravs (d - 1) Q;
    add_break pps (1,0);
    sys (dgrav,dgrav,gr) (d - 1) Z;
    end_block pps
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

temp_add_user_printer ({Tyop = "bool", Thy = "min"}, print_ARM_PROG);

ARM_GCD_PROGRAM;
ARM_PROG_FRAME;

*)

val ARM_PROG_PUSH_COND = prove(
  ``ARM_PROG (P * cond c) cs C Q Z ==> ARM_PROG (P * cond c) cs C (Q * cond c) Z``,
  SIMP_TAC (std_ss++sep_ss) [ARM_PROG_MOVE_COND]);

val PUSH_COND = MATCH_MP ARM_PROG_PUSH_COND;


val DIV_BOUNDS = prove(
  ``!k. 0 < k ==> !m n. (m DIV k = n) = (n*k <= m /\ m < n*k+k)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  THEN1 (METIS_TAC [DIVISION,LESS_EQ_ADD,LT_ADD_LCANCEL])
  \\ `?l. m = n*k+l` by METIS_TAC [LESS_EQ_EXISTS]  
  \\ FULL_SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC std_ss [DIV_MULT,GSYM LT_ADD_LCANCEL]);

val BIT_32_EQ_LE = prove( 
  ``!x:word32 y:word32. BIT 32 (w2n x + w2n y) = 2**32 <= w2n x + w2n y``,
  Cases_word
  \\ Cases_word
  \\ REWRITE_TAC [BIT_def,BITS_def,MOD_2EXP_def,DIV_2EXP_def]
  \\ FULL_SIMP_TAC std_ss [w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [dimword_def]
  \\ `0 < 2 /\ 0 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [DIV_MOD_MOD_DIV]
  \\ `n + n' < 8589934592` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LESS_MOD,DIV_BOUNDS]);
  
val POST_LEMMA = prove(
  ``!x:word32 y:word32. 
        (if BIT 32 (w2n x + w2n y) then ~0w else x + y) =
        n2w (MIN (w2n x + w2n y) (2**32-1))``,
  Cases_word \\ Cases_word
  \\ ASM_SIMP_TAC std_ss [w2n_n2w,BIT_32_EQ_LE,EVAL ``~(0w:word32)``,word_add_n2w]
  \\ REWRITE_TAC [GSYM (EVAL ``SUC 4294967295``),GSYM LESS_EQ,MIN_DEF]
  \\ Cases_on `4294967295 < n + n'`
  \\ ASM_REWRITE_TAC [MIN_DEF]
  THEN1 (`~(n + n' < 4294967295)` by DECIDE_TAC \\ ASM_REWRITE_TAC [])
  \\ Cases_on `n + n' < 4294967295` \\ ASM_REWRITE_TAC []
  \\ `n + n' = 4294967295` by DECIDE_TAC \\ ASM_REWRITE_TAC []);

val cut_add_def = Define `cut_add x y = n2w (MIN (w2n x + w2n y) (2 ** 32 - 1))`;

val CUT_ADD_PROGRAM = let

  val adds = (SIMP_RULE (srw_ss()++sep_ss) [] o SET_SC `T` `AL`) arm_ADD2
  val adds = FST_PROG2 (SET_AM `OneReg` adds)
  val adds = Q.INST [`a`|->`0w`,`b`|->`1w`] adds
  val adds1 = APP_FRAME `cond ~(BIT 32 (w2n (x:word32) + w2n (y:word32)))` adds
  val adds2 = APP_FRAME `cond (BIT 32 (w2n (x:word32) + w2n (y:word32)))` adds

  val movcc = (SIMP_RULE (srw_ss()++sep_ss) [] o SET_SC `F` `CC`) arm_MOV2
  val movcc = Q.INST [`a`|->`1w`,`b`|->`0w`] (SET_AM `OneReg` movcc)
  val movcc1 = PUSH_COND (FST_PROG2 movcc)
  val movcc1 = MOVE_STAR_RULE `b*a*s*c` `a*b*s*c` movcc1
  val movcc2 = RW [] (PUSH_COND (SND_PROG2 movcc))
  val movcc2 = RW [STAR_ASSOC] (RW1 [STAR_COMM] (APP_FRAME `R 0w x * R 1w y` movcc2))
    
  val mvncs = (SIMP_RULE (srw_ss()++sep_ss) [] o SET_SC `F` `CS`) arm_MVN1
  val mvncs = (Q.INST [`a`|->`0w`] o SET_AM `Imm 0w`) mvncs
  val mvncs = SIMP_RULE std_ss [EVAL ``(w2w (0w:word8)):word32``] mvncs
  val mvncs1 = HIDE_POST1 (SND_PROG2 mvncs)
  val mvncs1 = APP_FRAME `R 0w x * R 1w y` mvncs1
  val mvncs1 = RW [STAR_ASSOC] (RW1 [STAR_COMM] mvncs1)
  val mvncs2 = FST_PROG2 mvncs
  val mvncs2 = APP_FRAME `R 1w y` (HIDE_POST1 (FST_PROG2 mvncs))
  val mvncs2 = POST1_MOVE_STAR `x*y*z` `x*z*y` mvncs2
  val mvncs2 = PRE_MOVE_STAR `x*y*c*z` `x*z*y*c` mvncs2

  val th1 = MATCH_COMPOSE adds1 movcc1
  val th2 = MATCH_COMPOSE adds2 movcc2
  val th1 = MATCH_COMPOSE th1 mvncs1
  val th2 = MATCH_COMPOSE th2 mvncs2

  val lemma = prove(
    ``ARM_PROG (P * cond ~c) cs C (Q * Q' y) Z ==>
      ARM_PROG (P * cond c) cs C (Q * Q' x) Z ==>
      ARM_PROG P cs C (Q * Q' (if c then x else y)) Z``,  
    Cases_on `c` \\ SIMP_TAC (std_ss++sep_ss) [])
    
  val th1 = POST1_MOVE_STAR `x*y*s` `y*s*x` th1
  val th2 = POST1_MOVE_STAR `x*y*s` `y*s*x` th2
  val th = MATCH_MP (MATCH_MP lemma th1) th2
  val th = POST1_MOVE_STAR `y*s*x` `x*y*s` th
  val th = HIDE_STATUS (RW [POST_LEMMA] th)
  val th = RW [GSYM cut_add_def] th

  val ret = (SIMP_RULE (srw_ss()++sep_ss) [] o SET_SC `T` `AL`) arm_MOV_PC
  val ret = (HIDE_STATUS o HIDE_POST o FST_PROG2) ret
  val ret = Q.INST [`a`|->`14w`,`x`|->`lr`] ret
  val ret = RW1 [STAR_COMM] ret
  val ret = APP_FRAME `R 0w x * R 1w y` ret
  val ret = RW [STAR_ASSOC] (RW1 [STAR_COMM] ret)
  val th = APP_FRAME `R30 14w lr` th

  val th = MATCH_COMPOSE th ret
  val th = RW1 [ARM_PROG_EXTRACT_CODE] th
  val th = RW [GSYM ARM_PROC_THM] (Q.GEN `lr` th)    

in th end;


(* ----------------------------------------------------------------------------- *)
(* Instantiation of STM and LDM instructions                                     *)
(* ----------------------------------------------------------------------------- *)

val th = SET_AM `am4_FA F` arm_STM
val th = Q.INST [`xs`|->`[(b1,y1);(b2,y2);(b3,y3);(b4,y4)]`] th
val th = REWRITE_RULE  [blank_ms_def,LENGTH,ADDR_MODE4_ADDR_def,ADDR_MODE4_ADDR'_def,
              ADDR_MODE4_WB'_def,ADDR_MODE4_UP_def,MAP,ADDR_MODE4_WB_def,
              ADDR_MODE4_wb_def,xR_list_def,STAR_ASSOC] th
val th = REWRITE_RULE [ADD1,GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_ADD] th
val th = SIMP_RULE arith_ss [GSYM WORD_SUB_PLUS,word_add_n2w,WORD_SUB_RZERO] th
val th = SIMP_RULE (std_ss++sep_ss) [MAP,xR_list_def,STAR_ASSOC,ADDR_MODE4_CMD_def,GSYM WORD_ADD_ASSOC,word_add_n2w] th


val _ = export_theory();
