
(*
  val armDir = concat Globals.HOLDIR "/examples/elliptic/arm";
  val yaccDir = concat Globals.HOLDIR "/tools/mlyacc/mlyacclib";
  loadPath := !loadPath @ [armDir,yaccDir];
  quietdec := true;
*)

open HolKernel boolLib bossLib;

open pred_setTheory res_quanTheory wordsTheory arithmeticTheory;
open arm_rulesTheory arm_rulesLib arm_evalTheory armTheory instructionTheory; 
open bsubstTheory listTheory rich_listTheory pairTheory sortingTheory;
open relationTheory;

open set_sepTheory set_sepLib progTheory arm_progTheory;

val _ = new_theory "arm_inst";

(*
  quietdec := false;
*)


(* ----------------------------------------------------------------------------- *)
(* Setting the environment                                                       *)
(* ----------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val ERROR = mk_HOL_ERR "";

val PAIR_EQ = pairTheory.PAIR_EQ;

val RW = REWRITE_RULE;
val UD_ALL = UNDISCH_ALL o RW [GSYM AND_IMP_INTRO];

val INSERT_UNION_COMM = prove(
  ``!x s t. (x INSERT s) UNION t = x INSERT (s UNION t)``,
  ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ REWRITE_TAC [UNION_ASSOC]);

val SET_APPEND_ss = rewrites [INSERT_UNION_COMM,UNION_EMPTY];

fun can_match x y = can (uncurry match_term) (x,y);
fun subst_fresh x = subst [x |-> genvar (type_of x)];

val comb1 = fst o dest_comb;
val comb2 = snd o dest_comb;
val binop1 = comb2 o comb1;
val binop2 = comb2;

val IF_DISTRIB_LEFT = prove(
  ``(if b then f x else f x') = f (if b then x else x')``,SRW_TAC [] []);

val IF_DISTRIB_RIGHT = prove(
  ``(if b then f x else g x) = (if b then f else g) x``,SRW_TAC [] []);

val PUSH_IF_ss = rewrites [IF_DISTRIB_LEFT,IF_DISTRIB_RIGHT];


(* ----------------------------------------------------------------------------- *)
(* IMP_ARM_RUN lemma                                                             *)
(* ----------------------------------------------------------------------------- *)
	
val IMP_ARM_RUN1 = prove(
  ``!x P Q.
      (!t s. t SUBSET arm2set s /\ P t ==> (t = arm2set' x s)) /\
        (!s.
           P (arm2set' x s) ==>
           (arm2set'' x s = arm2set'' x (NEXT_ARM_MEM s)) /\
           Q (arm2set' x (NEXT_ARM_MEM s))) ==>
      ARM_RUN P Q``,
  `!s. NEXT_ARM_MEM s = STATE_ARM_MEM (SUC 0) s` by REWRITE_TAC[STATE_ARM_MEM_def]
  \\ ASM_REWRITE_TAC[]
  \\ METIS_TAC[IMP_ARM_RUN]);


(* ----------------------------------------------------------------------------- *)
(* Define a few naming conventions                                               *)
(* ----------------------------------------------------------------------------- *)

val default_Regv = [``15w:word4``,``R1:word4``,``R2:word4``,``R3:word4``,``R4:word4``,``R5:word4``];
val default_Regx = [``p:word32``,``x1:word32``,``x2:word32``,``x3:word32``,``x4:word32``,``x5:word32``];
val default_Memv = [``M1:word30``,``M2:word30``,``M3:word30``];
val default_Memx = [``m1:word32``,``m2:word32``,``m3:word32``];
val default_Status = ``(sN:bool,sZ:bool,sC:bool,sV:bool)``;
val default_Undef = ``undef_value:bool``;
val default_Rest = ``rest_value:arm_mem_state``;
val default_Cond = ``cond_value:bool``;
    
val default_Regs = zip default_Regv default_Regx
val default_Mems = zip default_Memv default_Memx

fun take 0 xs = []
  | take n [] = []
  | take n (x::xs) = x::take (n-1) xs;


(* ----------------------------------------------------------------------------- *)
(* Function for expanding arm2set'                                               *)
(* ----------------------------------------------------------------------------- *)

fun mk_Regset n =
  let 
    fun mk_default_set [] = ``EMPTY:word4 set``
      | mk_default_set (r::rs) = 
          mk_comb (subst [``x:word4``|->r] ``$INSERT (x:word4)``,mk_default_set rs)
  in
    mk_default_set (take n default_Regv)
  end;

fun mk_Memset n =
  let 
    fun mk_default_set [] = ``EMPTY:word30 set``
      | mk_default_set (r::rs) = 
          mk_comb (subst [``x:word30``|->r] ``$INSERT (x:word30)``,mk_default_set rs)
  in
    mk_default_set (take n default_Memv)
  end;

fun bool2term b = if b then ``T`` else ``F``;

val Reg_CLAUESES = prove(
  ``!s x. ({Reg a (reg a s) |a| a IN {}} = {}) /\ 
          ({Reg a (reg a s) |a| a IN (x INSERT xs)} = 
           Reg x (reg x s) INSERT {Reg a (reg a s) |a| a IN xs})``,
  SRW_TAC [] [EXTENSION,GSPECIFICATION] \\ METIS_TAC []);

val Mem_CLAUESES = prove(
  ``!s x. ({Mem a (mem a s) |a| a IN {}} = {}) /\ 
          ({Mem a (mem a s) |a| a IN (x INSERT xs)} = 
           Mem x (mem x s) INSERT {Mem a (mem a s) |a| a IN xs})``,
  SRW_TAC [] [EXTENSION,GSPECIFICATION] \\ METIS_TAC []);

fun expand_arm2set' (rs,ms,st,ud,rt) =
  let
    val vs = [mk_Regset rs,mk_Memset ms,bool2term st,bool2term ud,bool2term rt]
    val th = SPECL vs arm2set'_def
    val th = SIMP_RULE bool_ss [Reg_CLAUESES,Mem_CLAUESES] th
    val th = SIMP_RULE (bool_ss++SET_APPEND_ss) [] th
  in
    GSYM th
  end;

fun INTRO_arm2set' x = PURE_REWRITE_RULE [expand_arm2set' x];

(* debug:
   expand_arm2set' (3,2,true,true,false)
*)


(* ----------------------------------------------------------------------------- *)
(* Produce theorems to satisfy "cond 1" of IMP_ARM_RUN1                           *)
(* ----------------------------------------------------------------------------- *)

val SET_REQ_TAC =
  SRW_TAC [] [arm2set_def,SUBSET_DEF,one_def,IN_INSERT,cond_def]
  \\ POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [IN_INSERT,NOT_IN_EMPTY])
  \\ ASM_REWRITE_TAC [];

val SET_REQ_emp = prove(
  ``!t. t SUBSET (arm2set s) /\ emp t ==> (t = {})``,METIS_TAC [emp_def]);

val SET_REQ_Reg = prove(
  ``!x y t.  t SUBSET (arm2set s) /\ one (Reg x y) t ==> (t = { Reg x (reg x s) })``,
  SET_REQ_TAC);

val SET_REQ_Mem = prove(
  ``!x y t. t SUBSET (arm2set s) /\ one (Mem x y) t ==> (t = { Mem x (mem x s) })``,
  SET_REQ_TAC);

val SET_REQ_Status = prove(
  ``!x t. t SUBSET (arm2set s) /\ one (Status x) t ==> (t = { Status (status s) })``,
  SET_REQ_TAC);

val SET_REQ_Undef = prove(
  ``!x t. t SUBSET (arm2set s) /\ one (Undef x) t ==> (t = { Undef (s.undefined) })``,
  SET_REQ_TAC);

val SET_REQ_Rest = prove(
  ``!x t. t SUBSET (arm2set s) /\ one (Rest x) t ==> (t = { Rest (owrt_visible s) })``,
  SET_REQ_TAC);
  
val SET_REQ_Cond = prove(
  ``!x t. t SUBSET (arm2set s) /\ cond x t ==> (t = {})``,
  SET_REQ_TAC);

val SET_REQ_COMPOSE = prove(
  ``!P Q x1 x2. 
       (!t. t SUBSET (arm2set s) /\ P t ==> (t = x1)) /\
       (!t. t SUBSET (arm2set s) /\ Q t ==> (t = x2)) ==>
       (!t. t SUBSET (arm2set s) /\ (P * Q) t ==> (t = x1 UNION x2))``,
  REWRITE_TAC [STAR_def,SPLIT_def] \\ BETA_TAC
  \\ REPEAT STRIP_TAC
  \\ `(u = x1) /\ (v = x2)` by METIS_TAC [UNION_SUBSET,SUBSET_TRANS]
  \\ METIS_TAC []);

fun set_req_compose th1 th2 = 
  SIMP_RULE (bool_ss++SET_APPEND_ss) [] (MATCH_MP SET_REQ_COMPOSE (CONJ th1 th2));

fun set_req_compose_list g xs =
  let
    fun f [] th = RW [emp_STAR,GSYM CONJ_ASSOC,STAR_ASSOC] (SPEC_ALL th) 
      | f (x::xs) th = f xs (set_req_compose th (g x))
  in
    f xs SET_REQ_emp
  end;

fun set_req_Reg n = map (fn (x,y) => SPECL [x,y] SET_REQ_Reg) (take n default_Regs);
fun set_req_Mem n = map (fn (x,y) => SPECL [x,y] SET_REQ_Mem) (take n default_Mems);

val set_req_Status = SPEC default_Status SET_REQ_Status;
val set_req_Undef = SPEC default_Undef SET_REQ_Undef;
val set_req_Rest = SPEC default_Rest SET_REQ_Rest;
val set_req_Cond = SPEC default_Cond SET_REQ_Cond;

fun mk_set_req (rs,ms,st,ud,rt) =
  let 
    val ys = set_req_Reg rs @ set_req_Mem ms
    val ys = if st then ys @ [set_req_Status] else ys
    val ys = if ud then ys @ [set_req_Undef] else ys
    val ys = if rt then ys @ [set_req_Rest] else ys
    val ys = ys @ [set_req_Cond]
    val th = set_req_compose_list I ys
    val th = RW [emp_STAR] th
  in
    INTRO_arm2set' (rs,ms,st,ud,rt) th
  end;

(* debug:
   mk_set_req (2,2,true,true,false)
*)
  

(* ----------------------------------------------------------------------------- *)
(* Produce theorems to give implied inequalities                                 *)
(* ----------------------------------------------------------------------------- *)

fun IMP_NEQ_PROVE tm = (Q.GEN `Q` o UNDISCH) (prove(tm, 
  REWRITE_TAC [STAR_def,SPLIT_def,one_def,DISJOINT_DEF,WD_ARM_def,WD_Reg_def,WD_Mem_def,SUBSET_DEF]
  \\ REWRITE_TAC [IN_INTER,IN_INSERT,NOT_IN_EMPTY,IN_UNION,EXTENSION] \\ BETA_TAC 
  \\ METIS_TAC [WD_Reg_def,WD_ARM_def]));

val IMP_NEQ_Reg1 = IMP_NEQ_PROVE
  ``WD_ARM t ==> { Reg 15w (reg 15w s) } SUBSET t /\ (one (Reg 15w p) * Q) t ==> T``;

val IMP_NEQ_Reg2 = IMP_NEQ_PROVE
  ``WD_ARM t ==> { Reg 15w (reg 15w s); Reg R1 (reg R1 s) } SUBSET t /\ 
    (one (Reg 15w p) * one (Reg R1 x1) * Q) t ==> ~(15w = R1)``;

val IMP_NEQ_Reg3 = IMP_NEQ_PROVE
  ``WD_ARM t ==> 
    { Reg 15w (reg 15w s); Reg R1 (reg R1 s); Reg R2 (reg R2 s) } SUBSET t /\
    (one (Reg 15w p) * one (Reg R1 x1) * one (Reg R2 x2) * Q) t ==> 
    ~(15w = R1) /\ ~(15w = R2) /\ ~(R1 = R2)``;

val IMP_NEQ_Reg4 = IMP_NEQ_PROVE
  ``WD_ARM t ==> 
    { Reg 15w (reg 15w s); Reg R1 (reg R1 s); Reg R2 (reg R2 s); Reg R3 (reg R3 s) } SUBSET t /\ 
    (one (Reg 15w p) * one (Reg R1 x1) * one (Reg R2 x2) * one (Reg R3 x3) * Q) t ==> 
    ~(15w = R1) /\ ~(15w = R2) /\ ~(15w = R3) /\ ~(R1 = R2) /\ ~(R1 = R3) /\ ~(R2 = R3)``;

val IMP_NEQ_Reg5 = IMP_NEQ_PROVE
  ``WD_ARM t ==> 
    { Reg 15w (reg 15w s); Reg R1 (reg R1 s); Reg R2 (reg R2 s); 
      Reg R3 (reg R3 s); Reg R4 (reg R4 s) } SUBSET t /\  
    (one (Reg 15w p) * one (Reg R1 x1) * one (Reg R2 x2) * one (Reg R3 x3) * one (Reg R4 x4) * Q) t ==> 
    ~(15w = R1) /\ ~(15w = R2) /\ ~(15w = R3) /\ ~(15w = R4) /\ 
    ~(R1 = R2) /\ ~(R1 = R3) /\ ~(R1 = R4) /\ ~(R2 = R3) /\ 
    ~(R2 = R4) /\ ~(R3 = R4)``;

val IMP_NEQ_Mem1 = IMP_NEQ_PROVE
  ``WD_ARM t ==> { Mem M1 (mem M1 s) } SUBSET t /\ (one (Mem M1 m1) * Q) t ==> T``;

val IMP_NEQ_Mem2 = IMP_NEQ_PROVE
  ``WD_ARM t ==> { Mem M1 (mem M1 s); Mem M2 (mem M2 s) } SUBSET t /\
    (one (Mem M1 m1) * one (Mem M2 m2) * Q) t ==> ~(M1 = M2)``;

val IMP_NEQ_Status = IMP_NEQ_PROVE
  ``WD_ARM t ==> { Status (status s) } SUBSET t /\ 
    (one (Status (sN,sZ,sC,sV)) * Q) t ==> T``;

val IMP_NEQ_Undef = IMP_NEQ_PROVE
  ``WD_ARM t ==> { Undef s.undefined } SUBSET t /\ 
    (one (Undef undef_value) * Q) t ==> T``;

val IMP_NEQ_Rest = IMP_NEQ_PROVE
  ``WD_ARM t ==> { Rest (owrt_visible s) } SUBSET t /\ 
    (one (Rest rest_value) * Q) t ==> T``;

val IMP_NEQ_Cond = IMP_NEQ_PROVE
  ``WD_ARM t ==> { } SUBSET t /\ (cond cond_value * Q) t ==> T``;

fun IMP_NEQ_Reg 1 = IMP_NEQ_Reg1
  | IMP_NEQ_Reg 2 = IMP_NEQ_Reg2
  | IMP_NEQ_Reg 3 = IMP_NEQ_Reg3
  | IMP_NEQ_Reg 4 = IMP_NEQ_Reg4
  | IMP_NEQ_Reg n = IMP_NEQ_Reg5;  

fun IMP_NEQ_Mem 1 = IMP_NEQ_Mem1
  | IMP_NEQ_Mem n = IMP_NEQ_Mem2;

val IMP_NEQ_EMPTY = prove(
  ``!Q. {} SUBSET t /\ (emp * Q) (t:ARMset) ==> T``, METIS_TAC []);

val IMP_NEQ_COMPOSE = prove(
  ``(!Q. t1 SUBSET t /\ (x1 * Q) t ==> c1) /\ 
    (!Q. t2 SUBSET t /\ (x2 * Q) t ==> c2) ==>
    (!Q. (t1 UNION t2) SUBSET t /\ ((x1 * x2) * Q) (t:ARMset) ==> c1 /\ c2)``,
  METIS_TAC [STAR_ASSOC,STAR_SYM,UNION_SUBSET]);

fun imp_neq_compose th1 th2 = 
  SIMP_RULE (pure_ss++SET_APPEND_ss) [] (MATCH_MP IMP_NEQ_COMPOSE (CONJ th1 th2));

fun imp_neq_compose_list g xs =
  let
    fun f [] th = Q.SPEC `emp` th 
      | f (x::xs) th = f xs (imp_neq_compose th (g x))
    val c = BINOP_CONV (REWRITE_CONV [emp_STAR,GSYM CONJ_ASSOC,STAR_ASSOC])
  in
    CONV_RULE c (f xs IMP_NEQ_EMPTY)
  end;

fun mk_imp_neq (rs,ms,st,ud,rt) =
  let 
    val ys = [IMP_NEQ_Reg rs, IMP_NEQ_Mem ms]
    val ys = if st then ys @ [IMP_NEQ_Status] else ys
    val ys = if ud then ys @ [IMP_NEQ_Undef] else ys
    val ys = if rt then ys @ [IMP_NEQ_Rest] else ys
    val ys = ys @ [IMP_NEQ_Cond]
    val th = imp_neq_compose_list I ys
  in
    DISCH_ALL th
  end;

(* debug:
  mk_imp_neq (2,2,true,true,false)
*)


(* ----------------------------------------------------------------------------- *)
(* Produce theorems to give implied equalities                                   *)
(* ----------------------------------------------------------------------------- *)

fun IMP_EQ_TAC x =
  REWRITE_TAC [one_STAR,cond_STAR,WD_ARM_def,SUBSET_DEF,IN_INSERT] \\ METIS_TAC [x];

fun IMP_EQ_PROVE x tm = prove(tm,IMP_EQ_TAC x);

val IMP_EQ_Reg = IMP_EQ_PROVE WD_Reg_def
  ``!r n m t. 
       WD_ARM t ==> !Q. { Reg r n } SUBSET t /\ (one (Reg r m) * Q) t ==> (n = m)``;

val IMP_EQ_Mem = IMP_EQ_PROVE WD_Mem_def
  ``!a n m t. 
       WD_ARM t ==> !Q. { Mem a n } SUBSET t /\ (one (Mem a m) * Q) t ==> (n = m)``;

val IMP_EQ_Status = IMP_EQ_PROVE WD_Status_def
  ``WD_ARM t ==> 
    !Q. { Status (status s) } SUBSET t /\ (one (Status (sN,sZ,sC,sV)) * Q) t ==> 
    ((status s) = (sN,sZ,sC,sV))``;

val IMP_EQ_Undef = IMP_EQ_PROVE WD_Undef_def
  ``WD_ARM t ==> 
    !Q. { Undef s.undefined } SUBSET t /\ (one (Undef undef_value) * Q) t ==> 
    (s.undefined = undef_value)``;

val IMP_EQ_Rest = IMP_EQ_PROVE WD_Rest_def
  ``WD_ARM t ==> 
    !Q. { Rest (owrt_visible s) } SUBSET t /\ (one (Rest rest_value) * Q) t ==> 
    ((owrt_visible s) = rest_value)``;

val IMP_EQ_Cond = IMP_EQ_PROVE WD_ARM_def
  ``WD_ARM t ==> 
    !Q. {} SUBSET t /\ (cond cond_value * Q) t ==> 
    cond_value``;

fun mk_reg_imp_eq (v,x) = 
  let
    val n = subst [``x:word4``|->v] ``reg x s``
  in  
    (UNDISCH o RW [IN_INSERT] o SPEC_ALL o SPECL [v,n,x]) IMP_EQ_Reg
  end;

fun mk_mem_imp_eq (v,x) = 
  let
    val n = subst [``x:word30``|->v] ``mem x s``
  in  
    (UNDISCH o RW [IN_INSERT] o SPEC_ALL o SPECL [v,n,x]) IMP_EQ_Mem
  end;

fun IMP_EQ_Reg n = map mk_reg_imp_eq (take n default_Regs);
fun IMP_EQ_Mem n = map mk_mem_imp_eq (take n default_Mems);

val IMP_EQ_EMPTY = prove(
  ``!Q. {} SUBSET t /\ (emp * Q) (t:ARMset) ==> T``, METIS_TAC []);

val IMP_EQ_COMPOSE = prove(
  ``(!Q. t1 SUBSET t /\ (x1 * Q) t ==> c1) /\ 
    (!Q. t2 SUBSET t /\ (x2 * Q) t ==> c2) ==>
    (!Q. (t1 UNION t2) SUBSET t /\ ((x1 * x2) * Q) (t:ARMset) ==> c1 /\ c2)``,
  METIS_TAC [STAR_ASSOC,STAR_SYM,UNION_SUBSET]);

fun imp_eq_compose th1 th2 = 
  SIMP_RULE (bool_ss++SET_APPEND_ss) [] (MATCH_MP IMP_EQ_COMPOSE (CONJ th1 th2));

fun imp_eq_compose_list g xs =
  let
    fun f [] th = RW [emp_STAR,GSYM CONJ_ASSOC,STAR_ASSOC] (SPEC_ALL th) 
      | f (x::xs) th = f xs (imp_eq_compose th (g x))
  in
    f xs IMP_EQ_EMPTY
  end;

fun mk_imp_eq (rs,ms,st,ud,rt) =
  let 
    val ys = IMP_EQ_Reg rs @ IMP_EQ_Mem ms
    val ys = if st then ys @ [UNDISCH IMP_EQ_Status] else ys
    val ys = if ud then ys @ [UNDISCH IMP_EQ_Undef] else ys
    val ys = if rt then ys @ [UNDISCH IMP_EQ_Rest] else ys
    val ys = ys @ [UNDISCH IMP_EQ_Cond]
    val th = imp_eq_compose_list I ys
  in
    (DISCH_ALL o RW [emp_STAR] o Q.INST [`Q`|->`emp`]) th
  end;

(* debug:
  mk_imp_eq (2,2,true,true,false)
*)


(* ----------------------------------------------------------------------------- *)
(* Produce theorems describing the postcondition                                 *)
(* ----------------------------------------------------------------------------- *)

val POST_GEN_TAC = 
  REWRITE_TAC [GSYM STAR_ASSOC] 
  \\ SRW_TAC [] [one_STAR,DELETE_DEF] \\ SRW_TAC [] [one_def];

fun POST_GEN_PROVE tm = prove(tm,POST_GEN_TAC);

val POST_GEN_Reg1 = POST_GEN_PROVE
  ``T ==> (one (Reg 15w (reg 15w s))) { Reg 15w (reg 15w s) }``;

val POST_GEN_Reg2 = POST_GEN_PROVE
  ``~(15w = R1) ==> 
    (one (Reg 15w (reg 15w s)) * one (Reg R1 (reg R1 s))) 
    { Reg 15w (reg 15w s); Reg R1 (reg R1 s) }``;

val POST_GEN_Reg3 = POST_GEN_PROVE
  ``~(15w = R1) /\ ~(15w = R2) /\ ~(R1 = R2) ==>  
    (one (Reg 15w (reg 15w s)) * one (Reg R1 (reg R1 s)) * one (Reg R2 (reg R2 s))) 
    { Reg 15w (reg 15w s); Reg R1 (reg R1 s); Reg R2 (reg R2 s) }``;

val POST_GEN_Reg4 = POST_GEN_PROVE
  ``~(15w = R1) /\ ~(15w = R2) /\ ~(15w = R3) /\ ~(R1 = R2) /\ ~(R1 = R3) /\ ~(R2 = R3) ==> 
    (one (Reg 15w (reg 15w s)) * one (Reg R1 (reg R1 s)) * one (Reg R2 (reg R2 s)) * 
     one (Reg R3 (reg R3 s))) 
    { Reg 15w (reg 15w s); Reg R1 (reg R1 s); Reg R2 (reg R2 s); Reg R3 (reg R3 s) }``;

val POST_GEN_Reg5 = POST_GEN_PROVE
  ``~(15w = R1) /\ ~(15w = R2) /\ ~(15w = R3) /\ ~(15w = R4) /\ ~(R1 = R2) /\ ~(R1 = R3) /\ 
    ~(R1 = R4) /\ ~(R2 = R3) /\ ~(R2 = R4) /\ ~(R3 = R4) ==>  
    (one (Reg 15w (reg 15w s)) * one (Reg R1 (reg R1 s)) * one (Reg R2 (reg R2 s)) *
     one (Reg R3 (reg R3 s)) * one (Reg R4 (reg R4 s))) 
    { Reg 15w (reg 15w s); Reg R1 (reg R1 s); Reg R2 (reg R2 s); 
      Reg R3 (reg R3 s); Reg R4 (reg R4 s) }``;

val POST_GEN_Mem1 = POST_GEN_PROVE
  ``T ==> (one (Mem M1 (mem M1 s))) { Mem M1 (mem M1 s) }``;

val POST_GEN_Mem2 = POST_GEN_PROVE
  ``~(M1 = M2) ==>  
        (one (Mem M1 (mem M1 s)) * one (Mem M2 (mem M2 s))) 
        { Mem M1 (mem M1 s); Mem M2 (mem M2 s) }``;

val POST_GEN_Status = POST_GEN_PROVE
  ``T ==> (one (Status (status s))) { Status (status s) }``;

val POST_GEN_Undef = POST_GEN_PROVE
  ``T ==> (one (Undef s.undefined)) { Undef s.undefined }``;

val POST_GEN_Rest = POST_GEN_PROVE
  ``T ==> (one (Rest (owrt_visible s))) { Rest (owrt_visible s) }``;

val POST_GEN_emp = prove(``T ==> emp ({}:ARMset)``,SIMP_TAC bool_ss [emp_def]);

val POST_GEN_COMPOSE = prove(
  ``(c1 ==> P x1) /\ (c2 ==> Q x2) ==> 
    (($DISJOINT:ARMset->ARMset->bool) x1 x2) ==>
    (c1 /\ c2 ==> (P * Q) (x1 UNION x2))``,  
  SRW_TAC [] [DISJOINT_DEF,SPLIT_def,STAR_def,EXTENSION] \\ METIS_TAC []);

fun post_gen_compose th1 th2 =
  let 
    val th = MATCH_MP POST_GEN_COMPOSE (CONJ th1 th2)
    val c1 = SIMP_CONV (srw_ss()) [DISJOINT_DEF,IN_INTER,EXTENSION,NOT_IN_EMPTY]
    val c2 = PURE_REWRITE_CONV [INSERT_UNION_COMM,UNION_EMPTY]
    val th = CONV_RULE (FORK_CONV (c1,c2)) th
  in
    MP th TRUTH        
  end;

fun post_gen_compose_list g xs =
  let
    fun f [] th = PURE_REWRITE_RULE 
                     [emp_STAR,GSYM CONJ_ASSOC,STAR_ASSOC] (SPEC_ALL th) 
      | f (x::xs) th = f xs (post_gen_compose th (g x))
  in
    f xs POST_GEN_emp
  end;

fun post_gen_Reg 1 = POST_GEN_Reg1
  | post_gen_Reg 2 = POST_GEN_Reg2
  | post_gen_Reg 3 = POST_GEN_Reg3
  | post_gen_Reg 4 = POST_GEN_Reg4
  | post_gen_Reg n = POST_GEN_Reg5;

fun post_gen_Mem 1 = POST_GEN_Mem1
  | post_gen_Mem n = POST_GEN_Mem2;

fun post_gen (rs,ms,st,ud,rt) =
  let 
    val ys = [post_gen_Reg rs, post_gen_Mem ms]
    val ys = if st then ys @ [POST_GEN_Status] else ys
    val ys = if ud then ys @ [POST_GEN_Undef] else ys
    val ys = if rt then ys @ [POST_GEN_Rest] else ys
    val th = post_gen_compose_list I ys
    val th = PURE_REWRITE_RULE [emp_STAR] th
    val th = INTRO_arm2set' (rs,ms,st,ud,rt) th
  in
    th
  end;

(* debug:
  post_gen (2,2,true,true,false)
*)


(* ----------------------------------------------------------------------------- *)
(* Produce theorems to give implied equalities, inequalities and postcondition   *)
(* ----------------------------------------------------------------------------- *)

val WD_ARM_IMP_SIMP = prove(
  ``(!t. WD_ARM t ==> (arm2set' x s) SUBSET t /\ P t ==> b) ==> 
    (P (arm2set' x s) ==> b)``,
  METIS_TAC [WD_ARM_arm2set',SUBSET_REFL]);

fun mk_clean_imp f (rs,ms,st,ud,rt) = 
  let
    val th = f (rs,ms,st,ud,rt)
    val th = Q.GEN `t` th
    val th = INTRO_arm2set' (rs,ms,st,ud,rt) th
  in  
    MATCH_MP WD_ARM_IMP_SIMP th
  end;

fun mk_imps (rs,ms,st,ud,rt) =
  let 
    val th1 = mk_clean_imp mk_imp_eq (rs,ms,st,ud,rt)
    val th2 = mk_clean_imp mk_imp_neq (rs,ms,st,ud,rt)
    val th3 = post_gen (rs,ms,st,ud,rt)
    val th3 = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV []))) th3
    val th3 = Q.INST [`s`|->`NEXT_ARM_MEM s`] th3
    val th = CONJ th1 th2
    val th = PURE_REWRITE_RULE [GSYM IMP_CONJ_THM] th 
    val th = REWRITE_RULE [GSYM CONJ_ASSOC] th
    val th' = DISCH_ALL (MP th3 (UNDISCH th2))   
  in
    (th,th')
  end;

(* debug:
  mk_imps (2,2,true,true,false)
*)


(* ----------------------------------------------------------------------------- *)
(* Lemmas for forms of pre and post-conditions                                   *)
(* ----------------------------------------------------------------------------- *)

val DEFAULT_INST_LEMMA = GEN_ALL (REWRITE_CONV [] ``b = F``);

fun DEFAULT_INST_PRE pre = 
  let
    val pre = Q.INST [`undef_value`|->`F`] pre    
    val pre = Q.INST [`M1`|->`addr30 p`] pre
    val pre = Q.INST [`m1`|->`command`] pre
    val pre = INST [``M2:word30``|->``addr30 M2``] pre
    val pre = INST [``M3:word30``|->``addr30 M3``] pre
    val pre = INST [``M4:word30``|->``addr30 M4``] pre
    val pre = INST [``M5:word30``|->``addr30 M5``] pre
    val pre = PURE_REWRITE_RULE [DEFAULT_INST_LEMMA] pre   
  in
    pre
  end;

val DIST_PC = prove(
  ``!s f p. (reg 15w s = p) /\ f p = (reg 15w s = p) /\ f (s.registers r15)``,
  SRW_TAC [] [reg_def] \\ METIS_TAC []);

fun GEN_CONDs (rs,ms,st,ud,rt) =
  let
    val (pre1,post) = mk_imps (rs,ms,st,ud,rt)
    val pre2 = mk_set_req (rs,ms,st,ud,rt)
    val pre = CONJ pre1 (CONJ pre2 post)
    val pre = DEFAULT_INST_PRE pre
    val pre1 = CONJUNCT1 pre
    val pre  = CONJUNCT2 pre
    val pre2 = CONJUNCT1 pre
    val post = CONJUNCT2 pre
  in
    (pre1,pre2,post)
  end;

val c11FTF = GEN_CONDs (1,1,false,true,false);
val c21FTF = GEN_CONDs (2,1,false,true,false);
val c31FTF = GEN_CONDs (3,1,false,true,false);
val c41FTF = GEN_CONDs (4,1,false,true,false);
val c51FTF = GEN_CONDs (5,1,false,true,false);

val c11TTF = GEN_CONDs (1,1,true,true,false);
val c21TTF = GEN_CONDs (2,1,true,true,false);
val c31TTF = GEN_CONDs (3,1,true,true,false);
val c41TTF = GEN_CONDs (4,1,true,true,false);
val c51TTF = GEN_CONDs (5,1,true,true,false);

val c12TTF = GEN_CONDs (1,2,true,true,false);
val c22TTF = GEN_CONDs (2,2,true,true,false);
val c32TTF = GEN_CONDs (3,2,true,true,false);
val c42TTF = GEN_CONDs (4,2,true,true,false);
val c52TTF = GEN_CONDs (5,2,true,true,false);


(* ----------------------------------------------------------------------------- *)
(* Produce theorems to satisfy "cond 2" of IMP_ARM_RUN1                           *)
(* ----------------------------------------------------------------------------- *)

val REG_WRITE_r15 = prove(
  ``!r m n d. ~(15w = n) ==> ((REG_WRITE r m n d) r15 = r r15)``,
  METIS_TAC [(RW [REG_READ6_def,FETCH_PC_def] o Q.INST [`n2`|->`15w`] o SPEC_ALL) 
             arm_evalTheory.REG_READ_WRITE_NEQ]);

val REG_READ_WRITE_NEQ2 = prove(
  ``!n1 n2 r m1 m2 d. 
      ~(n1 = n2) ==> 
      (REG_READ (REG_WRITE r m1 n1 d) m2 n2 = REG_READ r m2 n2)``,
  REPEAT STRIP_TAC \\ Cases_on `15w = n2`
  THEN1 ASM_SIMP_TAC std_ss [REG_READ_def,REG_READ_WRITE_NEQ,REG_WRITE_r15]
  \\ METIS_TAC [REG_READ6_def,REG_READ_WRITE_NEQ]);

val SHAPE_ss = rewrites
  [owrt_visible_def,set_status_def,owrt_visible_regs_def,state_mode_def,
   status_def,statusN_def,statusZ_def,statusC_def,statusV_def,mem_def,reg_def,
   REG_READ_WRITE_NEQ2,REG_OWRT_ALL,REG_READ_INC_PC,MEM_WRITE_WORD_def,SUBST_def,
   ADDR30_def,GSYM addr30_def];

val SHAPE_TAC = 
  SIMP_TAC (srw_ss()++SHAPE_ss) [arm2set''_EQ,IN_INSERT,NOT_IN_EMPTY] \\ CONV_TAC PSR_CONV 
  \\ SIMP_TAC (srw_ss()++SHAPE_ss) [arm2set''_EQ,IN_INSERT,NOT_IN_EMPTY];

val SHAPE_TERM_FORMAT = 
  ``(NEXT_ARM_MEM s = 
       <|registers := rx; psrs := px; memory := mx; undefined := F|>) ==>
    (fx s = fx (NEXT_ARM_MEM s) :ARMset)``;

fun MK_SHAPE_TERM (rx,px,mx) fx =
  subst [``rx:registers``   |-> rx,
         ``px:psrs``       |-> px,
         ``mx:mem``     |-> mx,
         ``fx:arm_mem_state -> ARMset`` |-> fx] SHAPE_TERM_FORMAT;

fun MK_SHAPE_THM (rx,px,mx) fx = prove(MK_SHAPE_TERM (rx,px,mx) fx, SHAPE_TAC);

val i' = ``INC_PC s.registers``;
val ir' = ``INC_PC (REG_WRITE s.registers (state_mode s) R1 z)``;
val ri' = ``REG_WRITE (INC_PC s.registers) (state_mode s) R1 z``;
val irr' = ``INC_PC (REG_WRITE (REG_WRITE s.registers (state_mode s) R1 z') (state_mode s) R2 z)``;
val rir' = ``REG_WRITE (INC_PC (REG_WRITE s.registers (state_mode s) R1 z')) (state_mode s) R2 z``;
val rri' = ``REG_WRITE (REG_WRITE (INC_PC s.registers) (state_mode s) R1 z') (state_mode s) R2 z``;

val m' = ``MEM_WRITE_WORD s.memory M2 v``;

val i = (i',``s.psrs``,``s.memory``);
val ir = (ir',``s.psrs``,``s.memory``);
val ri = (ri',``s.psrs``,``s.memory``);
val irr = (irr',``s.psrs``,``s.memory``);
val rir = (rir',``s.psrs``,``s.memory``);
val rri = (rri',``s.psrs``,``s.memory``);
val im = (i',``s.psrs``,m');
val is = (i',``set_status (bb1,bb2,bb3,bb4) s``,``s.memory``);
val irs = (ir',``set_status (bb1,bb2,bb3,bb4) s``,``s.memory``);
val ris = (ri',``set_status (bb1,bb2,bb3,bb4) s``,``s.memory``);
val irm = (ir',``s.psrs``,m');
val rim = (ri',``s.psrs``,m');
val rims = (ri',``set_status (bb1,bb2,bb3,bb4) s``,m');
val rris = (rri',``set_status (bb1,bb2,bb3,bb4) s``,``s.memory``);

val b = (``REG_WRITE s.registers usr 15w z``,``s.psrs``,``s.memory``);
val br = (``REG_WRITE (REG_WRITE s.registers (state_mode s) R1 z') usr 15w z``,``s.psrs``,``s.memory``);
val rb = (``REG_WRITE (REG_WRITE s.registers usr 15w z') (state_mode s) R1 z``,``s.psrs``,``s.memory``);

(* actually used *)

val Sb11FTF  = MK_SHAPE_THM b  ``arm2set'' ({15w},{M1},F,T,F)``;
val Sb11TTF  = MK_SHAPE_THM b  ``arm2set'' ({15w},{M1},T,T,F)``;
val Sb21FTF  = MK_SHAPE_THM b  ``arm2set'' ({15w;R1},{M1},F,T,F)``;
val Sb21TTF  = MK_SHAPE_THM b  ``arm2set'' ({15w;R1},{M1},T,T,F)``;
val Srb21FTF = MK_SHAPE_THM rb ``arm2set'' ({15w;R1},{M1},F,T,F)``;
val Srb21TTF = MK_SHAPE_THM rb ``arm2set'' ({15w;R1},{M1},T,T,F)``;
val Sbr22TTF = MK_SHAPE_THM br ``arm2set'' ({15w;R1},{M1;addr30 M2},T,T,F)``;

val Si11TTF   = MK_SHAPE_THM i   ``arm2set'' ({15w},{M1},T,T,F)``;
val Sis21TTF  = MK_SHAPE_THM is  ``arm2set'' ({15w;R1},{M1},T,T,F)``;
val Sis31TTF  = MK_SHAPE_THM is  ``arm2set'' ({15w;R1;R2},{M1},T,T,F)``;
val Sirs21TTF = MK_SHAPE_THM irs ``arm2set'' ({15w;R1},{M1},T,T,F)``;
val Sirs31TTF = MK_SHAPE_THM irs ``arm2set'' ({15w;R1;R2},{M1},T,T,F)``;
val Sirs41TTF = MK_SHAPE_THM irs ``arm2set'' ({15w;R1;R2;R3},{M1},T,T,F)``;
val Sris21TTF = MK_SHAPE_THM ris ``arm2set'' ({15w;R1},{M1},T,T,F)``;
val Sris31TTF = MK_SHAPE_THM ris ``arm2set'' ({15w;R1;R2},{M1},T,T,F)``;
val Sris41TTF = MK_SHAPE_THM ris ``arm2set'' ({15w;R1;R2;R3},{M1},T,T,F)``;
val Sris51TTF = MK_SHAPE_THM ris ``arm2set'' ({15w;R1;R2;R3;R4},{M1},T,T,F)``;
val Srris41TTF = MK_SHAPE_THM rris ``arm2set'' ({15w;R1;R2;R3},{M1},T,T,F)``;
val Srris51TTF = MK_SHAPE_THM rris ``arm2set'' ({15w;R1;R2;R3;R4},{M1},T,T,F)``;

val Srim22TTF = MK_SHAPE_THM rim ``arm2set'' ({15w;R1},{M1;addr30 M2},T,T,F)``;
val Srim32TTF = MK_SHAPE_THM rim ``arm2set'' ({15w;R1;R2},{M1;addr30 M2},T,T,F)``;
val Srim42TTF = MK_SHAPE_THM rim ``arm2set'' ({15w;R1;R2;R3},{M1;addr30 M2},T,T,F)``;

val Sirm22TTF = MK_SHAPE_THM irm ``arm2set'' ({15w;R1},{M1;addr30 M2},T,T,F)``;
val Sirm32TTF = MK_SHAPE_THM irm ``arm2set'' ({15w;R1;R2},{M1;addr30 M2},T,T,F)``;

val Sri22TTF = MK_SHAPE_THM ri ``arm2set'' ({15w;R1},{M1;addr30 M2},T,T,F)``;
val Srir32TTF = MK_SHAPE_THM rir ``arm2set'' ({15w;R1;R2},{M1;addr30 M2},T,T,F)``;


(* ----------------------------------------------------------------------------- *)
(* Function for tidying up theorems from arm_rules                               *)
(* ----------------------------------------------------------------------------- *)

(* lemmas that tidy up *)

val CLEAN_ADC1 = prove(
  ``!b x y z. (if b then x+y+z else x+y) = x+y+(if b then z else 0w)``,
  Cases_on `b` \\ REWRITE_TAC [WORD_ADD_0]);

val CLEAN_ADC2 = prove(
  ``(if b then (f (m + n + 1w),
                m + n + 1w = 0w,
                g (w2n m + (w2n n + 1)),
                (f m = f n) /\ ~(f m = f (m + n + 1w)))
          else
               (f (m + n),
                m + n = 0w,
                g (w2n m + w2n n),
                (f m = f n) /\ ~(f m = f (m + n)))) =
    (f (m + n + (if b then 1w else 0w)),
     m + n + (if b then 1w else 0w) = 0w,
     g (w2n m + w2n n + w2n (if b then 1w:word32 else 0w)),
     (f m = f n) /\ ~(f m = f (m + n + (if b then 1w else 0w))))``,
  Cases_on `b` 
  \\ REWRITE_TAC [WORD_ADD_0,arithmeticTheory.ADD_0] 
  \\ EVAL_TAC 
  \\ REWRITE_TAC [arithmeticTheory.ADD_ASSOC]);

val CLEAN_SBC1 = prove(
  ``!b x y z. (if b then x-y else x-y-z) = x-y-(if b then 0w else z)``,
  Cases_on `b` \\ REWRITE_TAC [WORD_SUB_RZERO]);

val CLEAN_SBC2 = prove(
  ``(if b then (f (m - n),
                m - n = 0w,
                g (w2n m - w2n n),
                (f m = f n) /\ ~(f m = f (m - n)))
          else
               (f (m - n - 1w),
                m - n - 1w = 0w,
                g (w2n m - w2n n - 1),
                (f m = f n) /\ ~(f m = f (m - n - 1w)))) =
    (f (m - n - (if b then 0w else 1w)),
     m - n - (if b then 0w else 1w) = 0w,
     g (w2n m - w2n n - w2n (if b then 0w:word32 else 1w)),
     (f m = f n) /\ ~(f m = f (m - n - (if b then 0w else 1w))))``,
  Cases_on `b` 
  \\ REWRITE_TAC [WORD_SUB_RZERO,arithmeticTheory.SUB_0] 
  \\ EVAL_TAC 
  \\ REWRITE_TAC [arithmeticTheory.ADD_ASSOC]);

val CLEAN_ss = rewrites [CLEAN_ADC1,CLEAN_ADC2,CLEAN_SBC1]; 

(* push in if statements *)

val REG_PUSH_IF = prove(
  ``!b regs m r x y.
      (if b then REG_WRITE regs m r x else REG_WRITE regs m r y) =
      REG_WRITE regs m r (if b then x else y)``,
  SRW_TAC [] []);

val REG_PUSH_IF2 = prove(
  ``!b regs m r x y.
      (if b then REG_WRITE regs m r x else REG_WRITE regs' m r y) =
      REG_WRITE (if b then regs else regs') m r (if b then x else y)``,
  SRW_TAC [] []);

val STATUS_PUSH_IF = prove(
  `` (if s then set_status (n,z,c,v) state 
           else state.psrs) =
     set_status ((if s then n else statusN state),
                 (if s then z else statusZ state),
                 (if s then c else statusC state),
                 (if s then v else statusV state)) state``,
  Cases_on `s` 
  \\ REWRITE_TAC [set_status_def,statusN_def,statusZ_def,statusC_def,statusV_def]
  \\ REWRITE_TAC [SET_NZCV_ID,CPSR_READ_WRITE]);

val CLEAN_IF_ss = rewrites [REG_PUSH_IF,REG_PUSH_IF2,STATUS_PUSH_IF];

val SAME_IF = prove(``(if b then c else c) = c``,Cases_on `b` \\ REWRITE_TAC []);

(* helpers *)

fun LIST_DISCH ts th = foldr (uncurry DISCH) th ts;

fun ASM_UNABBREV_ALL_RULE th =
  let
    val xs = hyp th  
    val is_Abbrev = can_match ``Abbrev b``; 
    val xs1 = filter is_Abbrev xs
    val xs2 = filter (not o is_Abbrev) xs
    val th = LIST_DISCH xs1 (LIST_DISCH xs2 th)
    fun unabbrev_fst th =
      let
        val (l,r) = (dest_eq o snd o dest_comb o binop1 o concl) th
        val th = INST [l |-> r] th
        val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [markerTheory.Abbrev_def])) th
      in
        MP th TRUTH
      end
    val unabbrev_all = funpow (length xs1) unabbrev_fst
    val undisch_rest = funpow (length xs2) UNDISCH
  in
    undisch_rest (unabbrev_all th)
  end;

(* main part *)

val CONDITION_PASSED2_AL = prove(
  ``!x. CONDITION_PASSED2 x AL``,
  STRIP_TAC 
  \\ `?x1 x2 x3 x4. x = (x1,x2,x3,x4)` by METIS_TAC [pairTheory.PAIR]
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [] [CONDITION_PASSED2_def]);

val SET_AL = 
  UNDISCH_ALL o RW [CONDITION_PASSED2_AL] o Q.INST [`c`|->`AL`] o DISCH_ALL;

val INC_PC_EQ = prove(
  ``INC_PC registers = REG_WRITE registers usr 15w (registers r15 + 4w)``,
  SRW_TAC [wordsLib.SIZES_ss] [INC_PC_def,REG_WRITE_def,mode_reg2num_def,SUBST_def,FUN_EQ_THM]
  \\ Q.UNABBREV_TAC `n`
  \\ REWRITE_TAC [num2register_thm]
  \\ METIS_TAC []);

val reg_LEMMA = prove(
  ``!r s. ~(15w = r) ==> (REG_READ s.registers (state_mode s) r = reg r s)``,
  SRW_TAC [] [reg_def]);
  
val rs = [``Rm:word4``,``Rn:word4``,``Rd:word4``];

fun mk_subst_list [] xs = []
  | mk_subst_list rs [] = raise ERROR "mk_subst_list" "Second argument too short."
  | mk_subst_list (r::rs) (x::xs) = (r |-> x) :: mk_subst_list rs xs;

val CONTRCT_DEFS_ss = (rewrites o map GSYM) 
  [status_def,statusN_def,statusZ_def,statusC_def,statusV_def,mem_def,addr30_def];

(* debug:
    val al = false
    val rs = [``Rd:word4``,``Rm:word4``,``Rs:word4``]
    val th = ARM_MUL
    val c  = ``CONDITION_PASSED2 (status s) c``
    val aggressive = false
*)

fun CLEAN_ARM_RULE al rs th c aggressive =
  let
    val th = SPEC_ALL th
    val th = INST [``state:arm_mem_state``|->``s:arm_mem_state``,``s:bool``|->``s_flag:bool``] th
    val th = ASM_UNABBREV_ALL_RULE (UD_ALL th)
    fun NOT_PC x = subst [``x:word4``|->x] ``~(15w:word4 = x)``
    val xs = map NOT_PC rs
    val th = RW [INC_PC_EQ] th 
    val th = foldr (uncurry ADD_ASSUM) th xs
    val th = DISCH_ALL th
    val th = INST (mk_subst_list rs (tl default_Regv)) th
    val th = SIMP_RULE (bool_ss++CONTRCT_DEFS_ss) [NZCV_def] th
    val th = SIMP_RULE bool_ss 
               [GSYM state_mode_def,reg_LEMMA,GSYM set_status_def,
                SET_NZ_def,SET_NZC_def,GSYM statusN_def,
                GSYM statusZ_def,GSYM statusC_def,GSYM statusV_def] th
    val th = DISCH c th
    val th = SIMP_RULE (bool_ss++CLEAN_ss) [] th
    val th = if aggressive then SIMP_RULE (bool_ss++CLEAN_IF_ss) [] th 
                           else RW [STATUS_PUSH_IF,SAME_IF] th
    val th = RW [GSYM INC_PC_EQ] th 
    val th = PURE_REWRITE_RULE [GSYM set_status_def] th
    val th = UD_ALL th
  in
    if al then SET_AL th else th
  end;

fun CLEAN_ARM_RULE_AL rs th = CLEAN_ARM_RULE true rs th ``T`` false;

fun CLEAN_ARM_RULE_C rs th = 
  CLEAN_ARM_RULE false rs th ``CONDITION_PASSED2 (status s) c`` false;

fun CLEAN_ARM_RULE_NOP rs th = 
  CLEAN_ARM_RULE false rs th ``~CONDITION_PASSED2 (status s) c`` false;

(* debug:
  val th = CLEAN_ARM_RULE_C [] ARM_B
*)


(* ----------------------------------------------------------------------------- *)
(* Function for instantiating pre and post-conditions according to a given rule  *)
(* ----------------------------------------------------------------------------- *)

fun INST_CONDs th (p1,p2,p3) c =
  let
    val ms = filter (can_match ``mem x s = enc k``) (hyp th)
    val cmd = (snd o dest_eq o hd) ms
    val f1 = INST [``command:word32`` |-> cmd,``cond_value:bool``|->c]
    val f2 = RW [SEP_cond_CLAUSES,emp_STAR]
    val f = f2 o f1
  in
    (f p1,f p2,f p3)        
  end; 

val CONNECT_LEMMA = prove(
  ``(b ==> c) ==> (c ==> d) ==> (b ==> d:bool)``,
  SRW_TAC [] []);

val registers_r15 = prove(
  ``!s. s.registers r15 = reg 15w s``,
  SRW_TAC [] [reg_def]);

(* debug:
  val conds = c11TTF
  val shape = Sb11TTF
  val th = CLEAN_ARM_RULE [] ARM_B
  val c = ``T``
*)

fun CONNECT th conds c = 
  let
    val (p1,p2,p3) = INST_CONDs th conds c
    val th = (RW [AND_IMP_INTRO] o DISCH_ALL) th
    val BimpC = mk_imp (binop2 (concl p1),binop1 (concl th))
    val BimpC = prove(BimpC,SRW_TAC [] [registers_r15] THEN METIS_TAC [])
    val th' = MATCH_MP CONNECT_LEMMA BimpC    
    val th' = MATCH_MP th' th
    val th' = UNDISCH th'
    val th' = ASM_REWRITE_RULE [] th'
    val th' = DISCH_ALL th'
    val th' = MATCH_MP th' (UNDISCH p1)
    val th' = DISCH_ALL th'
  in 
    (p1,p2,p3,th')
  end;

(* debug:
  val conds = c11TTF
  val shape = Sb11TTF
  val th = CLEAN_ARM_RULE false [] ARM_B
  val c = ``T``
*)

fun COLLECT (conds,shape,insts) th c =
  let
    val f = INST insts
    val (p1,p2,p3,th') = CONNECT th conds c
    val (p1,p2,p3,th') = (f p1,f p2,f p3,f th')
    val shape = DISCH_ALL (MATCH_MP shape (UNDISCH th')) 
    val i = Q.INST [`R1'`|->`R1`,`R2'`|->`R2`,`R3'`|->`R3`,
                    `R4'`|->`R4`,`R5'`|->`R5`,`M2'`|->`M2`,`M1`|->`addr30 p`]
  in
    (p1,p2,p3,th',(i o f) shape)
  end;


(* ----------------------------------------------------------------------------- *)
(* Function for producting ARM_RUNs                                              *)
(* ----------------------------------------------------------------------------- *)

(* registers *)

val REG_READ_WRITE = prove(
  ``!r m n d. ~(15w = n) ==> (REG_READ (REG_WRITE r m n d) m n = d)``,
  SIMP_TAC bool_ss [REG_READ_def,REG_WRITE_def,SUBST_def]);

val REG_READ_WRITE_NEQ = prove(
  ``!r m1 m2 n1 n2 d.
       ~(15w = n2) /\ ~(n1 = n2) ==>
       (REG_READ (REG_WRITE r m1 n1 d) m2 n2 = REG_READ r m2 n2)``,
  METIS_TAC [REG_READ_WRITE_NEQ,REG_READ6_def]);

val INC_PC_r15 = prove(
  ``!r. INC_PC r r15 = r r15 + 4w``,
  SRW_TAC [] [INC_PC_def,SUBST_def]);

val regs_15w_EQ_reg15 = prove(
  ``!s. s.registers r15 = reg 15w s``,  
  SRW_TAC [] [reg_def]);

val REG_WRITE_15 = prove(
  ``!regs m x. REG_WRITE regs m 15w x r15 = x``,
  SIMP_TAC bool_ss [REG_WRITE_def,mode_reg2num_def,EVAL ``w2n (15w:word4)``,LET_DEF]
  \\ SIMP_TAC bool_ss [num2register_thm,SUBST_def]);

val REG_ss = rewrites([REG_READ_INC_PC,REG_READ_WRITE_NEQ,reg_LEMMA,REG_WRITE_15,
                       REG_READ_WRITE,INC_PC_r15,REG_WRITE_r15,regs_15w_EQ_reg15]);

(* status *)

val selectN_def = Define `selectN (n,z,c,v) = n`;
val selectZ_def = Define `selectZ (n,z,c,v) = z`;
val selectC_def = Define `selectC (n,z,c,v) = c`;
val selectV_def = Define `selectV (n,z,c,v) = v`;

val statusN_THM = prove(
  ``CPSR_READ s.psrs %% 31 = selectN (status s)``,
  SRW_TAC [] [status_def,statusN_def,selectN_def]);

val statusZ_THM = prove(
  ``CPSR_READ s.psrs %% 30 = selectZ (status s)``,
  SRW_TAC [] [status_def,statusZ_def,selectZ_def]);

val statusC_THM = prove(
  ``CPSR_READ s.psrs %% 29 = selectC (status s)``,
  SRW_TAC [] [status_def,statusC_def,selectC_def]);

val statusV_THM = prove(
  ``CPSR_READ s.psrs %% 28 = selectV (status s)``,
  SRW_TAC [] [status_def,statusV_def,selectV_def]);

val STATUS_ss = rewrites 
  [statusN_THM,statusZ_THM,statusC_THM,statusV_THM,
   selectN_def,selectZ_def,selectC_def,selectV_def];

val STATUS_PULL_IF = prove(
  ``Status ((if b then n else n'),(if b then z else z'),
            (if b then c else c'),(if b then v else v')) =
    Status (if b then (n,z,c,v) else (n',z',c',v'))``,
  Cases_on `b` \\ REWRITE_TAC []);

(* memory *)

val MEM_READ_WRITE = prove(
  ``!x z s. MEM_WRITE_WORD s.memory x z (addr30 x) = z``, 
  REWRITE_TAC [MEM_WRITE_WORD_def,mem_def,SUBST_def]
  \\ SIMP_TAC bool_ss [ADDR30_def,GSYM addr30_def,addr30_addr32]);

val MEM_READ_WRITE_NEQ = prove(
  ``!x y z s. ~(addr30 x = addr30 y) ==> 
              (MEM_WRITE_WORD s.memory y z (addr30 x) = mem (addr30 x) s)``,
  REWRITE_TAC [MEM_WRITE_WORD_def,mem_def,SUBST_def]
  \\ SIMP_TAC bool_ss [ADDR30_def,GSYM addr30_def,addr30_addr32]);

val MEM_ss = rewrites [MEM_READ_WRITE,MEM_READ_WRITE_NEQ];

(* general *)

val NEXT_ARM_MEM_TEMP_def = Define `NEXT_ARM_MEM_TEMP = NEXT_ARM_MEM`;

val FIX_POST_LEMMA = prove(
  ``(a ==> d) ==> (a ==> b) ==> (a ==> c) ==> (a ==> (b /\ c) ==> d):bool``,
  SRW_TAC [] []);

val CONNECT' = prove(
  ``(a ==> (b /\ c) ==> d) ==> (a ==> b) ==> (a ==> c) ==> (a ==> d):bool``,
  SRW_TAC [] []);

val ALL_DEFS = [set_status_def,state_mode_def,reg_def,
                status_def,statusN_def,statusZ_def,statusC_def,statusV_def,mem_def,
                REG_READ6_def,FETCH_PC_def];

val EXPAND_ALL_DEFS_ss = rewrites ALL_DEFS

(* debug:
    val th = ARM_BIC
    val nop = ARM_BIC_NOP
    val th = Q.INST [`Rm`|->`Rn`,`Rd`|->`Rn`] (SPEC_ALL th)
    val th = FIX_ADDR_MODE1 th
    val rs = [``Rn:word4``]
    val (conds,shape,prog) = (c21TTF,Sirs21TTF,P21sc)
    val c = ``CONDITION_PASSED2 (sN,sZ,sC,sV) c``
*)
  
val NEQ_14_15 = (* required by ARM_BL *)
  EVAL ``14 MOD dimword (:i4) = 15 MOD dimword (:i4)``;

val SAME_IF = prove(``(if b then c else c) = c``,Cases_on `b` \\ REWRITE_TAC []);

fun MK_ARM_RUN (conds,shape,insts) th c = 
  let
    val (p1,p2,p3,th',c2) = COLLECT (conds,shape,insts) th c
    val p3 = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV [GSYM NEXT_ARM_MEM_TEMP_def]))) p3
    val th = MATCH_MP FIX_POST_LEMMA p3
    val th = MATCH_MP th p1
    val th = MATCH_MP th th'
    val th = UNDISCH th
    val th = SIMP_RULE bool_ss [] th
    val th = CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()++EXPAND_ALL_DEFS_ss) [])) th
    val th = SIMP_RULE bool_ss [] th
    val th = CONV_RULE PSR_CONV th
    val th = SIMP_RULE bool_ss [GSYM state_mode_def,GSYM mem_def] th
    val th = SIMP_RULE (bool_ss++REG_ss++MEM_ss++STATUS_ss) [NEQ_14_15] th
    val th = RW [GSYM regs_15w_EQ_reg15] th
    (* wrap up post *)
    val th = RW [NEXT_ARM_MEM_TEMP_def] th
    val th = DISCH_ALL th
    val th = MATCH_MP CONNECT' th
    val th = MP th (RW [GSYM regs_15w_EQ_reg15] p1)
    val th = MP th (RW [SAME_IF] th')
    (* wrap up all *)
    val c1 = Q.GEN `t` (Q.GEN `s` p2)
    val c23 = Q.GEN `s` (DISCH_ALL (CONJ (UNDISCH c2) (UNDISCH th)))  
    val c123 = CONJ c1 c23
    val x = (comb2 o comb1 o binop2 o binop2 o concl) p2
    val P = (comb1 o binop2 o binop1 o concl) p2
    val Q = (comb1 o binop2 o concl) th
    val c123_imp = ISPECL [x,P,Q] IMP_ARM_RUN1
    val result = MP c123_imp c123
  in
    RW [STATUS_PULL_IF] (Q.INST [`c:condition`|->`c_flag`] result)
  end;

fun MK_ARM_RUN_AL (conds,shape,i) th = MK_ARM_RUN (conds,shape,i) th ``T``;

fun MK_ARM_RUN_C (conds,shape,insts) th = 
  MK_ARM_RUN (conds,shape,insts) th ``CONDITION_PASSED2 (sN,sZ,sC,sV) c``;

fun MK_ARM_RUN_NOP th = 
  MK_ARM_RUN (c11TTF,Si11TTF,[]) th ``~CONDITION_PASSED2 (sN,sZ,sC,sV) c``;


(* ----------------------------------------------------------------------------- *)
(* Rules for producing ARM_PROGs from ARM_RUNs                                   *)
(* ----------------------------------------------------------------------------- *)

(* ARM_PROG and ARM_CALL introduction rules *)

val EQ_IMP_IMP = METIS_PROVE [] ``(x = y) ==> x ==> y``;

val ARM_RUN_IMP_PROG2 =
  let 
    val th = Q.SPECL [`P`,`[c]`,`Q`,`Q'`,`f`] ARM_PROG_INTRO
    val th = SIMP_RULE std_ss [LENGTH,ms_def,emp_STAR,pcINC_def,pcADD_def,wLENGTH_def] th
    val th = ONCE_REWRITE_RULE [WORD_ADD_COMM] th
    val th = REWRITE_RULE [ARMpc_def,STAR_ASSOC] th
  in MATCH_MP EQ_IMP_IMP th end;

val ARM_RUN_IMP_PROG1 = 
  REWRITE_RULE [F_STAR,SEP_DISJ_CLAUSES,ARM_PROG_FALSE_POST] 
  (Q.INST [`Q'`|->`SEP_F`] ARM_RUN_IMP_PROG2);

val ARM_RUN_IMP_CALL =
  let
    val th' = Q.SPECL [`[c]`,`I`] mpool_eq_ms
    val th' = SIMP_RULE std_ss [LENGTH,ms_def,emp_STAR] th'
    val th = Q.SPECL [`[c]`,`k`] ARM_CALL_THM
    val th = SIMP_RULE std_ss [LENGTH,ms_def,emp_STAR,pcINC_def,pcADD_def,wLENGTH_def] th
    val th = ONCE_REWRITE_RULE [WORD_ADD_COMM] th
    val th = REWRITE_RULE [ARMpc_def,STAR_ASSOC,th'] th
  in MATCH_MP EQ_IMP_IMP (GSYM th) end;


(* main part *)

val ARM_RUN2PROG_THM = prove(
  ``(rx = rx') ==> (ry = ry') ==> 
    (mx = mx') ==> (my = my') ==> 
    (sx = sx') ==> (sy = sy') ==> 
    (c = c') ==>
    (!p. ARM_RUN 
      (one (Reg 15w p) * rx * one (Mem (addr30 p) cmd) * mx * sx * one (Undef F) * c)
      (one (Reg 15w (p+4w)) * ry * one (Mem (addr30 p) cmd) * my * sy * one (Undef F))) ==>
    ARM_PROG (rx' * mx' * sx' * c') [cmd] {} (ry' * my' * sy') {}``,
  REPEAT STRIP_TAC
  \\ MATCH_MP_TAC ARM_RUN_IMP_PROG1
  \\ REPEAT STRIP_TAC
  \\ REWRITE_TAC [R30_def,M_def,R_def,addr32_SUC] 
  \\ PAT_ASSUM ``!a:'a. b`` (STRIP_ASSUME_TAC o RW [addr30_addr32] o Q.SPEC `addr32 p`)  
  \\ FULL_SIMP_TAC std_ss [AC STAR_COMM STAR_ASSOC]
  \\ METIS_TAC []);

fun ARM_RUN2PROG (rx,ry) (mx,my) (sx,sy) c =
  let
    fun f (x,y) = MATCH_MP y x
  in
    RW [STAR_ASSOC,emp_STAR] (foldr f ARM_RUN2PROG_THM (rev [rx,ry,mx,my,sx,sy,c]))
  end;

fun MOVE_STAR_PROVE tm = prove(tm,SIMP_TAC (bool_ss++star_ss) []);

val ee = REFL ``emp:ARMset->bool``;
val ee2 = (ee,ee);
val cc = REFL ``c:ARMset->bool``;
val ss = REFL ``s:ARMset->bool``;
val ss' = REFL ``s':ARMset->bool``;
val ss2 = (ss,ss');
val x1x1 = MOVE_STAR_PROVE ``x1 = (x1 :ARMset->bool)``;
val y1y1 = MOVE_STAR_PROVE ``y1 = (y1 :ARMset->bool)``;
val xy1xy1 = (x1x1,y1y1);
val x12x12 = MOVE_STAR_PROVE ``x1*x2 = (x1*x2 :ARMset->bool)``;
val y12y12 = MOVE_STAR_PROVE ``y1*y2 = (y1*y2 :ARMset->bool)``;
val xy12xy12 = (x12x12,y12y12);
val x12x21 = MOVE_STAR_PROVE ``x1*x2 = (x2*x1 :ARMset->bool)``;
val y12y21 = MOVE_STAR_PROVE ``y1*y2 = (y2*y1 :ARMset->bool)``;
val xy12xy21 = (x12x21,y12y21);
val x123x123 = MOVE_STAR_PROVE ``x1*x2*x3 = (x1*x2*x3 :ARMset->bool)``;
val y123y123 = MOVE_STAR_PROVE ``y1*y2*y3 = (y1*y2*y3 :ARMset->bool)``;
val xy123xy123 = (x123x123,y123y123);
val x123x231 = MOVE_STAR_PROVE ``x1*x2*x3 = (x2*x3*x1 :ARMset->bool)``;
val y123y231 = MOVE_STAR_PROVE ``y1*y2*y3 = (y2*y3*y1 :ARMset->bool)``;
val xy123xy231 = (x123x231,y123y231);
val x123x312 = MOVE_STAR_PROVE ``x1*x2*x3 = (x3*x1*x2 :ARMset->bool)``;
val y123y312 = MOVE_STAR_PROVE ``y1*y2*y3 = (y3*y1*y2 :ARMset->bool)``;
val xy123xy312 = (x123x312,y123y312);
val x1234x2341 = MOVE_STAR_PROVE ``x1*x2*x3*x4 = (x2*x3*x4*x1 :ARMset->bool)``;
val y1234y2341 = MOVE_STAR_PROVE ``y1*y2*y3*y4 = (y2*y3*y4*y1 :ARMset->bool)``;
val xy1234xy2341 = (x1234x2341,y1234y2341);
val x1234x3412 = MOVE_STAR_PROVE ``x1*x2*x3*x4 = (x3*x4*x1*x2 :ARMset->bool)``;
val y1234y3412 = MOVE_STAR_PROVE ``y1*y2*y3*y4 = (y3*y4*y1*y2 :ARMset->bool)``;
val xy1234xy3412 = (x1234x3412,y1234y3412);
val m1m1 = MOVE_STAR_PROVE ``m1 = (m1 :ARMset->bool)``;
val n1n1 = MOVE_STAR_PROVE ``n1 = (n1 :ARMset->bool)``;
val mn1mn1 = (m1m1,n1n1);

val P21    = ARM_RUN2PROG xy1xy1 ee2 ee2 ee
val P21s   = ARM_RUN2PROG xy1xy1 ee2 ss2 ee
val P21sc  = ARM_RUN2PROG xy1xy1 ee2 ss2 cc
val P31    = ARM_RUN2PROG xy12xy12 ee2 ee2 ee
val P31s   = ARM_RUN2PROG xy12xy12 ee2 ss2 ee
val P31sc  = ARM_RUN2PROG xy12xy12 ee2 ss2 cc
val P31sc' = ARM_RUN2PROG xy12xy21 ee2 ss2 cc
val P41sc' = ARM_RUN2PROG xy123xy231 ee2 ss2 cc
val P51sc' = ARM_RUN2PROG xy1234xy2341 ee2 ss2 cc
val P4_MULL = ARM_RUN2PROG xy123xy312 ee2 ss2 cc
val P5_MULL = ARM_RUN2PROG xy1234xy3412 ee2 ss2 cc

val P3_SWP = ARM_RUN2PROG xy12xy12 mn1mn1 ss2 cc
val P4_SWP = ARM_RUN2PROG xy123xy312 mn1mn1 ss2 cc

val P2_STR = ARM_RUN2PROG xy1xy1 mn1mn1 ss2 cc
val P3_STR = ARM_RUN2PROG xy12xy21 mn1mn1 ss2 cc


(* ----------------------------------------------------------------------------- *)
(* Function for producing ARM_PROGs                                              *)
(* ----------------------------------------------------------------------------- *)

val DEFAULT_INST = 
  [``R1:word4``|->``a:word4``,``x1:word32``|->``x:word32``,
   ``R2:word4``|->``b:word4``,``x2:word32``|->``y:word32``,
   ``R3:word4``|->``c:word4``,``x3:word32``|->``z:word32``,
   ``R4:word4``|->``d:word4``,``x4:word32``|->``q:word32``];

val ARM_NOP_LEMMA = prove(
  ``(!sN sZ sC sV p. 
       ARM_RUN
         (one (Reg 15w p) * one (Mem (addr30 p) cmd) *
          one (Status (sN,sZ,sC,sV)) * one (Undef F) *
          cond ~CONDITION_PASSED2 (sN,sZ,sC,sV) c)
         (one (Reg 15w (p + 4w)) *
          one (Mem (addr30 p) cmd) *
          one (Status (sN,sZ,sC,sV)) * one (Undef F))) ==>
    ARM_NOP c [cmd]``,
  REWRITE_TAC [ARM_NOP_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  \\ MATCH_MP_TAC ARM_RUN_IMP_PROG1 \\ REPEAT STRIP_TAC
  \\ REWRITE_TAC [S_def,R_def,M_def,nPASS_def,R30_def,addr32_SUC]
  \\ POP_ASSUM (ASSUME_TAC o RW [addr30_addr32] o Q.SPECL [`q`,`q'`,`q''`,`r`,`addr32 p`])
  \\ FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]);

fun MK_NOP th =
  let
    val th = CLEAN_ARM_RULE_NOP [] th
    val th = MK_ARM_RUN_NOP th
    val th = (Q.GEN `sN` o Q.GEN `sZ` o Q.GEN `sC` o Q.GEN `sV` o Q.GEN `p`) th
  in  
    MATCH_MP ARM_NOP_LEMMA th
  end;

fun MK_PROG_C (conds,shape,insts,prog) rs th i =
  let
    val th = CLEAN_ARM_RULE_C rs th
    val th = MK_ARM_RUN_C (conds,shape,insts) th
    val th = MATCH_MP prog (Q.GEN `p` th)
    val th = RW [GSYM R_def,GSYM M_def, GSYM R30_def, GSYM S_def, GSYM PASS_def] th
    val th = INST i th
  in
    th
  end;

val PROG2_LEMMA = prove(
  ``ARM_NOP c cs ==> ARM_PROG P cs {} Q Z ==> ARM_PROG2 c P cs Q Z``,
  SIMP_TAC bool_ss [ARM_PROG2_def]);

fun MK_PROG2 (conds,shape,insts,prog) rs (th,nop) i =
  let
    val th1 = MK_PROG_C (conds,shape,insts,prog) rs th i
    val th2 = MK_NOP nop
    val th = MATCH_MP PROG2_LEMMA th2
    val th = MATCH_MP th th1
  in
    th
  end;

fun MK_PROG_AL (conds,shape,insts,prog) rs th i =
  let
    val th = CLEAN_ARM_RULE_AL rs th
    val th = MK_ARM_RUN_AL (conds,shape,insts) th
    val th = MATCH_MP prog (Q.GEN `p` th)
    val th = RW [GSYM R_def,GSYM M_def, GSYM R30_def, GSYM S_def] th
    val th = INST i th
  in
    th
  end;


(* ----------------------------------------------------------------------------- *)
(* Function for storing theorems                                                 *)
(* ----------------------------------------------------------------------------- *)

fun store_thms prefix suffix f list = 
  let
    fun g (th,nop,name) = 
      let 
        val st = prefix^name^suffix
     (*   val _ = print(st^"\n") *)
      in 
        save_thm(st,f (th,nop)) 
      end
  in
    map g list
  end;


(* ----------------------------------------------------------------------------- *)
(* Functions for specialising the address modes                                  *)
(* ----------------------------------------------------------------------------- *)

(* address mode 1 *)

val _ = Hol_datatype `
  abbrev_addr1 = OneReg | Imm of word8`;

val ADDR_MODE1_CMD_def = Define `
  (ADDR_MODE1_CMD OneReg Rd = Dp_shift_immediate (LSL Rd) 0w) /\
  (ADDR_MODE1_CMD (Imm k) Rd = Dp_immediate 0w k)`;

val ADDR_MODE1_VAL_def = Define `
  (ADDR_MODE1_VAL OneReg  x c = (c,x)) /\
  (ADDR_MODE1_VAL (Imm k) x c = (c,w2w k))`;

val ADDR_MODE1_VAL_THM = prove( 
  ``!c. ADDR_MODE1 state.registers mode (cpsr %% 29)
         (IS_DP_IMMEDIATE (ADDR_MODE1_CMD c Rd))
         ((11 >< 0) (addr_mode1_encode (ADDR_MODE1_CMD c Rd))) =
        ADDR_MODE1_VAL c (REG_READ state.registers mode Rd) (cpsr %% 29)``,
  Cases_on `c`
  \\ REWRITE_TAC [ADDR_MODE1_CMD_def,ADDR_MODE1_VAL_def]
  \\ REWRITE_TAC [IS_DP_IMMEDIATE_def,shift_immediate_shift_register,ADDR_MODE1_def]
  \\ REWRITE_TAC [immediate_enc,shift_immediate_enc]
  \\ SRW_TAC [] [ROR_def,w2w_def,LSL_def,word_mul_n2w]);

val FIX_ADDR_MODE1 = 
  RW [ADDR_MODE1_VAL_THM] o
  Q.INST [`Op2`|->`ADDR_MODE1_CMD a_mode Rn`] o
  SPEC_ALL;

(* address mode 2 *)

val ADDRESS_ROTATE = prove(
  ``!q:word32 z:word30. q #>> (8 * w2n ((1 >< 0) (addr32 z):word2)) = q``,
  SIMP_TAC std_ss [addr32_eq_0,EVAL ``w2n (0w:word2)``] \\ STRIP_TAC \\ EVAL_TAC);

val _ = Hol_datatype `
  abbrev_addr2' = RegOff' of bool # bool # bool # word12`;

val ADDR_MODE2_CMD1'_def = Define `
  (ADDR_MODE2_CMD1' (RegOff' (pre,up,wb,imm)) = <| Pre:=pre; Up:=up; Wb:=wb |>)`;

val ADDR_MODE2_CMD2'_def = Define `
  (ADDR_MODE2_CMD2' (RegOff' (pre,up,wb,imm)) = Dt_immediate imm)`;

val ADDR_MODE2_ADDR'_def = Define `
  (ADDR_MODE2_ADDR' (RegOff' (F,F,wb,imm)) (x:word32) = x) /\ 
  (ADDR_MODE2_ADDR' (RegOff' (F,T,wb,imm)) (x:word32) = x) /\ 
  (ADDR_MODE2_ADDR' (RegOff' (T,F,wb,imm)) (x:word32) = x - w2w imm) /\
  (ADDR_MODE2_ADDR' (RegOff' (T,T,wb,imm)) (x:word32) = x + w2w imm)`;

val ADDR_MODE2_WB'_def = Define `
  (ADDR_MODE2_WB' (RegOff' (F,F,F,imm)) (x:word32) = x - w2w imm) /\ 
  (ADDR_MODE2_WB' (RegOff' (F,T,F,imm)) (x:word32) = x + w2w imm) /\ 
  (ADDR_MODE2_WB' (RegOff' (F,F,T,imm)) (x:word32) = x - w2w imm) /\ 
  (ADDR_MODE2_WB' (RegOff' (F,T,T,imm)) (x:word32) = x + w2w imm) /\
  (ADDR_MODE2_WB' (RegOff' (T,F,F,imm)) (x:word32) = x) /\ 
  (ADDR_MODE2_WB' (RegOff' (T,T,F,imm)) (x:word32) = x) /\ 
  (ADDR_MODE2_WB' (RegOff' (T,F,T,imm)) (x:word32) = x - w2w imm) /\ 
  (ADDR_MODE2_WB' (RegOff' (T,T,T,imm)) (x:word32) = x + w2w imm)`;

val REG_WRITE_READ = prove(
  ``!rs m r. ~(r = 15w) ==> (REG_WRITE rs m r (REG_READ rs m r) = rs)``,
  REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC bool_ss [REG_WRITE_def,REG_READ_def] \\ SRW_TAC [] [SUBST_def]);

val AM2'_Cases = 
  Cases_on `c` \\ Cases_on `p` \\ Cases_on `r` \\ Cases_on `r'`
  \\ Cases_on `q` \\ Cases_on `q'` \\ Cases_on `q''`;

val ADDR_MODE2_WB'_THM = prove(
  ``!c. ~(Rn = 15w) ==> 
        ((if
            (ADDR_MODE2_CMD1' c).Pre ==> (ADDR_MODE2_CMD1' c).Wb
          then
            INC_PC
              (REG_WRITE state.registers (state_mode state) Rn
                 (SND
                    (ADDR_MODE2 state.registers (state_mode state)
                       (CPSR_READ state.psrs %% 29)
                       (IS_DT_SHIFT_IMMEDIATE (ADDR_MODE2_CMD2' c))
                       (ADDR_MODE2_CMD1' c).Pre
                       (ADDR_MODE2_CMD1' c).Up Rn
                       ((11 >< 0) (addr_mode2_encode (ADDR_MODE2_CMD2' c))))))
          else
            INC_PC state.registers) =
          INC_PC (REG_WRITE state.registers (state_mode state) Rn 
            (ADDR_MODE2_WB' c (REG_READ state.registers (state_mode state) Rn))))``,
  AM2'_Cases
  \\ SRW_TAC [] [ADDR_MODE2_CMD1'_def,ADDR_MODE2_CMD2'_def]
  \\ REWRITE_TAC [ADDR_MODE2_WB'_def,immediate_enc2]
  \\ REWRITE_TAC [ADDR_MODE2_def,IS_DT_SHIFT_IMMEDIATE_def]
  \\ SIMP_TAC bool_ss [LET_DEF,pairTheory.FST,UP_DOWN_def]
  \\ SRW_TAC [] [REG_WRITE_READ]);

val ADDR_MODE2_ADDR'_THM = prove(
  ``!c. FST (ADDR_MODE2 state.registers (state_mode state)
             (CPSR_READ state.psrs %% 29)
             (IS_DT_SHIFT_IMMEDIATE (ADDR_MODE2_CMD2' c))
             (ADDR_MODE2_CMD1' c).Pre (ADDR_MODE2_CMD1' c).Up
               Rn ((11 >< 0) (addr_mode2_encode (ADDR_MODE2_CMD2' c)))) =
        ADDR_MODE2_ADDR' c (REG_READ state.registers (state_mode state) Rn)``,
  AM2'_Cases
  \\ SRW_TAC [] [ADDR_MODE2_CMD1'_def,ADDR_MODE2_CMD2'_def]
  \\ REWRITE_TAC [ADDR_MODE2_ADDR'_def]
  \\ REWRITE_TAC [ADDR_MODE2_def,IS_DT_SHIFT_IMMEDIATE_def]
  \\ SIMP_TAC bool_ss [LET_DEF,pairTheory.FST,UP_DOWN_def]
  \\ REWRITE_TAC [immediate_enc2]);

(* address mode 2 aligned *)

val _ = Hol_datatype `
  abbrev_addr2 = RegOff of bool # bool # bool # word8`;

val MAKE_NONALIGNED_def = Define `
  (MAKE_NONALIGNED (RegOff (pre,up,wb,imm)) = RegOff' (pre,up,wb,w2w imm << 2))`;

val ADDR_MODE2_CMD1_def = Define `
  (ADDR_MODE2_CMD1 (RegOff (pre,up,wb,imm)) = <| Pre:=pre; Up:=up; Wb:=wb |>)`;

val ADDR_MODE2_CMD2_def = Define `
  (ADDR_MODE2_CMD2 (RegOff (pre,up,wb,imm)) = Dt_immediate ((w2w imm) << 2))`;

val ADDR_MODE2_ADDR_def = Define `
  (ADDR_MODE2_ADDR (RegOff (F,F,wb,imm)) (x:word30) = x) /\ 
  (ADDR_MODE2_ADDR (RegOff (F,T,wb,imm)) (x:word30) = x) /\ 
  (ADDR_MODE2_ADDR (RegOff (T,F,wb,imm)) (x:word30) = x - w2w imm) /\
  (ADDR_MODE2_ADDR (RegOff (T,T,wb,imm)) (x:word30) = x + w2w imm)`;

val ADDR_MODE2_WB_def = Define `
  (ADDR_MODE2_WB (RegOff (F,F,F,imm)) (x:word30) = x - w2w imm) /\ 
  (ADDR_MODE2_WB (RegOff (F,T,F,imm)) (x:word30) = x + w2w imm) /\ 
  (ADDR_MODE2_WB (RegOff (F,F,T,imm)) (x:word30) = x - w2w imm) /\ 
  (ADDR_MODE2_WB (RegOff (F,T,T,imm)) (x:word30) = x + w2w imm) /\
  (ADDR_MODE2_WB (RegOff (T,F,F,imm)) (x:word30) = x) /\ 
  (ADDR_MODE2_WB (RegOff (T,T,F,imm)) (x:word30) = x) /\ 
  (ADDR_MODE2_WB (RegOff (T,F,T,imm)) (x:word30) = x - w2w imm) /\ 
  (ADDR_MODE2_WB (RegOff (T,T,T,imm)) (x:word30) = x + w2w imm)`;

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

val w2w_ror_w2w = prove(
  ``!w. w2w (((w2w (w:word8)):word12) << 2):word32 = (w2w w) << 2``,
  wordsLib.Cases_word
  \\ REWRITE_TAC [w2w_def,n2w_11,n2w_lsl]
  \\ ASM_SIMP_TAC bool_ss [w2n_n2w]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (x MOD g = y MOD g)``)
  \\ MATCH_MP_TAC LESS_MOD
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
  \\ `n MOD 256 < 256` by METIS_TAC [EVAL ``0 < 256``,DIVISION]
  \\ DECIDE_TAC);

val MULT_MOD_MULT = prove(
  ``!k m n. 0 < k /\ 0 < n ==> ((m MOD k) * n = (m*n) MOD (k*n))``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (UNDISCH (Q.SPECL [`m`,`k`] DA))
  \\ ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB,GSYM MULT_ASSOC]  
  \\ `0 < k * n` by ASM_SIMP_TAC bool_ss [LESS_MULT2]  
  \\ `r * n < k * n` by ASM_SIMP_TAC bool_ss [LT_MULT_RCANCEL]
  \\ ASM_SIMP_TAC bool_ss [MOD_MULT]);

val ADD_MODE2_ADD_LEMMA = prove(
  ``!x imm. w2w (x:word30) << 2 + w2w (imm:word8) << 2 = (w2w (x + w2w imm) << 2) :word32``,
  wordsLib.Cases_word
  \\ wordsLib.Cases_word
  \\ REWRITE_TAC [w2w_def,n2w_lsl,word_add_n2w,GSYM RIGHT_ADD_DISTRIB]
  \\ REWRITE_TAC [GSYM word_add_n2w]
  \\ REWRITE_TAC [word_add_def] 
  \\ ASM_SIMP_TAC std_ss [w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
  \\ `n' < 1073741824` by DECIDE_TAC
  \\ `0 < 1073741824 /\ 0 < 4 /\ 0 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LESS_MOD,MULT_MOD_MULT]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [MOD_MOD]);
  
val ADD_MODE2_SUB_LEMMA = prove(
  ``!x imm. w2w (x:word30) << 2 - w2w (imm:word8) << 2 = (w2w (x - w2w imm) << 2) :word32``,
  wordsLib.Cases_word
  \\ wordsLib.Cases_word
  \\ REWRITE_TAC [w2w_def,n2w_lsl]
  \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD]
  \\ REWRITE_TAC [word_sub_def,word_2comp_n2w]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
  \\ `n' * 4 < 4294967296` by DECIDE_TAC
  \\ `n' < 1073741824` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [LESS_MOD,word_add_n2w,w2n_n2w]
  \\ `0 < 1073741824 /\ 0 < 4 /\ 0 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [MULT_MOD_MULT,RIGHT_ADD_DISTRIB,RIGHT_SUB_DISTRIB]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [MOD_MOD]);

val ADDR_MODE2_WB_THM = prove(
  ``!c x. ADDR_MODE2_WB' (MAKE_NONALIGNED c) (addr32 x) =
          addr32 (ADDR_MODE2_WB c x)``,
  AM2'_Cases
  \\ REWRITE_TAC [MAKE_NONALIGNED_def]
  \\ REWRITE_TAC [ADDR_MODE2_WB'_def,ADDR_MODE2_WB_def,addr32_def,w2w_ror_w2w]
  \\ REWRITE_TAC [ADD_MODE2_ADD_LEMMA,ADD_MODE2_SUB_LEMMA]);

val ADDR_MODE2_ADDR_THM = prove(
  ``!c x. addr30 (ADDR_MODE2_ADDR' (MAKE_NONALIGNED c) (addr32 x)) =
          ADDR_MODE2_ADDR c x``,
  AM2'_Cases
  \\ REWRITE_TAC [MAKE_NONALIGNED_def]
  \\ REWRITE_TAC [ADDR_MODE2_ADDR'_def,ADDR_MODE2_ADDR_def,addr30_def,addr32_def,w2w_ror_w2w]
  \\ REWRITE_TAC [ADD_MODE2_ADD_LEMMA,ADD_MODE2_SUB_LEMMA]
  \\ REWRITE_TAC [GSYM addr32_def,GSYM addr30_def,addr30_addr32]);

val ADDR_MODE2_ADDR_THM = prove(
  ``!c x. ADDR_MODE2_ADDR' (MAKE_NONALIGNED c) (addr32 x) =
          addr32 (ADDR_MODE2_ADDR c x)``,
  AM2'_Cases
  \\ REWRITE_TAC [MAKE_NONALIGNED_def]
  \\ REWRITE_TAC [ADDR_MODE2_ADDR'_def,ADDR_MODE2_ADDR_def,addr30_def,addr32_def,w2w_ror_w2w]
  \\ REWRITE_TAC [ADD_MODE2_ADD_LEMMA,ADD_MODE2_SUB_LEMMA]
  \\ REWRITE_TAC [GSYM addr32_def,GSYM addr30_def,addr30_addr32]);

val ADDR_MODE2_CMD1_THM = prove(
  ``!c x. ADDR_MODE2_CMD1' (MAKE_NONALIGNED c) = ADDR_MODE2_CMD1 c``,
  AM2'_Cases \\ REWRITE_TAC [ADDR_MODE2_CMD1_def,ADDR_MODE2_CMD1'_def,MAKE_NONALIGNED_def]);

val ADDR_MODE2_CMD2_THM = prove(
  ``!c x. ADDR_MODE2_CMD2' (MAKE_NONALIGNED c) = ADDR_MODE2_CMD2 c``,
  AM2'_Cases \\ REWRITE_TAC [ADDR_MODE2_CMD2_def,ADDR_MODE2_CMD2'_def,MAKE_NONALIGNED_def]);


(* ----------------------------------------------------------------------------- *)
(* BRANCH INSTRUCTIONS                                                           *)
(* ----------------------------------------------------------------------------- *)

(* lemmas *)

val sw2sw_EQ_w2w_sw2sw = prove(
  ``sw2sw (w:word24) << 2 = (w2w ((sw2sw w):word30) << 2) :word32``,
  REWRITE_TAC [sw2sw_def,w2w_def,bitTheory.SIGN_EXTEND_def]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [LET_DEF]
  \\ Cases_on `BIT 23 (w2n w)`
  \\ ASM_REWRITE_TAC []
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2n_n2w,word_lsl_n2w,n2w_11]
  \\ `0 < 1073741824` by EVAL_TAC
  \\ `!x. (x MOD 1073741824) * 4 = (4 * x) MOD (4 * 1073741824)` 
         by METIS_TAC [MULT_SYM,MOD_COMMON_FACTOR,EVAL ``0<4``]
  \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC std_ss [MOD_MOD]
  \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [MULT_SYM]))
  \\ REWRITE_TAC []
  \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB]
  \\ ONCE_REWRITE_TAC 
        [(RW [EVAL ``0 < 4294967296``] o GSYM o Q.SPEC `4294967296`) MOD_PLUS]
  \\ SIMP_TAC std_ss []);

val word_add_w2n = prove(
  ``!w v:'a word. w2n (w + v) = (w2n w + w2n v) MOD dimword (:'a)``,
  REWRITE_TAC [word_add_def,w2n_n2w]);

val w2w_add_lsl = prove(
  ``w2w w << 2 + w2w v << 2 = (w2w (w+v:word30) << 2) :word32``,
  SRW_TAC [] [w2w_def,word_lsl_n2w,WORD_ADD_0,word_add_n2w]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
  \\ REWRITE_TAC [GSYM (EVAL ``1073741824 * 4``),GSYM RIGHT_ADD_DISTRIB]
  \\ ONCE_REWRITE_TAC [MULT_SYM]  
  \\ `!x. (4 * x) MOD (4 * 1073741824) = 4 * (x MOD 1073741824)` 
         by METIS_TAC [MOD_COMMON_FACTOR,EVAL ``0<4``,EVAL ``0 < 1073741824``]
  \\ `!x y. (4 * x = 4 * y) = (x = y)` by METIS_TAC [EQ_MULT_LCANCEL,EVAL ``0=4``]
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [wordsLib.SIZES_ss] [word_add_w2n]);

val PC_SIMP_LEMMA = prove(
  ``w2w (p:word30) << 2 + 8w + sw2sw (offset:word24) << 2 = 
    (w2w (p + 2w + sw2sw offset) << 2):word32``,
  REWRITE_TAC [GSYM (EVAL ``((w2w (2w:word30)):word32) << 2``)]
  \\ REWRITE_TAC [sw2sw_EQ_w2w_sw2sw]
  \\ REWRITE_TAC [w2w_add_lsl]);

val PC_SIMP = prove(
  ``addr32 p + 8w + sw2sw (offset:word24) << 2 = 
    addr32 (pcADD (sw2sw offset + 2w) p)``,
  SIMP_TAC bool_ss [pcADD_def,PC_SIMP_LEMMA,addr32_def]
  \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

(* the branch instruction: ARM_B *)

val ARM_UNCONDITIONAL_JUMP = 
  let
    val th = CLEAN_ARM_RULE_AL [] ARM_B
    val b = MK_ARM_RUN (c11FTF,Sb11FTF,[]) th ``T``
    val b = Q.INST [`p:word32`|->`addr32 p`] b
    val b = MOVE_STAR_RULE `x*y*z` `y*x*z` b
    val b = RW [PC_SIMP,addr30_addr32] b
    val b = RW [GSYM M_def,GSYM R30_def,GSYM R_def] b
    val b = Q.GEN `p` b
    val th = Q.INST [`Q`|->`SEP_F`,`P`|->`emp`,`Q'`|->`emp`] ARM_RUN_IMP_PROG2
    val th = SIMP_RULE (bool_ss++sep_ss) [] th
  in
    MATCH_MP th b
  end; 

val _ = save_thm("arm_B_AL",ARM_UNCONDITIONAL_JUMP);

val ARM_RUN_PUSH_COND = prove(
  ``!P Q g. ARM_RUN (P * cond g) Q ==> ARM_RUN (P * cond g) (Q * cond g)``,
  REPEAT STRIP_TAC
  \\ `ARM_RUN (P * cond g * cond g) (Q * cond g)` by METIS_TAC [ARM_RUN_FRAME]
  \\ FULL_SIMP_TAC (bool_ss++sep_ss) [GSYM STAR_ASSOC]);

val ARM_CONDITIONAL_JUMP = 
  let
    val th  = CLEAN_ARM_RULE_C [] ARM_B 
    val th' = CLEAN_ARM_RULE_NOP [] ARM_B_NOP 
    val b = MK_ARM_RUN_C (c11TTF,Sb11TTF,[]) th
    val b = MATCH_MP ARM_RUN_PUSH_COND b
    val b' = MK_ARM_RUN_NOP th'
    val b' = MATCH_MP ARM_RUN_PUSH_COND b'
    val merge = Q.SPECL [`P`,`P'`,`SEP_F`,`Q`,`Q'`] ARM_RUN_COMPOSE
    val merge = GEN_ALL (SIMP_RULE (bool_ss++sep_ss) [] merge)
    val th = MATCH_MP merge (CONJ b' b)
    val th = SIMP_RULE (bool_ss++sep_ss) [STAR_OVER_DISJ] th
    val th = Q.GEN `p` (Q.INST [`p:word32`|->`addr32 p`] th)
    val th = RW [addr30_addr32,GSYM addr32_SUC,PC_SIMP] th
    val th = RW [GSYM M_def,GSYM R30_def,GSYM R_def,GSYM S_def,GSYM PASS_def,GSYM nPASS_def] th
    val th = MOVE_STAR_RULE `p*m*s*u` `s*m*p*u` th    
    val th = MOVE_STAR_RULE `u*s*(p*m)*n` `(s*n)*m*p*u` th    
    val th = MATCH_MP ARM_RUN_IMP_PROG2 th
  in th end;

val _ = save_thm("arm_B",ARM_CONDITIONAL_JUMP);


(* procedure calls: ARM_BL *)

val ARM_BL_REWRITE_LEMMA = prove(
  ``!m. ~(num2register (mode_reg2num m 14w) = r15)``,
  Cases_on `m` 
  \\ SRW_TAC [wordsLib.SIZES_ss] [mode_reg2num_def,USER_def]
  \\ Q.UNABBREV_TAC `n`
  \\ SRW_TAC [] [num2register_thm]);

val ARM_BL_REWRITE_THM = prove(
  ``INC_PC s.registers = 
    REG_WRITE (INC_PC s.registers) (state_mode s) 14w 
      (REG_READ s.registers (state_mode s) 14w)``,
  SRW_TAC [wordsLib.SIZES_ss] [INC_PC_def,REG_WRITE_def,REG_READ_def,SUBST_def,FUN_EQ_THM]
  \\ Cases_on `x = r15` \\ ASM_REWRITE_TAC [ARM_BL_REWRITE_LEMMA] 
  \\ `~(r15 = x)` by METIS_TAC []
  \\ ASM_REWRITE_TAC [] \\ METIS_TAC []);

val ARM_UNCONDITIONAL_CALL = 
  let
    val (c1,c2,c3) = c21FTF
    val g = Q.INST [`R1`|->`14w`] 
    val conds = (g c1, g c2, g c3)
    val shape = Q.INST [`R1`|->`14w`] Srb21FTF
    val th = ONCE_REWRITE_RULE [ARM_BL_REWRITE_THM] ARM_BL
    val th = CLEAN_ARM_RULE_AL [] th
    val b = MK_ARM_RUN (conds,shape,[]) th ``T``
    val b = Q.INST [`p:word32`|->`addr32 p`] b
    val b = RW [PC_SIMP,addr30_addr32] b
    val b = RW [GSYM M_def,GSYM R30_def,GSYM R_def,GSYM S_def] b
    val b = RW [GSYM addr32_SUC,GSYM R30_def] b
    val b = Q.GEN `x1` b
    val b = MOVE_STAR_RULE `p*lr*m*u` `(p*m*u)*lr` b
    val b = RW [ARM_RUN_HIDE_PRE] b
    val b = Q.GEN `p` b    
    val b = MOVE_STAR_RULE `(p*m*u)*lr` `lr*p*u*m` b
    val lemma = prove(``pcADD k p = p + k``,SIMP_TAC std_ss [pcADD_def,WORD_ADD_COMM])
    val b = MATCH_MP ARM_RUN_IMP_CALL (RW [lemma] b)
  in b end;

val _ = save_thm("arm_BL",ARM_UNCONDITIONAL_CALL);


(* procedure returns: MOV_PC *)

val MOV_PC_LEMMA = 
  (RW [EVAL ``0w = 15w:word4``] o Q.INST [`Rm`|->`0w`] o
   RW [ADDR_MODE1_VAL_def,ADDR_MODE1_CMD_def] o 
   Q.INST [`s`|->`F`,`a_mode`|->`OneReg`] o
   FIX_ADDR_MODE1) ARM_MOV_PC;

val MOV_PC = 
  let
    val conds = c21TTF
    val shape = Sb21TTF
    val th = MOV_PC_LEMMA
    val th = CLEAN_ARM_RULE_C [``Rn:word4``] th
    val b = MK_ARM_RUN_C (conds,shape,[]) th
    val b = RW [GSYM R_def] b
    val b = Q.INST [`R1`|->`a`,`x1`|->`addr32 (pcSET x (p:word30))`,`p`|->`addr32 p`] b
    val b = RW [GSYM R30_def,GSYM R_def,GSYM M_def,addr30_addr32,GSYM S_def] b
    val b = RW [pcSET_def] b
    val b = MOVE_STAR_RULE `p*lr*m*s*u` `(lr*s)*m*p*u` b
    val b = MOVE_STAR_RULE `m*u*s*(p*lr)*c` `(lr*s*c)*m*p*u` b
    val th = Q.INST [`Q`|->`SEP_F`] ARM_RUN_IMP_PROG2
    val th = SIMP_RULE (bool_ss++sep_ss) [] th
    val th = Q.INST [`f`|->`pcSET x`] th
    val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [pcSET_def])) th
    val b = MATCH_MP th (Q.GEN `p` b)
    val b = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [STAR_COMM])) b
    val b = RW [R30_def] b
    val b = MATCH_MP ARM_PROG_HIDE_POST b
    val b = RW [GSYM R30_def] b
    val b = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [STAR_COMM])) b
    val th = MATCH_MP PROG2_LEMMA (MK_NOP ARM_MOV_NOP)
    val th = MATCH_MP th b 
    val th = RW [GSYM PASS_def] th
  in save_thm("arm_MOV_PC",th) end;


(* ----------------------------------------------------------------------------- *)
(* COMPARISON INSTRUCTIONS                                                       *)
(* ----------------------------------------------------------------------------- *)

fun MK_COMPARE2 (th,nop) =
  let
    val th = FIX_ADDR_MODE1 th
    val rs = [``Rm:word4``,``Rn:word4``]
    val (conds,shape,prog) = (c31TTF,Sis31TTF,P31sc)
    val i = DEFAULT_INST
  in
    MK_PROG2 (conds,shape,[],prog) rs (th,nop) i
  end;


fun MK_COMPARE1 (th,nop) =
  let
    val th = Q.INST [`Rm`|->`Rn`] (SPEC_ALL th)
    val th = FIX_ADDR_MODE1 th
    val rs = [``Rn:word4``]
    val (conds,shape,prog) = (c21TTF,Sis21TTF,P21sc)
    val i = DEFAULT_INST
  in
    MK_PROG2 (conds,shape,[],prog) rs (th,nop) i
  end;

val cmps = [(ARM_CMN,ARM_CMN_NOP,"CMN"),
            (ARM_CMP,ARM_CMP_NOP,"CMP"),
            (ARM_TST,ARM_TST_NOP,"TST"),
            (ARM_TEQ,ARM_TEQ_NOP,"TEQ")];

val _ = store_thms "arm_" "1" MK_COMPARE1 cmps
val _ = store_thms "arm_" "2" MK_COMPARE2 cmps


(* ----------------------------------------------------------------------------- *)
(* MONOP INSTRUCTIONS                                                            *)
(* ----------------------------------------------------------------------------- *)

val MONOP2_INST = 
  [``R1:word4``|->``b:word4``,``x1:word32``|->``y:word32``,
   ``R2:word4``|->``a:word4``,``x2:word32``|->``x:word32``];

fun MK_MONOP2 (th,nop) = 
  let
    val th = FIX_ADDR_MODE1 th
    val th = Q.INST [`Rm`|->`Rd`] th
    val rs = [``Rd:word4``,``Rn:word4``]
  in
    MK_PROG2 (c31TTF,Sirs31TTF,[],P31sc') rs (th,nop) MONOP2_INST
  end;

fun MK_MONOP1 (th,nop) = 
  let
    val th = FIX_ADDR_MODE1 th
    val th = Q.INST [`Rm`|->`Rn`,`Rd`|->`Rn`] th
    val rs = [``Rn:word4``]
  in
    MK_PROG2 (c21TTF,Sirs21TTF,[],P21sc) rs (th,nop) DEFAULT_INST
  end;

val monops = [(ARM_MOV,ARM_MOV_NOP,"MOV"),
              (ARM_MVN,ARM_MVN_NOP,"MVN")];

val _ = store_thms "arm_" "1" MK_MONOP1 monops
val _ = store_thms "arm_" "2" MK_MONOP2 monops


(* ----------------------------------------------------------------------------- *)
(* BINOP INSTRUCTIONS (EXCEPT MULTIPLICATION)                                    *)
(* ----------------------------------------------------------------------------- *)

(* naming convention: 
    1: ADD xxx; 2: ADD yxy; 2': ADD xxy; 2'': ADD yxx; 3: ADD zxy
*)

val BINOP4_INST = 
  [``R1:word4``|->``d:word4``,``x1:word32``|->``z:word32``,
   ``R2:word4``|->``a:word4``,``x2:word32``|->``x:word32``,
   ``R3:word4``|->``b:word4``,``x3:word32``|->``y:word32``,
   ``R4:word4``|->``c:word4``,``x4:word32``|->``k:word32``];

val BINOP3_INST = 
  [``R1:word4``|->``c:word4``,``x1:word32``|->``z:word32``,
   ``R2:word4``|->``a:word4``,``x2:word32``|->``x:word32``,
   ``R3:word4``|->``b:word4``,``x3:word32``|->``y:word32``];

val BINOP2_INST = 
  [``R1:word4``|->``b:word4``,``x1:word32``|->``y:word32``,
   ``R2:word4``|->``a:word4``,``x2:word32``|->``x:word32``];

fun MK_BINOP3 (th,nop) = 
  let
    val th = FIX_ADDR_MODE1 th
    val rs = [``Rd:word4``,``Rm:word4``,``Rn:word4``]
  in
    MK_PROG2 (c41TTF,Sirs41TTF,[],P41sc') rs (th,nop) BINOP3_INST
  end;

fun MK_BINOP2 (th,nop) = 
  let
    val th = Q.INST [`Rm`|->`Rm`,`Rd`|->`Rn`] (SPEC_ALL th)
    val th = FIX_ADDR_MODE1 th
    val rs = [``Rn:word4``,``Rm:word4``]
  in
    MK_PROG2 (c31TTF,Sirs31TTF,[],P31sc') rs (th,nop) BINOP2_INST
  end;

fun MK_BINOP2' (th,nop) = 
  let
    val th = Q.INST [`Rm`|->`Rm`,`Rd`|->`Rm`] (SPEC_ALL th)
    val th = FIX_ADDR_MODE1 th
    val rs = [``Rm:word4``,``Rn:word4``]
  in
    MK_PROG2 (c31TTF,Sirs31TTF,[],P31sc) rs (th,nop) DEFAULT_INST
  end;

fun MK_BINOP2'' (th,nop) = 
  let
    val th = Q.INST [`Rm`|->`Rn`,`Rd`|->`Rm`] (SPEC_ALL th)
    val th = FIX_ADDR_MODE1 th
    val rs = [``Rm:word4``,``Rn:word4``]
  in
    MK_PROG2 (c31TTF,Sirs31TTF,[],P31sc') rs (th,nop) BINOP2_INST
  end;

fun MK_BINOP1 (th,nop) = 
  let
    val th = Q.INST [`Rm`|->`Rn`,`Rd`|->`Rn`] (SPEC_ALL th)
    val th = FIX_ADDR_MODE1 th
    val rs = [``Rn:word4``]
  in
    MK_PROG2 (c21TTF,Sirs21TTF,[],P21sc) rs (th,nop) DEFAULT_INST
  end;

val binops = [(ARM_ADC,ARM_ADC_NOP,"ADC"),
              (ARM_ADD,ARM_ADD_NOP,"ADD"),
              (ARM_AND,ARM_AND_NOP,"AND"),
              (ARM_BIC,ARM_BIC_NOP,"BIC"),
              (ARM_EOR,ARM_EOR_NOP,"EOR"),
              (ARM_ORR,ARM_ORR_NOP,"ORR"),
              (ARM_RSB,ARM_RSB_NOP,"RSB"),
              (ARM_RSC,ARM_RSC_NOP,"RSC"),
              (ARM_RSC,ARM_RSC_NOP,"SBC"),
              (ARM_SUB,ARM_SUB_NOP,"SUB")];

val _ = store_thms "arm_" "1" MK_BINOP1 binops
val _ = store_thms "arm_" "2" MK_BINOP2 binops
val _ = store_thms "arm_" "2'" MK_BINOP2' binops
val _ = store_thms "arm_" "2''" MK_BINOP2'' binops
val _ = store_thms "arm_" "3" MK_BINOP3 binops


(* ----------------------------------------------------------------------------- *)
(* 32 bit MULTIPLICATION INSTRUCTIONS                                            *)
(* ----------------------------------------------------------------------------- *)

val MUL3 = 
  let
    val rs = [``Rd:word4``,``Rm:word4``,``Rs:word4``]
  in
    MK_PROG2 (c41TTF,Sris41TTF,[],P41sc') rs (ARM_MUL,ARM_MUL_NOP) BINOP3_INST
  end;

val MUL2 = 
  let
    val th = Q.INST [`Rd`|->`Rs`] (SPEC_ALL ARM_MUL)
    val rs = [``Rs:word4``,``Rm:word4``]
  in
    MK_PROG2 (c31TTF,Sris31TTF,[],P31sc') rs (th,ARM_MUL_NOP) BINOP2_INST
  end;

val MUL2'' = 
  let
    val th = Q.INST [`Rm`|->`Rs`] (SPEC_ALL ARM_MUL)
    val rs = [``Rd:word4``,``Rs:word4``]
  in
    MK_PROG2 (c31TTF,Sris31TTF,[],P31sc') rs (th,ARM_MUL_NOP) BINOP2_INST
  end;

val _ = save_thm("arm_MUL3",MUL3);
val _ = save_thm("arm_MUL2",MUL2);
val _ = save_thm("arm_MUL2''",MUL2'');

val MLA4 = 
  let
    val th = ONCE_REWRITE_RULE [WORD_ADD_COMM] ARM_MLA
    val rs = [``Rd:word4``,``Rm:word4``,``Rs:word4``,``Rn:word4``]
  in
    MK_PROG2 (c51TTF,Sris51TTF,[],P51sc') rs (th,ARM_MLA_NOP) BINOP4_INST
  end;

val MLA3 = 
  let
    val th = ONCE_REWRITE_RULE [WORD_ADD_COMM] ARM_MLA
    val th = Q.INST [`Rs`|->`Rd`] (SPEC_ALL th)
    val rs = [``Rd:word4``,``Rm:word4``,``Rn:word4``]
  in
    MK_PROG2 (c41TTF,Sris41TTF,[],P41sc') rs (th,ARM_MLA_NOP) BINOP3_INST
  end;

val MLA3' = 
  let
    val th = ONCE_REWRITE_RULE [WORD_ADD_COMM] ARM_MLA
    val th = Q.INST [`Rn`|->`Rd`] (SPEC_ALL th)
    val rs = [``Rd:word4``,``Rm:word4``,``Rs:word4``]
  in
    MK_PROG2 (c41TTF,Sris41TTF,[],P41sc') rs (th,ARM_MLA_NOP) BINOP3_INST
  end;

val MLA3'' = 
  let
    val th = ONCE_REWRITE_RULE [WORD_ADD_COMM] ARM_MLA
    val th = Q.INST [`Rs`|->`Rm`] (SPEC_ALL th)
    val rs = [``Rd:word4``,``Rm:word4``,``Rn:word4``]
  in
    MK_PROG2 (c41TTF,Sris41TTF,[],P41sc') rs (th,ARM_MLA_NOP) BINOP3_INST
  end;

val _ = save_thm("arm_MLA4",MLA4);
val _ = save_thm("arm_MLA3",MLA3);
val _ = save_thm("arm_MLA3'",MLA3');
val _ = save_thm("arm_MLA3''",MLA3'');


(* ----------------------------------------------------------------------------- *)
(* 64 bit MULTIPLICATION INSTRUCTIONS                                            *)
(* ----------------------------------------------------------------------------- *)

val MULL_INST = 
  [``R1:word4``|->``c:word4``,``x1:word32``|->``z:word32``,
   ``R2:word4``|->``c':word4``,``x2:word32``|->``z':word32``,
   ``R3:word4``|->``a:word4``,``x3:word32``|->``x:word32``,
   ``R4:word4``|->``b:word4``,``x4:word32``|->``y:word32``];

fun MK_MULL4 (th,nop) = 
  let
    val rs = [``RdLo:word4``,``RdHi:word4``,``Rm:word4``,``Rs:word4``]
  in
    MK_PROG2 (c51TTF,Srris51TTF,[],P5_MULL) rs (th,nop) MULL_INST
  end;

fun MK_MULL3 (th,nop) = 
  let
    val th = Q.INST [`Rs`|->`RdLo`] (SPEC_ALL th)
    val rs = [``RdLo:word4``,``RdHi:word4``,``Rm:word4``]
  in
    MK_PROG2 (c41TTF,Srris41TTF,[],P4_MULL) rs (th,nop) MULL_INST
  end;

fun MK_MULL3' (th,nop) = 
  let
    val th = Q.INST [`Rs`|->`RdHi`] (SPEC_ALL th)
    val rs = [``RdLo:word4``,``RdHi:word4``,``Rm:word4``]
  in
    MK_PROG2 (c41TTF,Srris41TTF,[],P4_MULL) rs (th,nop) MULL_INST
  end;

fun MK_MULL3'' (th,nop) = 
  let
    val th = Q.INST [`Rs`|->`Rm`] (SPEC_ALL th)
    val rs = [``RdLo:word4``,``RdHi:word4``,``Rm:word4``]
  in
    MK_PROG2 (c41TTF,Srris41TTF,[],P4_MULL) rs (th,nop) MULL_INST
  end;

val mulls = [(ARM_UMULL,ARM_UMULL_NOP,"UMULL"),
             (ARM_SMULL,ARM_SMULL_NOP,"SMULL"),
             (ARM_SMULL,ARM_SMULL_NOP,"UMLAL"),
             (ARM_SMULL,ARM_SMULL_NOP,"SMLAL")];

val _ = store_thms "arm_" "4" MK_MULL4 mulls
val _ = store_thms "arm_" "3" MK_MULL3 mulls
val _ = store_thms "arm_" "3'" MK_MULL3' mulls
val _ = store_thms "arm_" "3''" MK_MULL3'' mulls


(* ----------------------------------------------------------------------------- *)
(* SWP INSTRUCTION                                                               *)
(* ----------------------------------------------------------------------------- *)

val SWP3_INST = 
  [``R1:word4``|->``b:word4``,``x1:word32``|->``y:word32``,
   ``R2:word4``|->``c:word4``,``x2:word32``|->``z:word32``,
   ``R3:word4``|->``a:word4``,``x3:word32``|->``x:word32``,
   ``m2:word32``|->``q:word32``];

val SWP2_INST = 
  [``R1:word4``|->``a:word4``,``x1:word32``|->``x:word32``,
   ``R2:word4``|->``b:word4``,``x2:word32``|->``y:word32``,
   ``m2:word32``|->``q:word32``];

val SWP3_NONALIGNED = 
  let
    val f = RW [GSYM addr30_def] o Q.INST [`b`|->`F`] o SPEC_ALL
    val (th,nop) = (f ARM_SWP,f ARM_SWP_NOP)
    val rs = [``Rd:word4``,``Rn:word4``,``Rm:word4``]
    val (conds,shape,prog) = (c42TTF,Srim42TTF,P4_SWP)
    val insts = [``M2:word32``|->``x2:word32``]
    val i = SWP3_INST
    val th = CLEAN_ARM_RULE_C rs th
    val c = ``CONDITION_PASSED2 (sN,sZ,sC,sV) c``
    val th = MK_PROG2 (conds,shape,insts,prog) rs (th,nop) i
  in save_thm("arm_SWP3_NONALIGNED",th) end;

val SWP3 = 
  let
    val th = Q.INST [`z`|->`addr32 z`] SWP3_NONALIGNED
    val th = RW [ADDRESS_ROTATE,addr30_addr32,GSYM R30_def] th    
  in save_thm("arm_SWP3",th) end;

val SWP2_NONALIGNED = 
  let
    val f = RW [GSYM addr30_def] o Q.INST [`b`|->`F`] o SPEC_ALL
    val f = Q.INST [`Rm`|->`Rd`] o f
    val (th,nop) = (f ARM_SWP,f ARM_SWP_NOP)
    val rs = [``Rd:word4``,``Rn:word4``]
    val (conds,shape,prog) = (c32TTF,Srim32TTF,P3_SWP)
    val insts = [``M2:word32``|->``x2:word32``]
    val i = SWP2_INST
    val th = MK_PROG2 (conds,shape,insts,prog) rs (th,nop) i
  in save_thm("arm_SWP2_NONALIGNED",th) end;

val SWP2 = 
  let
    val th = Q.INST [`y`|->`addr32 y`] SWP2_NONALIGNED
    val th = RW [ADDRESS_ROTATE,addr30_addr32,GSYM R30_def] th    
  in save_thm("arm_SWP2",th) end;


(* ----------------------------------------------------------------------------- *)
(* LDR and STR INSTRUCTIONS                                                      *)
(* ----------------------------------------------------------------------------- *)

val FORMAT_UnsignedWord = SIMP_CONV (srw_ss()) [FORMAT_def] ``FORMAT UnsignedWord x y``;

fun FIX_ADDR_MODE2 th = 
  let
    val th = SPEC_ALL th
    val th = DISCH_ALL (ASM_UNABBREV_ALL_RULE (UD_ALL th))
    val th = RW [GSYM state_mode_def] th
    val th = Q.GEN `opt` (Q.GEN `offset` th)
    val th = Q.INST [`b`|->`F`] th
    val th = Q.ISPEC `ADDR_MODE2_CMD1' a_mode` th
    val th = Q.ISPEC `ADDR_MODE2_CMD2' a_mode` th
    val th = SIMP_RULE bool_ss [ADDR_MODE2_WB'_THM,ADDR_MODE2_ADDR'_THM,FORMAT_UnsignedWord] th
  in UD_ALL th end;

fun AM2_ALIGN_ADDRESSES var th =
  let
    val th = Q.INST [var|->`addr32 y`,`a_mode`|->`MAKE_NONALIGNED a_mode`] th 
    val th = RW [ADDR_MODE2_WB_THM,ADDR_MODE2_ADDR_THM] th
    val th = RW [ADDR_MODE2_CMD1_THM,ADDR_MODE2_CMD2_THM] th
    val th = RW [GSYM R30_def,ADDRESS_ROTATE,addr30_addr32] th   
  in th end;

fun FIX_ADDR_MODE2_PAIR (th,nop) = 
  let
    val nop = Q.INST [`Op2`|->`offset`] (SPEC_ALL nop)
  in
    (FIX_ADDR_MODE2 th, FIX_ADDR_MODE2 nop)
  end;

val STR_INST = 
  [``R1:word4``|->``b:word4``,``x1:word32``|->``y:word32``,
   ``R2:word4``|->``a:word4``,``x2:word32``|->``x:word32``,
   ``m2:word32``|->``z:word32``];

val STR_NONALIGNED = 
  let
    val (th,nop) = FIX_ADDR_MODE2_PAIR (ARM_STR,ARM_STR_NOP)
    val rs = [``Rn:word4``,``Rd:word4``]
    val (conds,shape,prog) = (c32TTF,Sirm32TTF,P3_STR)
    val insts = [``M2:word32``|->``(ADDR_MODE2_ADDR' a_mode x1):word32``]
    val i = STR_INST
    val th = MK_PROG_C (conds,shape,insts,prog) rs th i
    val th = MOVE_STAR_RULE `a*b*y*s*c` `a*b*s*c*y` th
    val th = RW [ARM_PROG_HIDE_PRE] (Q.GEN `z` th)
    val th = MOVE_STAR_RULE `a*b*s*c*y` `a*b*y*s*c` th
    val imp = MATCH_MP PROG2_LEMMA (MK_NOP nop)
    val th = MATCH_MP imp th 
  in save_thm("arm_STR_NONALIGNED",th) end;

val STR = save_thm("arm_STR",AM2_ALIGN_ADDRESSES `y` STR_NONALIGNED);

val LDR_NONALIGNED =
  let
    val (th,nop) = FIX_ADDR_MODE2_PAIR (ARM_LDR,ARM_LDR_NOP)
    val rs = [``Rn:word4``,``Rd:word4``]
    val (conds,shape,prog) = (c32TTF,Srir32TTF,P3_STR)
    val insts = [``M2:word32``|->``(ADDR_MODE2_ADDR' a_mode x1):word32``]
    val i = STR_INST
    val th = MK_PROG2 (conds,shape,insts,prog) rs (th,nop) i
  in save_thm("arm_LDR_NONALIGNED",th) end;

val LDR = save_thm("arm_LDR",AM2_ALIGN_ADDRESSES `y` LDR_NONALIGNED);

val LDR1_NONALIGNED =
  let
    val lemma = prove(
      ``!regs m Rn x y. 
           REG_WRITE (INC_PC (REG_WRITE regs m Rn x)) m Rn y =
           REG_WRITE (INC_PC regs) m Rn y``,
       SRW_TAC [] [REG_WRITE_def,INC_PC_def,SUBST_def])
    val (th,nop) = FIX_ADDR_MODE2_PAIR (ARM_LDR,ARM_LDR_NOP)
    val th = UNDISCH_ALL (Q.INST [`Rd`|->`Rn`] (DISCH_ALL th))
    val th = RW [lemma] th
    val rs = [``Rn:word4``]
    val (conds,shape,prog) = (c22TTF,Sri22TTF,P2_STR)
    val insts = [``M2:word32``|->``(ADDR_MODE2_ADDR' a_mode x1):word32``]
    val i = STR_INST
    val th = CLEAN_ARM_RULE_C rs th
    val th = MK_PROG_C (conds,shape,insts,prog) rs th i
    val th = DISCH ``~(ADDR_MODE2_CMD1' a_mode).Wb`` th
    val th = RW [GSYM ARM_PROG_MOVE_COND] th
    val th = MOVE_STAR_RULE `b*y*s*p*c` `b*y*c*s*p` th
    val th' = MATCH_MP PROG2_LEMMA (MK_NOP nop)
    val th = MATCH_MP th' th
  in save_thm("arm_LDR1_NONALIGNED",th) end;

val LDR1 = save_thm("arm_LDR1",AM2_ALIGN_ADDRESSES `y` LDR1_NONALIGNED);

val LDR_PC_LEMMA = prove(
  ``!regs m x. REG_WRITE (INC_PC regs) m 15w x = REG_WRITE regs usr 15w x``,
  SIMP_TAC std_ss [REG_WRITE_def,mode_reg2num_def,num2register_thm,LET_DEF,
                   EVAL ``w2n (15w:word4)``,SUBST_def,INC_PC_def]);

val LDR_PC = 
  let
    val th = Q.INST [`Rd`|->`15w`] (SPEC_ALL ARM_LDR)
    val (th,nop) = FIX_ADDR_MODE2_PAIR (th,ARM_LDR_NOP)
    val rs = [``Rn:word4``]
    val (conds,shape) = (c22TTF,Sbr22TTF)
    val insts = [``M2:word32``|->``(ADDR_MODE2_ADDR' a_mode x1):word32``]
    val i = STR_INST
    val th = CLEAN_ARM_RULE_C rs th
    val th = RW [LDR_PC_LEMMA] th
    val th = CLEAN_ARM_RULE_C rs th
    val th = MK_ARM_RUN_C (conds,shape,insts) th
    val th = AM2_ALIGN_ADDRESSES `x1` th
    val th = Q.INST [`m2`|->`addr32 m2`,`p`|->`addr32 p`] th
    val th = RW [addr30_addr32] th
    val th = RW [GSYM R_def,GSYM R30_def, GSYM M_def, GSYM S_def, GSYM PASS_def] th
    val th = CONV_RULE (RATOR_CONV (MOVE_STAR_CONV `pp*y*m*my*s*u*c` `(y*my*s*c)*m*pp*u`)) th
    val th = CONV_RULE (RAND_CONV (MOVE_STAR_CONV `pp*y*m*my*s*u` `(y*my*s)*m*pp*u`)) th
    val imp = SIMP_RULE (std_ss++sep_ss) [] (Q.INST [`Q`|->`SEP_F`] ARM_RUN_IMP_PROG2)
    val imp = CONV_RULE (RATOR_CONV (REWRITE_CONV [pcSET_def])) (Q.INST [`f`|->`pcSET x`] imp)
    val th = MATCH_MP imp (Q.GEN `p` th)
    val th = CONV_RULE (RAND_CONV (MOVE_STAR_CONV `x*y*z` `x*z*y`)) th    
    val th = MATCH_MP ARM_PROG_HIDE_POST th
    val th = CONV_RULE (RAND_CONV (MOVE_STAR_CONV `x*z*y` `x*y*z`)) th    
    val th = Q.INST [`R1`|->`a`,`y`|->`x`,`m2`|->`y`] th
    val imp = MATCH_MP PROG2_LEMMA (MK_NOP nop)
    val imp = AM2_ALIGN_ADDRESSES `x:word32` imp   
    val th = MATCH_MP imp th
  in save_thm("arm_LDR_PC",th) end;


(* ----------------------------------------------------------------------------- *)
(* General tools                                                                 *)
(* ----------------------------------------------------------------------------- *)

val ARM_PROG2_EQ = let
  val th = Q.SPECL [`P`,`[cmd]`,`Q`,`Q'`,`f`] ARM_PROG_INTRO
  val th = SIMP_RULE (std_ss++sep_ss) [LENGTH,ms_def,pcINC_def,wLENGTH_def] th
  val th = SIMP_RULE std_ss [ARM_RUN_SEMANTICS,ARMpc_def,STAR_ASSOC,R30_def,SEP_DISJ_def,LET_DEF] th
  in GSYM th end;

val ARM_PROG1_EQ = let
  val th = Q.INST [`Q'`|->`SEP_F`] ARM_PROG2_EQ
  val th = SIMP_RULE (bool_ss++sep_ss) [ARM_PROG_FALSE_POST,SEP_F_def,LET_DEF] th
  in th end;

val STATE_ARM_MEM_1 = 
  REWRITE_CONV [GSYM (EVAL ``SUC 0``),STATE_ARM_MEM_def]``STATE_ARM_MEM 1 s``;

val ARM_PROG_INIT_TAC = 
  REWRITE_TAC [ARM_PROG1_EQ,ARM_PROG2_EQ,PASS_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `1` \\ REWRITE_TAC [STATE_ARM_MEM_1];


(* ----------------------------------------------------------------------------- *)
(* Semantics of ``R a1 x1  * ... * R an xn * ms b1 y1 * ... * ms bm ym * ...``   *)
(* ----------------------------------------------------------------------------- *)

val xR_list_def = Define `
  (xR_list [] = emp) /\
  (xR_list ((r,NONE)::xs) = ~R r * xR_list xs) /\
  (xR_list ((r,SOME x)::xs) = R r x * xR_list xs)`;

val xR_list_sem_def = Define `
  (xR_list_sem [] s = T) /\
  (xR_list_sem ((r,NONE)::xs) s = xR_list_sem xs s) /\
  (xR_list_sem ((r,SOME x)::xs) s = (reg r s = x) /\ xR_list_sem xs s)`;

val xR_list_lemma = prove(
  ``((R r x * P) (arm2set' (rs,ns,st,ud,rt) s) = 
     (reg r s = x) /\ r IN rs /\ P (arm2set' (rs DELETE r,ns,st,ud,rt) s)) /\ 
    ((~R r * P) (arm2set' (rs,ns,st,ud,rt) s) = 
     r IN rs /\ P (arm2set' (rs DELETE r,ns,st,ud,rt) s))``,
  SIMP_TAC (std_ss++sep2_ss) [R_def,SEP_HIDE_THM] 
  \\ SIMP_TAC std_ss [SEP_EXISTS,one_STAR,IN_arm2set']
  \\ METIS_TAC [DELETE_arm2set']);

val xR_list_thm = prove(
  ``!xs P rs ns st ud rt. 
      (xR_list xs * P) (arm2set' (rs,ns,st,ud,rt) s) = 
      xR_list_sem xs s /\ ALL_DISTINCT (MAP FST xs) /\ 
      P (arm2set' (rs DIFF (LIST_TO_SET (MAP FST xs)),ns,st,ud,rt) s) /\
      (LIST_TO_SET (MAP FST xs)) SUBSET rs``,
  Induct
  THEN1 SRW_TAC [sep_ss] [xR_list_def,xR_list_sem_def,MAP,ALL_DISTINCT]
  \\ REPEAT STRIP_TAC \\ Cases_on `h` \\ Cases_on `r`
  \\ SIMP_TAC bool_ss [MAP,ALL_DISTINCT,pairTheory.FST,xR_list_sem_def,xR_list_def]
  \\ ASM_REWRITE_TAC [GSYM STAR_ASSOC,xR_list_lemma]
  \\ `LIST_TO_SET (q::MAP FST xs) SUBSET rs =
      q IN rs /\ LIST_TO_SET (MAP FST xs) SUBSET rs` by SRW_TAC [] []
  \\ `rs DIFF LIST_TO_SET (q::MAP FST xs) =
      rs DELETE q DIFF LIST_TO_SET (MAP FST xs)` by 
         SRW_TAC [] [EXTENSION,IN_DIFF,IN_DELETE,CONJ_ASSOC]
  \\ `LIST_TO_SET (MAP FST xs) SUBSET rs DELETE q =
      ~MEM q (MAP FST xs) /\ LIST_TO_SET (MAP FST xs) SUBSET rs` by 
         (SRW_TAC [] [SUBSET_DEF,IN_DELETE] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [] \\ METIS_TAC []);

val _ = Hol_datatype `
  xM_option = xM_seq of word32 list | xM_blank of num`;

val xM_list_def = Define `
  (xM_list [] = emp) /\
  (xM_list ((a,xM_blank n)::xs) = blank_ms a n * xM_list xs) /\
  (xM_list ((a,xM_seq x)::xs) = ms a x * xM_list xs)`;

val ms_sem_def = Define `
  (ms_sem a [] s = T) /\ 
  (ms_sem a (x::xs) s = (mem a s = x) /\ ms_sem (a+1w) xs s)`;

val xM_list_sem_def = Define `
  (xM_list_sem [] s = T) /\
  (xM_list_sem ((a,xM_blank n)::xs) s = n <= 2**30 /\ xM_list_sem xs s) /\
  (xM_list_sem ((a,xM_seq x)::xs) s = 
     ms_sem a x s /\ LENGTH x <= 2**30 /\ xM_list_sem xs s)`;

val ms_address_set_def = Define `
  (ms_address_set a 0 = ({}:word30 set)) /\ 
  (ms_address_set a (SUC n) = a INSERT ms_address_set (a+1w) n)`;

val xM_list_addresses_def = Define `
  (xM_list_addresses [] = []) /\
  (xM_list_addresses ((a,xM_blank n)::xs) = 
    ms_address_set a n :: xM_list_addresses xs) /\
  (xM_list_addresses ((a,xM_seq x)::xs) = 
    ms_address_set a (LENGTH x) :: xM_list_addresses xs)`;

val xM_list_address_set_def = Define `
  xM_list_address_set xs = FOLDR $UNION EMPTY (xM_list_addresses xs)`;

val ALL_DISJOINT_def = Define `
  (ALL_DISJOINT [] = T) /\
  (ALL_DISJOINT (x::xs) = EVERY (\y. DISJOINT x y) xs /\ ALL_DISJOINT xs)`;

val IN_ms_address_set_ADD1 = prove(
  ``!xs a b. a IN (ms_address_set b xs) = (a+1w) IN (ms_address_set (b+1w) xs)``,
  Induct \\ SIMP_TAC std_ss [ms_address_set_def,NOT_IN_EMPTY,IN_INSERT,WORD_EQ_ADD_RCANCEL]
  \\ METIS_TAC []);

val ms_address_set_no_overlap_lemma = prove(
  ``!k n. k <= n /\ n < 2**30 ==> ~((a + n2w n) IN (ms_address_set a k))``,
  Induct \\ FULL_SIMP_TAC std_ss [ms_address_set_def,NOT_IN_EMPTY,IN_INSERT]
  \\ REPEAT STRIP_TAC 
  THEN1 (FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [WORD_ADD_RID_UNIQ,n2w_11]
         \\ `~(0 = n)` by DECIDE_TAC \\ METIS_TAC [LESS_MOD])
  \\ `k <= n - 1 /\ n - 1 < 1073741824` by DECIDE_TAC
  \\ `~((a + n2w (n-1)) IN (ms_address_set a k))` by METIS_TAC []
  \\ `!k a b. (b + 1w) IN (ms_address_set (a + 1w) k) = b IN (ms_address_set a k)` by
         (Induct \\ SRW_TAC [] [ms_address_set_def,WORD_EQ_ADD_RCANCEL])
  \\ `n = (n-1)+1` by DECIDE_TAC 
  \\ `a + n2w ((n-1)+1) IN ms_address_set (a + 1w) k` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ METIS_TAC []);

val ms_address_set_no_overlap = prove(
  ``!k h a. SUC k <= 2**30 ==> ~(a IN (ms_address_set (a+1w:word30) k))``,
  SIMP_TAC bool_ss [LENGTH,GSYM LESS_EQ] \\ REPEAT STRIP_TAC
  \\ `k <= 2 ** 30 - 1 /\ 2 ** 30 - 1 < 2 ** 30` by DECIDE_TAC
  \\ `~((a + n2w (2 ** 30 - 1) + 1w) IN (ms_address_set (a + 1w) k))` 
           by METIS_TAC [ms_address_set_no_overlap_lemma,IN_ms_address_set_ADD1] 
  \\ `2 ** 30 - 1 + 1 = 2 ** 30` by DECIDE_TAC
  \\ `n2w (2 ** 30) = 0w:word30` by SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11]
  \\ FULL_SIMP_TAC bool_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,WORD_ADD_0]);

val IN_ms_address_set = prove(
  ``!n a b. b IN ms_address_set a n = ?k. k < n /\ (b = n2w k + a)``,
  Induct \\ REWRITE_TAC [ms_address_set_def,NOT_IN_EMPTY,DECIDE ``~(k<0)``,IN_INSERT]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []
  THEN1 (Q.EXISTS_TAC `0` \\ ASM_REWRITE_TAC [WORD_ADD_0] \\ DECIDE_TAC) << [
    Q.PAT_ASSUM `!a:'a. b:bool` IMP_RES_TAC
    \\ `SUC k < SUC n` by DECIDE_TAC \\ Q.EXISTS_TAC `SUC k`
    \\ ASM_REWRITE_TAC [ADD1,GSYM word_add_n2w] \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM],
    Cases_on `k` \\ REWRITE_TAC [WORD_ADD_0] 
    \\ DISJ2_TAC \\ Q.EXISTS_TAC `n'` \\ `n' < n` by DECIDE_TAC 
    \\ ASM_REWRITE_TAC [ADD1,GSYM word_add_n2w] \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]]);
      
val xM_list_lemma_LEMMA1 = prove(
  ``!a n ns. ms_address_set (a + 1w) n SUBSET ns DELETE a ==> SUC n <= 2 ** 30``,
  REWRITE_TAC [SUBSET_DEF,IN_DELETE] \\ REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `2 ** 30 <= n` by DECIDE_TAC  
  \\ `a IN ms_address_set (a + 1w) n` by ALL_TAC << [    
    REWRITE_TAC [IN_ms_address_set] \\ Q.EXISTS_TAC `2**30-1`
    \\ `1 <= 2**30` by EVAL_TAC
    \\ ASM_SIMP_TAC bool_ss [LESS_EQ,ADD1,SUB_ADD,WORD_ADD_ASSOC]
    \\ `!b. b + a + 1w = b + 1w + a` by METIS_TAC [WORD_ADD_COMM,WORD_ADD_ASSOC]
    \\ ASM_SIMP_TAC bool_ss [word_add_n2w,SUB_ADD]
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [WORD_ADD_0],
    METIS_TAC []]);

val xM_list_lemma_LEMMA2 = prove(
  ``!a n ns. SUC n <= 2 ** 30 ==> ~(a IN ms_address_set (a + 1w) n)``,
  SIMP_TAC bool_ss [IN_ms_address_set] \\ REPEAT STRIP_TAC
  \\ Cases_on `k < n` \\ ASM_REWRITE_TAC [WORD_ADD_ASSOC]
  \\ `!b. b + a + 1w = a + (b + 1w)` by METIS_TAC [WORD_ADD_COMM,WORD_ADD_ASSOC]
  \\ ASM_REWRITE_TAC [word_add_n2w] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ `k + 1 < 2**30` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [WORD_ADD_RID_UNIQ,n2w_11]);

val xM_list_lemma1 = prove(
  ``!xs a rs ns st ud rt P.
      ((ms a xs * P) (arm2set' (rs,ns,st,ud,rt) s) = 
       (ms_sem a xs s) /\ LENGTH xs <= 2**30 /\
       ms_address_set a (LENGTH xs) SUBSET ns /\ 
       P (arm2set' (rs,ns DIFF ms_address_set a (LENGTH xs),st,ud,rt) s))``,
  Induct THEN1 SRW_TAC [sep_ss] [ms_def,ms_sem_def,ms_address_set_def]
  \\ REWRITE_TAC [ms_def,ms_sem_def,GSYM STAR_ASSOC,M_def,one_STAR]
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [IN_arm2set']
  \\ Cases_on `~(h = mem a s)` THEN1 METIS_TAC []
  \\ FULL_SIMP_TAC bool_ss [LENGTH]
  \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set',ms_address_set_def,LENGTH]
  \\ `!k. ns DELETE a DIFF ms_address_set (a + 1w) k =
          ns DIFF (a INSERT ms_address_set (a + 1w) k)` by 
        SRW_TAC [] [EXTENSION,IN_DELETE,IN_DIFF,CONJ_ASSOC]
  \\ EQ_TAC \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC
  \\ IMP_RES_TAC xM_list_lemma_LEMMA1 \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [IN_INSERT,SUBSET_DEF,IN_DELETE] THEN1 METIS_TAC []  
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ IMP_RES_TAC xM_list_lemma_LEMMA2 \\ ASM_REWRITE_TAC []);

val xM_list_lemma2 = prove(
  ``!n a rs ns st ud rt P.
      ((blank_ms a n * P) (arm2set' (rs,ns,st,ud,rt) s) = 
       n <= 2**30 /\ ms_address_set a n SUBSET ns /\ 
       P (arm2set' (rs,ns DIFF ms_address_set a n,st,ud,rt) s))``,
  Induct THEN1 SRW_TAC [sep_ss] [blank_ms_def,ms_address_set_def]
  \\ REWRITE_TAC [blank_ms_def,GSYM STAR_ASSOC,M_def,one_STAR]
  \\ SIMP_TAC (bool_ss++sep2_ss) [SEP_HIDE_THM] 
  \\ SIMP_TAC bool_ss [SEP_EXISTS_THM,M_def,one_STAR,GSYM STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [IN_arm2set']
  \\ FULL_SIMP_TAC bool_ss []
  \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set',ms_address_set_def]
  \\ `!k. ns DELETE a DIFF ms_address_set (a + 1w) k =
          ns DIFF (a INSERT ms_address_set (a + 1w) k)` by 
        SRW_TAC [] [EXTENSION,IN_DELETE,IN_DIFF,CONJ_ASSOC]
  \\ EQ_TAC \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC
  \\ IMP_RES_TAC xM_list_lemma_LEMMA1 \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [IN_INSERT,SUBSET_DEF,IN_DELETE] THEN1 METIS_TAC []  
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ IMP_RES_TAC xM_list_lemma_LEMMA2 \\ ASM_REWRITE_TAC []);

val EVERY_DISJOINT = prove(
  ``!xs x. EVERY (\y. DISJOINT x y) xs = DISJOINT x (FOLDR $UNION {} xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [EVERY_DEF,FOLDR,DISJOINT_EMPTY]
  \\ SRW_TAC [] [DISJOINT_DEF,EXTENSION] \\ METIS_TAC []);

val xM_list_thm = prove(
  ``!xs P rs ns st ud rt.
      ((xM_list xs * P) (arm2set' (rs,ns,st,ud,rt) s) = 
       xM_list_sem xs s /\ ALL_DISJOINT (xM_list_addresses xs) /\ 
       P (arm2set' (rs,ns DIFF (xM_list_address_set xs),st,ud,rt) s) /\
       xM_list_address_set xs SUBSET ns)``,
  Induct
  THEN1 SRW_TAC [sep_ss] [xM_list_def,xM_list_sem_def,MAP,ALL_DISJOINT_def,
                          xM_list_address_set_def,xM_list_addresses_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `h` \\ Cases_on `r`
  \\ SIMP_TAC bool_ss [MAP,ALL_DISJOINT_def,pairTheory.FST,xM_list_sem_def,xM_list_def,
                       xM_list_addresses_def,xM_list_address_set_def,FOLDR]
  \\ FULL_SIMP_TAC bool_ss [GSYM xM_list_address_set_def]
  \\ ASM_SIMP_TAC std_ss [xM_list_lemma1,xM_list_lemma2,GSYM STAR_ASSOC]
  \\ SIMP_TAC bool_ss [EVERY_DISJOINT,GSYM xM_list_address_set_def] 
  \\ REWRITE_TAC [prove(``!x:'a set y z. x DIFF y DIFF z = x DIFF (y UNION z)``, 
                  SRW_TAC [] [EXTENSION,IN_UNION,IN_DIFF,CONJ_ASSOC])]
  \\ `!x y z:word30 set. 
      DISJOINT x y /\ x UNION y SUBSET z = y SUBSET z DIFF x /\ x SUBSET z` by
        (SRW_TAC [] [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ METIS_TAC [])
  \\ EQ_TAC \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC []);

val rest_list_def = Define `
  rest_list (st,ud,rt,cd) (x,y,z,b) = 
    (if st then S x else emp) * 
    (if ud then one (Undef y) else emp) * 
    (if rt then one (Rest z) else emp) * 
    (if cd then cond b else emp)`;

val rest_list_sem_def = Define `
  rest_list_sem (st,ud,rt,cd) (x,y,z,b) s = 
    (if st then (status s = x) else T) /\ 
    (if ud then (s.undefined = y) else T) /\
    (if rt then (owrt_visible s = z) else T) /\ 
    (if cd then b else T)`;

val rest_list_thm = prove(
  ``!st ud rt cd x y z b P rs ns st' ud' rt'. 
      (rest_list (st,ud,rt,cd) (x,y,z,b) * P) (arm2set' (rs,ns,st',ud',rt') s) = 
      rest_list_sem (st,ud,rt,cd) (x,y,z,b) s /\ 
      (st ==> st') /\ (ud ==> ud') /\ (rt ==> rt') /\
      P (arm2set' (rs,ns,~st /\ st',~ud /\ ud',~rt /\ rt') s)``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [rest_list_def,rest_list_sem_def,
       prove(``!cd b. (if cd then cond b else emp) = cond (cd ==> b)``,SRW_TAC [sep_ss][])] 
  \\ Cases_on `st` \\ SIMP_TAC (bool_ss++sep_ss) [] \\ Cases_on `x = status s` 
  \\ Cases_on `ud` \\ SIMP_TAC (bool_ss++sep_ss) [] \\ Cases_on `y = s.undefined` 
  \\ Cases_on `rt` \\ SIMP_TAC (bool_ss++sep_ss) [] \\ Cases_on `z = owrt_visible s` 
  \\ ASM_SIMP_TAC bool_ss [GSYM STAR_ASSOC,S_def,one_STAR,IN_arm2set',DELETE_arm2set',cond_STAR]
  \\ EQ_TAC \\ ASM_SIMP_TAC bool_ss []);

val emp_list_thm = prove(
  ``!s rs ns st ud rt.
       emp (arm2set' (rs,ns,st,ud,rt) s) = (rs = {}) /\ (ns = {}) /\ ~st /\ ~ud /\ ~rt``,
  SIMP_TAC std_ss [emp_def,arm2set'_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `st` THEN1 SRW_TAC [] [EXTENSION]
  \\ Cases_on `ud` THEN1 SRW_TAC [] [EXTENSION]
  \\ Cases_on `rt` THEN1 SRW_TAC [] [EXTENSION]
  \\ SRW_TAC [] [EXTENSION,GSPECIFICATION]);

val rest_emp_list_thm = prove(
  ``!st ud rt xs x y z b P rs ns st' ud' rt'. 
      (rest_list (st,ud,rt,cd) (x,y,z,b)) (arm2set' (rs,ns,st',ud',rt') s) = 
      rest_list_sem (st,ud,rt,cd) (x,y,z,b) s /\ 
      (rs = {}) /\ (ns = {}) /\ (st = st') /\ (ud = ud') /\ (rt = rt')``,
  REPEAT STRIP_TAC  
  \\ CONV_TAC ((RATOR_CONV o RAND_CONV o RATOR_CONV) 
               (ONCE_REWRITE_CONV [(GSYM o CONJUNCT2 o SPEC_ALL) emp_STAR]))
  \\ REWRITE_TAC [rest_list_thm,emp_list_thm]
  \\ Cases_on `st` \\ Cases_on `st'` \\ Cases_on `ud` \\ Cases_on `ud'`
  \\ Cases_on `rt` \\ Cases_on `rt'` \\ SIMP_TAC bool_ss []);

val spec_list_def = Define `
  spec_list xs ys (st,x) (ud,y) (rt,z) (cd,b) = 
    xR_list xs * xM_list ys * rest_list (st,ud,rt,cd) (x,y,z,b)`;

val spec_list_select_def = Define `
  spec_list_select (xs,ys,st,ud,rt) =
    (LIST_TO_SET (MAP FST xs),xM_list_address_set ys,st,ud,rt)`;
  
val spec_list_sem_def = Define `
  spec_list_sem xs ys (st,x) (ud,y) (rt,z) (cd,b) q s =
    xR_list_sem xs s /\ xM_list_sem ys s /\ rest_list_sem (st,ud,rt,cd) (x,y,z,b) s /\ 
    ALL_DISTINCT (MAP FST xs) /\ ALL_DISJOINT (xM_list_addresses ys) /\
    (q = spec_list_select (xs,ys,st,ud,rt))`;
  
val spec_list_thm = store_thm("spec_list_thm",
  ``!xs ys st ud rt cd q s.
      (spec_list xs ys st ud rt cd) (arm2set' q s) = 
      spec_list_sem xs ys st ud rt cd q s``,
  REPEAT STRIP_TAC
  \\ `?rs ns st' ud' rt'. q = (rs,ns,st',ud',rt')` by METIS_TAC [pairTheory.PAIR]
  \\ `?st' x. st = (st',x)` by METIS_TAC [pairTheory.PAIR]
  \\ `?ud' y. ud = (ud',y)` by METIS_TAC [pairTheory.PAIR]
  \\ `?rt' z. rt = (rt',z)` by METIS_TAC [pairTheory.PAIR]
  \\ `?cd' b. cd = (cd',b)` by METIS_TAC [pairTheory.PAIR]
  \\ ASM_SIMP_TAC bool_ss [spec_list_def,GSYM STAR_ASSOC,xR_list_thm,xM_list_thm]
  \\ ASM_SIMP_TAC bool_ss [rest_emp_list_thm,
       prove(``(x DIFF y = {}) = x SUBSET y``,
       SRW_TAC [] [EXTENSION,SUBSET_DEF] \\ METIS_TAC [])]
  \\ REWRITE_TAC [spec_list_sem_def,pairTheory.PAIR_EQ,spec_list_select_def]
  \\ REWRITE_TAC [SET_EQ_SUBSET,GSYM CONJ_ASSOC]
  \\ EQ_TAC \\ SIMP_TAC std_ss []);

(* function for instantiation *)

val LIST_TO_SET_CLAUSES = prove(
  ``!x xs. (LIST_TO_SET [] = {}) /\ (LIST_TO_SET (x::xs) = x INSERT LIST_TO_SET xs)``,
  SRW_TAC [] [EXTENSION]);

val UNION_APPEND = prove(
  ``!x y z. (x INSERT y) UNION z = x INSERT (y UNION z)``,
  SRW_TAC [] [EXTENSION,DISJ_ASSOC]);

val spec_list_expand_ss = rewrites 
  [spec_list_def,xR_list_def,xM_list_def,rest_list_def,spec_list_sem_def,
   xR_list_sem_def,xM_list_sem_def,rest_list_sem_def,ms_sem_def,
   xM_list_addresses_def,ms_address_set_def,LIST_TO_SET_CLAUSES,spec_list_select_def,
   xM_list_address_set_def,FOLDR,UNION_EMPTY,UNION_APPEND,GSYM CONJ_ASSOC,ms_def,
   MAP,FST,STAR_ASSOC,EVAL ``SUC 0 <= 2**30``,LENGTH];

fun sep_pred_semantics (xs,ys,st,ud,rt,cd) = let
  val th = Q.SPECL [xs,ys,st,ud,rt,cd] spec_list_thm
  val th = SIMP_RULE (bool_ss++sep_ss++spec_list_expand_ss) [] th
  in th end;

(* example *)

val xs = `[(a1,SOME x1);(a2,SOME x2);(a3,SOME x3);(a4,NONE);(a5,NONE);(a6,NONE)]`;
val ys = `[(b1,xM_seq [y1]);(b2,xM_seq [y2]);(b3,xM_seq y3);(b4,xM_blank k4)]`;
val st = `(T,st)`;
val ud = `(T,ud)`;
val rt = `(F,rt)`;
val cd = `(T,g)`;
val th = sep_pred_semantics (xs,ys,st,ud,rt,cd);


(* ----------------------------------------------------------------------------- *)
(* CLEANING INSTRUCTION RULES                                                    *)
(* ----------------------------------------------------------------------------- *)

val reg_rw = prove(
  ``(!s. s.registers r15 = reg 15w s) /\ 
    !x s. ~(x = 15w) ==> (REG_READ s.registers (state_mode s) x = reg x s)``,
  SRW_TAC [] [reg_def]);

val contract_ss = rewrites ([NZCV_def,reg_rw] @ map GSYM
  [mem_def,status_def,statusN_def,statusZ_def,statusC_def,statusV_def,addr30_def,
   state_mode_def]);

fun PAT_DISCH tm th = DISCH (hd (filter (can_match tm) (hyp th))) th;
fun PAT_DISCH_LIST tms th = foldr (uncurry PAT_DISCH) th tms;

fun simple_clean th tms = let
  val th = SPEC_ALL th
  val th = INST [``state:arm_mem_state``|->``s:arm_mem_state``] th 
  val th = INST [``s:bool``|->``s_flag:bool``] th
  val th = ASM_UNABBREV_ALL_RULE (UD_ALL th)
  val th = foldr (uncurry DISCH) th tms
  val th = (UNDISCH_ALL o SIMP_RULE (bool_ss++contract_ss) [] o DISCH_ALL) th
  val tm1 = ``~s.undefined``
  val tm2 = ``CONDITION_PASSED2 (status s) c``
  val tm3 = ``mem (addr30 p) s = enc cmd``
  val th = PAT_DISCH_LIST ([tm1,tm2,tm3] @ tms) th
  in th end;


(* ----------------------------------------------------------------------------- *)
(* LDM and STM INSTRUCTIONS                                                      *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  abbrev_addr4 = am4_DA of bool | am4_IA of bool | am4_DB of bool | am4_IB of bool |
                 am4_FA of bool | am4_FD of bool | am4_EA of bool | am4_ED of bool`;

val ADDR_MODE4_CMD_def = Define `
  (ADDR_MODE4_CMD (am4_DA wb) = <| Pre:=F; Up:=F; Wb:=wb |>) /\ 
  (ADDR_MODE4_CMD (am4_FA wb) = <| Pre:=F; Up:=F; Wb:=wb |>) /\ 
  (ADDR_MODE4_CMD (am4_IA wb) = <| Pre:=F; Up:=T; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_FD wb) = <| Pre:=F; Up:=T; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_DB wb) = <| Pre:=T; Up:=F; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_EA wb) = <| Pre:=T; Up:=F; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_IB wb) = <| Pre:=T; Up:=T; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_ED wb) = <| Pre:=T; Up:=T; Wb:=wb |>)`;

val reg_bitmap_def = Define `
  reg_bitmap (xs:word4 list) = (FCP i. MEM (n2w i) xs):word16`;

val MEM_EQ_EXISTS = prove(
  ``!xs. MEM x xs = ?ys zs. xs = ys ++ [x] ++ zs``,
  Induct THEN1 SRW_TAC [] [] 
  \\ ASM_REWRITE_TAC [MEM] 
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `[]` \\ Q.EXISTS_TAC `xs` \\ SRW_TAC [] [])
  THEN1 (Q.EXISTS_TAC `h::ys` \\ Q.EXISTS_TAC `zs` \\ ASM_REWRITE_TAC [APPEND])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC bool_ss [APPEND,CONS_11] \\ METIS_TAC []);

val MEM_MAP_FILTER = prove(
  ``!x xs. MEM x ((MAP SND o FILTER FST) xs) = MEM (T,x) xs``,        
  Induct_on `xs` THEN1 SRW_TAC [] [] 
  \\ Cases_on `h` \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [FILTER,MAP,MEM]);

val MEM_SNOC = prove(
  ``!xs x y. MEM x (SNOC y xs) = MEM x (CONS y xs)``,
  Induct_on `xs` \\ SRW_TAC [] [MEM,SNOC] \\ METIS_TAC []);

val MEM_GENLIST = prove(
  ``!n x f. MEM x (GENLIST f n) = ?i. i < n /\ (x = f i)``,
  Induct THEN1 SIMP_TAC std_ss [MEM,GENLIST]
  \\ SRW_TAC [] [MEM,GENLIST,MEM_SNOC]
  \\ Cases_on `x = f n` \\ ASM_REWRITE_TAC []
  THEN1 (Q.EXISTS_TAC `n` \\ SRW_TAC [] [])
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `i` \\ METIS_TAC [LESS_TRANS,LESS_EQ_IMP_LESS_SUC,LESS_EQ_REFL],
    Cases_on `i = n` THEN1 METIS_TAC [] \\ `i < n` by DECIDE_TAC \\ METIS_TAC []]);

val MEM_PAIR_GENLIST = prove(
  ``!n x f g. 
       MEM (T,x) (GENLIST (\i. (f i, g i)) n) = ?i. i < n /\ f i /\ (x = g i)``,
  SRW_TAC [] [MEM_GENLIST]);

val w2n_FCP_BETA = let
  val th' = Q.INST_TYPE [`:'a`|->`:i4`] w2n_lt
  val th' = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] th'
  val th = Q.SPEC `w2n (x:word4)` fcpTheory.FCP_BETA
  val th = Q.INST_TYPE [`:'b`|->`:i16`] th
  val th = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] th
  in MP th (Q.SPEC `x` th') end;

val MEM_reg_bitmap = prove(
  ``!x xs. MEM x xs = reg_bitmap xs %% w2n x``,
  SIMP_TAC std_ss [reg_bitmap_def,w2n_FCP_BETA,n2w_w2n]);

val MEM_REGISTER_LIST_reg_bitmap = store_thm("MEM_REGISTER_LIST_reg_bitmap",
  ``!xs x. MEM x (REGISTER_LIST (reg_bitmap xs)) = MEM x xs``,  
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [REGISTER_LIST_def,MEM_MAP_FILTER]
  \\ REWRITE_TAC [MEM_reg_bitmap]
  \\ REWRITE_TAC [MEM_PAIR_GENLIST]
  \\ ASSUME_TAC (Q.INST_TYPE [`:'a`|->`:i4`] w2n_lt)
  \\ EQ_TAC \\ STRIP_TAC \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2n_n2w]
  \\ Q.EXISTS_TAC `w2n (x:word4)` \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_w2n]);

val SNOC_CONS = prove(
  ``!xs x y. SNOC x (y::xs) = y::(SNOC x xs)``,Induct \\ ASM_REWRITE_TAC [SNOC]);
  
val FILTER_SNOC = prove(
  ``!xs x P. FILTER P (SNOC x xs) = if P x then SNOC x (FILTER P xs) else FILTER P xs``,  
  Induct \\ ASM_REWRITE_TAC [SNOC,FILTER] \\ SRW_TAC [] [SNOC_CONS]);

val MAP_SNOC = prove(
  ``!xs x f. MAP f (SNOC x xs) = SNOC (f x) (MAP f xs)``,
  Induct \\ ASM_REWRITE_TAC [SNOC,MAP] \\ SRW_TAC [] [SNOC_CONS]);
    
val SORTED_SNOC_SNOC = prove(
  ``!xs f x y. SORTED f (SNOC x (SNOC y xs)) = f y x /\ SORTED f (SNOC y xs)``,
  Induct \\ FULL_SIMP_TAC std_ss [SNOC,SORTED_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `xs`
  \\ FULL_SIMP_TAC std_ss [SNOC,SORTED_DEF] \\ METIS_TAC []);

val SORTED_REGISTER_LIST_LEMMA = prove(
  ``!k g:word16. 
      k <= 16 ==> 
      SORTED $<+ ((MAP SND o FILTER FST) (GENLIST (\i. (g %% i,(n2w i):word4)) k))``,
  Induct 
  \\ SIMP_TAC std_ss [GENLIST,FILTER,MAP,SORTED_DEF,FILTER_SNOC]
  \\ REPEAT STRIP_TAC \\ Cases_on `g %% k` 
  \\ `k <= 16` by DECIDE_TAC
  \\ PAT_ASSUM ``!g'. b`` (ASSUME_TAC o UNDISCH o Q.SPEC `g`)
  \\ FULL_SIMP_TAC std_ss [MAP_SNOC]
  \\ STRIP_ASSUME_TAC (Q.ISPEC `MAP SND (FILTER FST 
       (GENLIST (\i. ((g:word16) %% i,((n2w i):word4))) k))` SNOC_CASES)
  \\ FULL_SIMP_TAC std_ss [SNOC,SORTED_DEF,SORTED_SNOC_SNOC]
  \\ `!xs. MEM x (SNOC x xs)` by (Induct \\ SRW_TAC [] [MEM,SNOC])
  \\ `MEM x (MAP SND (FILTER FST (GENLIST (\i. (g %% i,n2w i)) k)))` by METIS_TAC [] 
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,MEM_FILTER,MEM_GENLIST]
  \\ `k < 16 /\ i < 16` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_lo_n2w]);

val SORTED_REGISTER_LIST = store_thm("SORTED_REGSITER_LIST",
  ``!g. SORTED $<+ (REGISTER_LIST g)``,
  REWRITE_TAC [REGISTER_LIST_def]
  \\ MATCH_MP_TAC (SPEC_ALL SORTED_REGISTER_LIST_LEMMA) \\ DECIDE_TAC);

val SORTED_CONS_IMP = prove(
  ``!xs h. SORTED $<+ (h::xs) ==> SORTED $<+ xs /\ ~(MEM h xs) /\ EVERY (\x. h <+ x) xs``,
  Induct \\ SRW_TAC [] [MEM,SORTED_DEF] THEN1 METIS_TAC [WORD_NOT_LOWER_EQ]
  \\ `SORTED $<+ (h'::xs)` by (Cases_on `xs` \\ METIS_TAC [SORTED_DEF,WORD_LOWER_TRANS])
  \\ METIS_TAC []);

val SORTED_LO_IMP_EQ = store_thm("SORTED_LOWER_IMP_EQ",
  ``!xs ys. SORTED $<+ xs /\ SORTED $<+ ys /\ (!x. MEM x xs = MEM x ys) ==> (xs = ys)``,
  Induct THEN1 (Cases_on `ys` \\ SRW_TAC [] [MEM] \\ METIS_TAC [])
  \\ REWRITE_TAC [MEM] \\ REPEAT STRIP_TAC 
  \\ `MEM h ys` by METIS_TAC []
  \\ `?hs zs. ys = hs ++ [h] ++ zs` by METIS_TAC [MEM_EQ_EXISTS]
  \\ Q.PAT_ASSUM `!ys. b ==> (c:bool)` (ASSUME_TAC o Q.SPEC `zs`)
  \\ Cases_on `hs` \\ FULL_SIMP_TAC std_ss [CONS_11,APPEND,MEM]
  THEN1 METIS_TAC [SORTED_CONS_IMP]
  \\ IMP_RES_TAC SORTED_CONS_IMP
  \\ FULL_SIMP_TAC std_ss [MEM_APPEND,MEM,EVERY_APPEND,EVERY_DEF]
  \\ `MEM h' xs` by METIS_TAC []
  \\ `?hs' zs'. xs = hs' ++ [h'] ++ zs'` by METIS_TAC [MEM_EQ_EXISTS]
  \\ FULL_SIMP_TAC std_ss [EVERY_APPEND,EVERY_DEF] \\ METIS_TAC [WORD_LOWER_ANTISYM]);


val LEAST_MEM_def = Define `
  (LEAST_MEM [x] = x) /\ 
  (LEAST_MEM (x::y::ys) = 
     let m = LEAST_MEM (y::ys) in if x <=+ m then x else m)`;

val LENGTH_FILTER = prove(
  ``!xs P. LENGTH (FILTER P xs) <= LENGTH xs ``,
  Induct \\ SIMP_TAC std_ss [FILTER,LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `P h` \\ ASM_REWRITE_TAC [LENGTH] 
  \\ PAT_ASSUM ``!P:'a. b:bool`` (ASSUME_TAC o SPEC_ALL) \\ DECIDE_TAC );

val LEAST_SORT_LEMMA = prove(
  ``!xs m. MEM m xs ==> LENGTH (FILTER (\x. ~(x = m)) xs) < LENGTH xs``,
  Induct THEN1 SRW_TAC [] []
  \\ SIMP_TAC std_ss [MEM,FILTER,LENGTH] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `h = m` \\ ASM_REWRITE_TAC [LESS_EQ,DECIDE ``n < SUC m = n <= m``]
  THEN1 METIS_TAC [LENGTH_FILTER,LESS_LESS_EQ_TRANS]
  \\ `~(m = h)` by METIS_TAC [] \\ ASM_REWRITE_TAC [LENGTH,GSYM LESS_EQ]);

val MEM_LEAST_MEM = prove(
  ``!xs x. MEM (LEAST_MEM (x::xs)) (x::xs)``,
  Induct \\ ONCE_REWRITE_TAC [LEAST_MEM_def] \\ SIMP_TAC std_ss [LET_DEF]
  THEN1 REWRITE_TAC [MEM]
  \\ Cases_on `x <=+ LEAST_MEM (h::xs)` \\ ASM_REWRITE_TAC []
  THEN1 REWRITE_TAC [MEM] \\ ONCE_REWRITE_TAC [MEM] \\ ASM_REWRITE_TAC []);

val (LEAST_SORT_def,LEAST_SORT_ind) = let
  val d = Defn.Hol_defn "LEAST_SORT" `
    (LEAST_SORT [] = []) /\
    (LEAST_SORT (x::xs) = 
       let m = LEAST_MEM (x::xs) in 
         m :: LEAST_SORT (FILTER (\x. ~(x = m)) (x::xs)))`
  val tac = WF_REL_TAC `measure LENGTH` \\ METIS_TAC [LEAST_SORT_LEMMA,MEM_LEAST_MEM,MEM]
  in Defn.tprove (d,tac) end;

val MEM_LEAST_SORT = prove(
  ``!xs x. MEM x (LEAST_SORT xs) = MEM x xs``,
  recInduct LEAST_SORT_ind \\ REWRITE_TAC [LEAST_SORT_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `x' = LEAST_MEM (x::xs)`
  THEN1 (ASM_REWRITE_TAC [MEM_LEAST_MEM] \\ REWRITE_TAC [MEM])
  \\ CONV_TAC (RATOR_CONV (REWRITE_CONV [MEM])) \\ ASM_REWRITE_TAC []
  \\ Q.PAT_ASSUM `!m. b:bool` 
       (ASSUME_TAC o Q.SPEC `x'` o REWRITE_RULE [] o Q.SPEC `LEAST_MEM (x::xs)`)
  \\ ASM_SIMP_TAC std_ss [MEM_FILTER]);

val SORTED_EQ_LOWER = 
  (REWRITE_RULE [relationTheory.transitive_def,WORD_LOWER_TRANS] o Q.ISPEC `$<+`) SORTED_EQ;

val LEAST_MEM_IMP = prove(
  ``!xs x y. (y = LEAST_MEM (x::xs)) ==> !z. MEM z (x::xs) ==> (y = z) \/ (y <+ z)``,
  Induct \\ REWRITE_TAC [LEAST_MEM_def,MEM] THEN1 METIS_TAC []
  \\ SIMP_TAC std_ss [LET_DEF] \\ NTAC 3 STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o REWRITE_RULE [] o Q.SPECL [`h`,`LEAST_MEM (h::xs)`])    
  \\ Cases_on `z = x` \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `x <=+ LEAST_MEM (h::xs)` \\ ASM_REWRITE_TAC []
  THEN1 METIS_TAC [WORD_LOWER_CASES]
  \\ FULL_SIMP_TAC std_ss [MEM,WORD_LOWER_OR_EQ]
  \\ METIS_TAC [WORD_LOWER_TRANS]);

val LEAST_MEM_LOWER_EQ = prove(
  ``!xs x. MEM x xs ==> LEAST_MEM xs <=+ x``,
  Induct \\ SIMP_TAC std_ss [MEM,LEAST_MEM_def]
  \\ Cases_on `xs` \\ SIMP_TAC std_ss [LEAST_MEM_def,LET_DEF]
  THEN1 SRW_TAC [] [MEM,WORD_LOWER_EQ_REFL] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `x = h'` \\ ASM_REWRITE_TAC []
  THEN1 METIS_TAC [WORD_LOWER_EQ_CASES]
  \\ Cases_on `h' <=+ LEAST_MEM (h::t)` \\ ASM_REWRITE_TAC []
  \\ METIS_TAC [WORD_LOWER_EQ_TRANS]);

val SORTED_LEAST_SORT = prove(
  ``!xs. SORTED $<+ (LEAST_SORT xs)``,
  recInduct LEAST_SORT_ind \\ SIMP_TAC std_ss 
    [LEAST_SORT_def,LET_DEF,SORTED_DEF,SORTED_EQ_LOWER,MEM_LEAST_SORT,MEM_FILTER]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC LEAST_MEM_LOWER_EQ
  \\ FULL_SIMP_TAC std_ss [WORD_LOWER_OR_EQ] \\ METIS_TAC [WORD_LOWER_REFL]);

val REGISTER_LIST_EQ_LEAST_SORT = prove(
  ``!xs. REGISTER_LIST (reg_bitmap xs) = LEAST_SORT xs``,
  STRIP_TAC \\ MATCH_MP_TAC SORTED_LO_IMP_EQ
  \\ REWRITE_TAC [MEM_REGISTER_LIST_reg_bitmap,MEM_LEAST_SORT,
                  SORTED_LEAST_SORT,SORTED_REGISTER_LIST]);

val ALL_DISTINCT_FILTER = prove(
  ``!xs. ALL_DISTINCT xs ==> !g. ALL_DISTINCT (FILTER g xs)``,
  Induct \\ REWRITE_TAC [ALL_DISTINCT,FILTER] \\ REPEAT STRIP_TAC
  \\ Cases_on `g h` \\ ASM_REWRITE_TAC [ALL_DISTINCT,MEM_FILTER] \\ METIS_TAC []);

val LENGTH_FILTER_NEQ = prove(
  ``!xs y. ALL_DISTINCT xs /\ MEM y xs ==> 
           (LENGTH (FILTER (\x. ~(x = y)) xs) = LENGTH xs - 1)``,
  Induct \\ SIMP_TAC bool_ss [MEM,FILTER,ALL_DISTINCT]
  \\ NTAC 2 STRIP_TAC \\ Cases_on `y = h` \\ ASM_REWRITE_TAC [LENGTH]
  \\ `!xs. ~MEM h xs ==> (FILTER (\x. ~(x = h)) xs = xs)` by (Induct \\ SRW_TAC [] [FILTER])
  \\ ASM_SIMP_TAC std_ss [ADD1,ADD_SUB,LENGTH]
  \\ Cases_on `xs` \\ REWRITE_TAC [MEM,LENGTH,ADD1,ADD_SUB]);

val LENGTH_LEAST_SORT = prove(
  ``!xs. ALL_DISTINCT xs ==> (LENGTH (LEAST_SORT xs) = LENGTH xs)``,
  recInduct LEAST_SORT_ind \\ SIMP_TAC std_ss [LENGTH,LEAST_SORT_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC ALL_DISTINCT_FILTER
  \\ Q.PAT_ASSUM `!g.b:bool` (ASSUME_TAC o Q.SPEC `\x'. ~(x' = LEAST_MEM (x::xs))`)
  \\ FULL_SIMP_TAC bool_ss [] 
  \\ ASSUME_TAC (Q.SPECL [`xs`,`x`] MEM_LEAST_MEM)
  \\ IMP_RES_TAC LENGTH_FILTER_NEQ \\ ASM_REWRITE_TAC [LENGTH,ADD1,ADD_SUB]);


val PERM_IMP_MEM_EQUALITY = prove(
  ``!xs ys. PERM xs ys ==> !x. MEM x xs = MEM x ys``,
  REPEAT STRIP_TAC
  \\ `!xs. MEM x xs = ~(FILTER ($= x) xs = [])` by (Induct \\ SRW_TAC [] [MEM,FILTER])
  \\ FULL_SIMP_TAC bool_ss [PERM_DEF]);

val ALL_DISTINCT_MOVE_CONS = prove(
  ``!xs ys. ALL_DISTINCT (xs ++ h::ys) = ALL_DISTINCT (h::xs ++ ys)``,
  Induct \\ ASM_SIMP_TAC bool_ss [APPEND,APPEND_NIL] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [ALL_DISTINCT,APPEND,MEM_APPEND,MEM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val PERM_ALL_DISTINCT = prove(
  ``!xs ys. ALL_DISTINCT xs /\ PERM xs ys ==> ALL_DISTINCT ys``,
  Induct \\ SIMP_TAC bool_ss [PERM_NIL,ALL_DISTINCT,PERM_CONS_EQ_APPEND]
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ IMP_RES_TAC PERM_IMP_MEM_EQUALITY
  \\ REWRITE_TAC [ALL_DISTINCT_MOVE_CONS,ALL_DISTINCT,APPEND] \\ METIS_TAC []);

val QSORT_SORTS_LS = prove(
  ``SORTS QSORT ($<=+ :'a word->'a word->bool)``,
  MATCH_MP_TAC QSORT_SORTS
  \\ REWRITE_TAC [transitive_def,total_def,WORD_LOWER_EQ_TRANS,WORD_LOWER_EQ_CASES]);

val SORTED_LO = prove(
  ``!xs. SORTED $<=+ xs /\ ALL_DISTINCT xs ==> SORTED $<+ (xs:'a word list)``,
  Induct \\ REWRITE_TAC [SORTED_DEF]
  \\ Cases_on `xs` \\ REWRITE_TAC [SORTED_DEF]
  \\ ONCE_REWRITE_TAC [ALL_DISTINCT]
  \\ REWRITE_TAC [MEM] \\ METIS_TAC [WORD_LOWER_OR_EQ]);

val ADDR_MODE4_UP_def = Define `
  (ADDR_MODE4_UP (am4_DA wb) = F) /\ 
  (ADDR_MODE4_UP (am4_FA wb) = F) /\ 
  (ADDR_MODE4_UP (am4_IA wb) = T) /\
  (ADDR_MODE4_UP (am4_FD wb) = T) /\
  (ADDR_MODE4_UP (am4_DB wb) = F) /\
  (ADDR_MODE4_UP (am4_EA wb) = F) /\
  (ADDR_MODE4_UP (am4_IB wb) = T) /\
  (ADDR_MODE4_UP (am4_ED wb) = T)`;

val ADDR_MODE4_wb_def = Define `
  (ADDR_MODE4_wb (am4_DA wb) = wb) /\ 
  (ADDR_MODE4_wb (am4_FA wb) = wb) /\ 
  (ADDR_MODE4_wb (am4_IA wb) = wb) /\
  (ADDR_MODE4_wb (am4_FD wb) = wb) /\
  (ADDR_MODE4_wb (am4_DB wb) = wb) /\
  (ADDR_MODE4_wb (am4_EA wb) = wb) /\
  (ADDR_MODE4_wb (am4_IB wb) = wb) /\
  (ADDR_MODE4_wb (am4_ED wb) = wb)`;

val ADDR_MODE4_WB'_def = Define `
  ADDR_MODE4_WB' am4 x n = 
    (if ADDR_MODE4_UP am4 then $+ else $-) x (n2w n)`;

val ADDR_MODE4_WB_def = Define `
  ADDR_MODE4_WB am4 x xs = 
    if ADDR_MODE4_wb am4 then ADDR_MODE4_WB' am4 x (LENGTH xs) else x`;

val ALL_DISTINCT_IMP_LENGTH_EQ = prove(
  ``!xs ys. ALL_DISTINCT xs /\ ALL_DISTINCT ys /\ (!x. MEM x xs = MEM x ys) ==>
            (LENGTH xs = LENGTH ys)``,
  Induct THEN1 (Cases_on `ys` \\ SRW_TAC [] [] \\ METIS_TAC [])
  \\ REWRITE_TAC [MEM] \\ REPEAT STRIP_TAC
  \\ `MEM h ys` by METIS_TAC []
  \\ `?hs zs. ys = hs ++ [h] ++ zs` by METIS_TAC [MEM_EQ_EXISTS]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,ALL_DISTINCT_MOVE_CONS,MEM,MEM_APPEND]
  \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT,MEM_APPEND,LENGTH,LENGTH_APPEND]
  \\ `!x. MEM x xs = MEM x (hs ++ zs)` by METIS_TAC [MEM_APPEND]
  \\ Q.PAT_ASSUM `!ys'. b ==> (c:bool)` IMP_RES_TAC  
  \\ ASM_REWRITE_TAC [ADD1,LENGTH_APPEND] \\ DECIDE_TAC);

val SORTED_LO_IMP_ALL_DISTINCT = prove(
  ``!xs. SORTED $<+ xs ==> ALL_DISTINCT xs``,
  Induct \\ REWRITE_TAC [SORTED_DEF,ALL_DISTINCT]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC SORTED_CONS_IMP \\ METIS_TAC []);

val REGISTER_LIST_LENGTH = prove(
  ``!xs. ALL_DISTINCT xs ==> (LENGTH (REGISTER_LIST (reg_bitmap xs)) = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ALL_DISTINCT_IMP_LENGTH_EQ
  \\ ASM_SIMP_TAC std_ss [MEM_REGISTER_LIST_reg_bitmap]
  \\ MATCH_MP_TAC SORTED_LO_IMP_ALL_DISTINCT \\ REWRITE_TAC [SORTED_REGISTER_LIST]);

val ADDR_MODE4_UP_THM = prove(
  ``!am4. (ADDR_MODE4_CMD am4).Up = ADDR_MODE4_UP am4``,
  Cases_on `am4` \\ SRW_TAC [] [ADDR_MODE4_CMD_def,ADDR_MODE4_UP_def]);

val WB_ADDRESS_EQ_ADDR_MODE4_WB' = prove(
  ``!am4 x xs. ALL_DISTINCT xs ==> 
         (WB_ADDRESS (ADDR_MODE4_CMD am4).Up (addr32 x) 
             (LENGTH (REGISTER_LIST (reg_bitmap xs))) = 
          addr32 (ADDR_MODE4_WB' am4 x (LENGTH xs)))``,
  REWRITE_TAC [ADDR_MODE4_def,ADDR_MODE4_WB'_def,WB_ADDRESS_def,UP_DOWN_def]
  \\ SIMP_TAC bool_ss [REGISTER_LIST_LENGTH,ADDR_MODE4_UP_THM] 
  \\ REPEAT STRIP_TAC \\ Cases_on `ADDR_MODE4_UP am4` 
  \\ ASM_REWRITE_TAC [addr32_ADD,addr32_SUB,addr32_n2w]);

val ADDR_MODE4_ADDR'_def = Define `
  (ADDR_MODE4_ADDR' (am4_DA wb) x y = y + 1w) /\ 
  (ADDR_MODE4_ADDR' (am4_FA wb) x y = y + 1w) /\ 
  (ADDR_MODE4_ADDR' (am4_IA wb) x y = x:word30) /\
  (ADDR_MODE4_ADDR' (am4_FD wb) x y = x) /\
  (ADDR_MODE4_ADDR' (am4_DB wb) x y = y) /\
  (ADDR_MODE4_ADDR' (am4_EA wb) x y = y) /\
  (ADDR_MODE4_ADDR' (am4_IB wb) x y = x + 1w) /\
  (ADDR_MODE4_ADDR' (am4_ED wb) x y = x + 1w)`;

val ADDR_MODE4_ADDR'_THM = prove(
  ``!am4 x xs.
      ALL_DISTINCT xs ==>
      (FIRST_ADDRESS (ADDR_MODE4_CMD am4).Pre (ADDR_MODE4_CMD am4).Up
        (addr32 x) (addr32 (ADDR_MODE4_WB' am4 x (LENGTH xs))) =
       addr32 (ADDR_MODE4_ADDR' am4 x (ADDR_MODE4_WB' am4 x (LENGTH xs))))``,
  Cases \\ SRW_TAC [] [ADDR_MODE4_ADDR'_def,FIRST_ADDRESS_def,ADDR_MODE4_CMD_def,addr32_SUC]);

val ADDR_MODE4_ADDR_def = Define `
  ADDR_MODE4_ADDR am4 x xs = ADDR_MODE4_ADDR' am4 x (ADDR_MODE4_WB' am4 x (LENGTH xs))`;

val ADDRESS_LIST'_def = Define `
  (ADDRESS_LIST' start 0 = []) /\
  (ADDRESS_LIST' start (SUC n) = start :: ADDRESS_LIST' (start + 4w) n)`;

val GENLIST_EQ = prove(
  ``!xs f n. (!k. k < n ==> (f k = EL k xs)) /\ (n = LENGTH xs) ==> (GENLIST f n = xs)``,
  recInduct SNOC_INDUCT \\ REPEAT STRIP_TAC 
  \\ FULL_SIMP_TAC std_ss [LENGTH,GENLIST,LENGTH_SNOC,SNOC_11]
  \\ `!k n. k < n ==> k < SUC n` by DECIDE_TAC
  \\ `!k. k < LENGTH l ==> (f k = EL k l)` by METIS_TAC [EL_SNOC]
  \\ `LENGTH l < SUC (LENGTH l)` by DECIDE_TAC
  \\ `f (LENGTH l) = EL (LENGTH l) (SNOC x l)` by METIS_TAC []     
  \\ ASM_REWRITE_TAC [EL_LENGTH_SNOC] 
  \\ Q.PAT_ASSUM `!f. b ==> (GENLIST f g = l)` MATCH_MP_TAC
  \\ ASM_REWRITE_TAC []);

val ADDRESS_LIST'_INTRO = prove(
  ``!n y. ADDRESS_LIST y n = ADDRESS_LIST' y n``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [ADDRESS_LIST_def] 
  \\ MATCH_MP_TAC GENLIST_EQ \\ SIMP_TAC std_ss []
  \\ Q.SPEC_TAC (`y`,`y`)
  \\ Induct_on `n` THEN1 SRW_TAC [] [LENGTH,ADDRESS_LIST'_def]
  \\ REPEAT STRIP_TAC << [
    Cases_on `k` \\ REWRITE_TAC [EL,WORD_MULT_CLAUSES,
       WORD_ADD_0,TL,HD,ADDRESS_LIST'_def,ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [],
    REWRITE_TAC [ADDRESS_LIST'_def,LENGTH] \\ METIS_TAC []]);

val ADDR_MODE4_ADDRESSES_def = Define `
  ADDR_MODE4_ADDRESSES am4 x xs = 
    ADDRESS_LIST' (addr32 (ADDR_MODE4_ADDR am4 x xs)) (LENGTH xs)`;

val ADDR_MODE4_FORMAT = prove(
  ``!am4 x xs.
      ALL_DISTINCT xs ==> 
      (ADDR_MODE4 (ADDR_MODE4_CMD am4).Pre 
          (ADDR_MODE4_CMD am4).Up (addr32 x) 
          (reg_bitmap xs) =
       (LEAST_SORT xs,
        ADDR_MODE4_ADDRESSES am4 x xs,
        addr32 (ADDR_MODE4_WB' am4 x (LENGTH xs))))``,
  SIMP_TAC std_ss [LET_DEF,ADDR_MODE4_def,WB_ADDRESS_EQ_ADDR_MODE4_WB',REGISTER_LIST_LENGTH]
  \\ SIMP_TAC std_ss [REGISTER_LIST_EQ_LEAST_SORT,ADDR_MODE4_ADDRESSES_def,
                      ADDR_MODE4_ADDR'_THM,ADDR_MODE4_ADDR_def,ADDRESS_LIST'_INTRO]);

val ADDR_MODE4_WB_THM = prove(
  ``!am4 p xs. 
      (reg Rd s = addr32 p) ==>
      ((if (ADDR_MODE4_CMD am4).Wb then
         INC_PC (REG_WRITE s.registers (state_mode s) Rd
           (addr32 (ADDR_MODE4_WB' am4 p (LENGTH (MAP FST xs)))))
        else INC_PC s.registers) =
       INC_PC (REG_WRITE s.registers (state_mode s) Rd
         (addr32 (ADDR_MODE4_WB am4 p (MAP FST xs)))))``,
  REPEAT STRIP_TAC 
  \\ `!am4. (ADDR_MODE4_CMD am4).Wb = ADDR_MODE4_wb am4` by 
        (Cases \\ SRW_TAC [] [ADDR_MODE4_CMD_def,ADDR_MODE4_wb_def])
  \\ ASM_REWRITE_TAC [ADDR_MODE4_WB_def] 
  \\ Cases_on `ADDR_MODE4_wb am4` \\ ASM_REWRITE_TAC []
  \\ Q.PAT_ASSUM `reg Rd s = addr32 p` (ASSUME_TAC o SYM)
  \\ ASM_REWRITE_TAC [reg_def]
  \\ Cases_on `Rd = 15w` \\ ASM_SIMP_TAC std_ss [REG_WRITE_READ]
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) 
       [REG_WRITE_def,mode_reg2num_def,num2register_thm,LET_DEF,
        EVAL ``w2n (15w:word4)``,INC_PC_def,SUBST_def]);

(* LDM instruction ------------------------------------------------------------- *)

val LDM_VALUES_def = Define `
  LDM_VALUES am4 x xs s = 
    ZIP (LEAST_SORT xs, MAP (s.memory o ADDR30) (ADDR_MODE4_ADDRESSES am4 x xs))`;

val MEM_MAP_FST_ZIP = prove(
  ``!xs ys x. (LENGTH xs = LENGTH ys) ==> (MEM x (MAP FST (ZIP (xs,ys))) = MEM x xs)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH,ZIP,MAP,MEM]
  THEN1 REWRITE_TAC [SUC_NOT] THEN1 METIS_TAC [SUC_NOT] \\ ASM_SIMP_TAC std_ss [MEM]);

val ALL_DISTINCT_MAP_FST_ZIP = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==> 
            (ALL_DISTINCT (MAP FST (ZIP (xs,ys))) = ALL_DISTINCT xs)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH]
  THEN1 SRW_TAC [] [ZIP,MAP,FST,ALL_DISTINCT]
  THEN1 REWRITE_TAC [SUC_NOT] THEN1 METIS_TAC [SUC_NOT]
  \\ ASM_SIMP_TAC bool_ss [ZIP,MAP,FST,ALL_DISTINCT,MEM_MAP_FST_ZIP]);  

val SORTED_LOWER_IMP_ALL_DISTINCT = prove(
  ``!xs. SORTED $<+ xs ==> ALL_DISTINCT xs``,
  Induct \\ SIMP_TAC std_ss [ALL_DISTINCT] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC SORTED_EQ_LOWER \\ METIS_TAC [WORD_LOWER_REFL]);

val ALL_DISTINCT_LEAST_SORT = prove(
  ``!xs. ALL_DISTINCT (LEAST_SORT xs)``,
  STRIP_TAC \\ MATCH_MP_TAC SORTED_LOWER_IMP_ALL_DISTINCT
  \\ REWRITE_TAC [SORTED_LEAST_SORT]);

val REG_WRITEL_INTRO = prove(
  ``!l r m. 
      ALL_DISTINCT (MAP FST l) ==>
      (FOLDL (\reg' (rp,rd). REG_WRITE reg' m rp rd) r l = REG_WRITEL r m l)``,
  Induct \\ SIMP_TAC std_ss [FOLDL,REG_WRITEL_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [REG_WRITEL_def,ALL_DISTINCT,MAP,FST]
  \\ `!l. ~MEM q (MAP FST l) ==> 
    (REG_WRITEL (REG_WRITE r m q r') m l = REG_WRITE (REG_WRITEL r m l) m q r')` 
          by ALL_TAC << [
    Induct \\ SIMP_TAC bool_ss [REG_WRITEL_def,MEM,MAP,FST] \\ REPEAT STRIP_TAC
    \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [REG_WRITEL_def] 
    \\ MATCH_MP_TAC REG_WRITE_WRITE_COMM \\ ASM_REWRITE_TAC [],
  METIS_TAC []]);

val LENGTH_ADDRESS_LIST' = prove(
  ``!n x. LENGTH (ADDRESS_LIST' x n) = n``,
  Induct \\ SRW_TAC [] [LENGTH,ADDRESS_LIST'_def]);

val LDM_WRITEL_INTRO_LEMMA = prove(
  ``!xs. 
      ALL_DISTINCT xs ==> 
      (LENGTH (LEAST_SORT xs) = 
       LENGTH (MAP g (ADDR_MODE4_ADDRESSES am4 x xs)))``,
  SIMP_TAC std_ss 
    [LENGTH_LEAST_SORT,ADDR_MODE4_ADDRESSES_def,LENGTH_ADDRESS_LIST',LENGTH_MAP]);
  
val LDM_WRITEL_INTRO = prove(
  ``!xs r m. 
      ALL_DISTINCT xs ==>
      (FOLDL (\reg' (rp,rd). REG_WRITE reg' m rp rd) r (LDM_VALUES am4 x xs s) = 
       REG_WRITEL r m (LDM_VALUES am4 x xs s))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC REG_WRITEL_INTRO
  \\ `LENGTH (LEAST_SORT xs) = 
      LENGTH (MAP (s.memory o ADDR30) (ADDR_MODE4_ADDRESSES am4 x xs))`
             by ASM_SIMP_TAC std_ss [LENGTH_LEAST_SORT,LENGTH_ADDRESS_LIST',
                                     ADDR_MODE4_ADDRESSES_def,LENGTH_MAP]
  \\ IMP_RES_TAC ALL_DISTINCT_MAP_FST_ZIP
  \\ ASM_SIMP_TAC std_ss [LDM_VALUES_def,ALL_DISTINCT_LEAST_SORT]);

val LDM_STATE_def = Define `
  LDM_STATE am4 p xs Rd s =
  <|registers :=
            REG_WRITEL
              (INC_PC
                 (REG_WRITE s.registers (state_mode s) Rd
                    (addr32 (ADDR_MODE4_WB am4 p (MAP FST xs)))))
              (state_mode s)
              (ZIP
                 (LEAST_SORT (MAP FST xs),
                  MAP (s.memory o ADDR30)
                    (ADDRESS_LIST'
                       (addr32 (ADDR_MODE4_ADDR am4 p (MAP FST xs)))
                       (LENGTH (MAP FST xs))))); psrs := s.psrs;
          memory := s.memory; undefined := F|>`;

val ldm = simple_clean ARM_LDM [``~(Rd = 15w:word4)``]
val ldm = Q.INST [`opt`|->`ADDR_MODE4_CMD am4`] ldm
val ldm = Q.INST [`list`|->`reg_bitmap (MAP FST (xs:(word4 # word32) list))`] ldm
val ldm = Q.INST [`s_flag`|->`F`] ldm
val ldm = DISCH ``reg Rd s = addr32 p`` ldm
val ldm = DISCH ``ALL_DISTINCT (MAP FST (xs:(word4 # word32) list))`` ldm
val ldm = SIMP_RULE bool_ss [ADDR_MODE4_FORMAT,FST,SND,ADDR_MODE4_WB_THM,
                             GSYM LDM_VALUES_def,LDM_WRITEL_INTRO] ldm
val ldm = REWRITE_RULE [LDM_VALUES_def,GSYM LDM_STATE_def,ADDR_MODE4_ADDRESSES_def] ldm


val reg_values_def = Define ` 
  reg_values = MAP SND o QSORT (\x y. FST x <=+ FST y)`;
  
val LDM_PRE_EXPANSION = let
  val xs = `(15w,SOME x1)::(a,SOME x2)::xs`;
  val ys = `[(b1,xM_seq [y1]);(b3,xM_seq y3)]`;
  val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(T,g)`);
  val th = sep_pred_semantics (xs,ys,st,ud,rt,cd);
  in th end;

val LDM_POST_EXPANSION = let
  val xs = `(15w,SOME x1)::(a,SOME x2)::xs`;
  val ys = `[(b1,xM_seq [y1]);(b3,xM_seq y3)]`;
  val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(F,g)`);
  val th = sep_pred_semantics (xs,ys,st,ud,rt,cd);
  in th end;

val LDM_SIMP_LEMMA = prove(
  ``!xs. (MAP FST (MAP (\x. (FST x,NONE)) xs) = MAP FST xs) /\ 
         (MAP FST (MAP (\x. (FST x,SOME (SND x))) xs) = MAP FST xs)``,
  Induct \\ SRW_TAC [] []);

val MEM_LOWEST = prove(
  ``!xs. 0 < LENGTH xs ==> ?h. MEM h xs /\ !x. MEM x xs ==> h <=+ x``,
  Induct \\ FULL_SIMP_TAC std_ss [LENGTH,MEM] \\ REPEAT STRIP_TAC  
  \\ Cases_on `?y. MEM y xs /\ y <=+ h` << [  
    `?y. MEM y xs /\ y <=+ h` by METIS_TAC []
    \\ Cases_on `xs` THEN1 FULL_SIMP_TAC std_ss [MEM]
    \\ FULL_SIMP_TAC bool_ss [LENGTH,DECIDE ``0 < SUC n = T``]
    \\ Q.EXISTS_TAC `h''` \\ ASM_REWRITE_TAC []
    \\ METIS_TAC [WORD_LOWER_EQ_TRANS],
    Q.EXISTS_TAC `h` \\ FULL_SIMP_TAC bool_ss []
    \\ METIS_TAC [WORD_LOWER_EQ_CASES,WORD_LOWER_EQ_REFL]]);

val PERM_IMPs = prove(
  ``!xs ys. PERM xs ys ==> (LENGTH xs = LENGTH ys) /\ !x. MEM x xs = MEM x ys``,
  Induct \\ SIMP_TAC bool_ss [PERM_NIL,PERM_CONS_EQ_APPEND,LENGTH]
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []
  \\ Q.PAT_ASSUM `!ys. b:bool` IMP_RES_TAC 
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,MEM,MEM_APPEND] THEN1 DECIDE_TAC
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss []);

val LDM_mem_SIMP = prove(
  ``!ys y s g. 
      ms_sem y ys <|registers := g; psrs := s.psrs; memory := s.memory; undefined := F|> =
      ms_sem y ys s``,
  Induct \\ SRW_TAC [] [ms_sem_def,mem_def]);

val LDM_VALUES_0 = prove(
  ``!xs.
      (0 = LENGTH xs) ==> 
      (ZIP (LEAST_SORT xs,
            MAP (s.memory o ADDR30) (ADDRESS_LIST' (addr32 y) (LENGTH xs))) = [])``,
  Cases \\ SRW_TAC [] [LENGTH,LEAST_SORT_def,ADDR_MODE4_ADDRESSES_def,ADDRESS_LIST'_def]);

val LDM_VALUES_SUC = prove(
  ``!xs:word4 list n. 
      ALL_DISTINCT xs ==> (SUC n = LENGTH xs) ==> 
      ?ys. 
        !y. (ZIP
              (LEAST_SORT xs,
                MAP (s.memory o ADDR30) (ADDRESS_LIST' (addr32 y) (LENGTH xs))) = 
              (LEAST_MEM xs,s.memory y)::
                ZIP
                  (LEAST_SORT ys,
                 MAP (s.memory o ADDR30) (ADDRESS_LIST' (addr32 (y+1w)) (LENGTH ys)))) /\
           (n = LENGTH ys) /\ ALL_DISTINCT ys /\ !x. MEM x (LEAST_MEM xs::ys) = MEM x xs``,
  REPEAT STRIP_TAC \\ Cases_on `xs` 
  \\ FULL_SIMP_TAC std_ss [LENGTH] THEN1 METIS_TAC [SUC_NOT]
  \\ FULL_SIMP_TAC std_ss [LEAST_SORT_def,LET_DEF,ADDRESS_LIST'_def,MAP,ADDR30_def,
     GSYM addr30_def,addr30_addr32,ZIP,CONS_11]  
  \\ Q.EXISTS_TAC `FILTER (\x. ~(x = LEAST_MEM (h::t))) (h::t)`  
  \\ `MEM (LEAST_MEM (h::t)) (h::t)` by METIS_TAC [MEM_LEAST_MEM]
  \\ IMP_RES_TAC LENGTH_FILTER_NEQ  
  \\ FULL_SIMP_TAC bool_ss [LENGTH,ADD1,ADD_SUB,addr32_SUC]
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC [ALL_DISTINCT_FILTER]  
  \\ SIMP_TAC std_ss [MEM,MEM_FILTER]
  \\ Cases_on `x = LEAST_MEM (h::t)` \\ ASM_REWRITE_TAC []
  \\ METIS_TAC [MEM_LEAST_MEM,MEM]);
  
val MEM_NOT_MEM_IMP_NEQ = prove(
  ``!xs x y. MEM x xs /\ ~MEM y xs ==> ~(x = y)``,
  REPEAT STRIP_TAC
  \\ `?ys zs. xs = ys ++ [x] ++ zs` by METIS_TAC [MEM_EQ_EXISTS]
  \\ FULL_SIMP_TAC std_ss [MEM_APPEND,MEM]);

val reg_15_LDM_STATE = prove(
  ``ALL_DISTINCT (MAP FST xs) /\ (reg 15w s = addr32 p) /\ 
    ~MEM 15w (MAP FST xs) /\ ~(a = 15w) ==>
    (reg 15w (LDM_STATE am4 x xs a s) = addr32 (pcADD 1w p))``,
  SIMP_TAC (srw_ss()) [LDM_STATE_def,reg_def] 
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))`,`y`)
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP]
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`MAP FST xs`,`xs`) \\ STRIP_TAC
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x xs`,`w`)
  \\ Induct_on `LENGTH xs` << [
    SIMP_TAC std_ss [LDM_VALUES_0,REG_WRITEL_def,INC_PC_r15,REG_WRITE_r15,pcADD_def] 
    \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ REWRITE_TAC [addr32_SUC] 
    \\ METIS_TAC [WORD_ADD_COMM],  
    REPEAT STRIP_TAC
    \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o Q.SPECL [`xs`,`v`]) LDM_VALUES_SUC
    \\ FULL_SIMP_TAC bool_ss [REG_WRITEL_def]    
    \\ Cases_on `xs` THEN1 METIS_TAC [LENGTH,SUC_NOT]
    \\ `MEM (LEAST_MEM (h::t)) (h::t)` by METIS_TAC [MEM_LEAST_MEM]    
    \\ IMP_RES_TAC MEM_NOT_MEM_IMP_NEQ
    \\ ASM_SIMP_TAC std_ss [REG_WRITE_r15]
    \\ `~MEM 15w ys` by METIS_TAC [MEM]
    \\ `ALL_DISTINCT ys` by METIS_TAC []
    \\ `LENGTH ys = LENGTH ys` by REWRITE_TAC []
    \\ Q.PAT_ASSUM `!xs'. b ==> c:bool` 
           (STRIP_ASSUME_TAC o UD_ALL o Q.SPECL [`w+1w`,`y`] o UD_ALL o Q.SPEC `ys`)]);

val state_mode_simp = prove(
  ``state_mode <|registers := r; psrs := s.psrs; memory := m; undefined := b|> =
    state_mode s``,SRW_TAC [] [state_mode_def]);

val reg_wb_LDM_STATE = prove(
  ``ALL_DISTINCT (MAP FST xs) /\ ~MEM a (MAP FST xs) /\ ~(a = 15w) ==>
    (reg a (LDM_STATE am4 x xs a s) = addr32 (ADDR_MODE4_WB am4 x xs))``,
  SIMP_TAC (srw_ss()) [LDM_STATE_def,reg_def,ADDR_MODE4_WB_def] 
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP]
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ REWRITE_TAC [GSYM ADDR_MODE4_WB_def] 
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))`,`y`)
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST xs)`,`w`)
  \\ Q.SPEC_TAC (`MAP FST xs`,`xs`) \\ STRIP_TAC
  \\ REWRITE_TAC [state_mode_simp]
  \\ Induct_on `LENGTH xs`
  THEN1 SIMP_TAC std_ss [LDM_VALUES_0,REG_WRITEL_def,REG_READ_INC_PC,
    REG_READ_WRITE_NEQ,pcADD_def,REG_READ_WRITE] 
  \\ REPEAT STRIP_TAC
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o Q.SPECL [`xs`,`v`]) LDM_VALUES_SUC
  \\ FULL_SIMP_TAC bool_ss [REG_WRITEL_def]    
  \\ Cases_on `xs` THEN1 METIS_TAC [LENGTH,SUC_NOT]
  \\ `MEM (LEAST_MEM (h::t)) (h::t)` by METIS_TAC [MEM_LEAST_MEM]    
  \\ IMP_RES_TAC MEM_NOT_MEM_IMP_NEQ
  \\ ASM_SIMP_TAC std_ss [REG_READ_WRITE_NEQ2]
  \\ `~MEM a ys` by METIS_TAC [MEM]
  \\ `ALL_DISTINCT ys` by METIS_TAC []
  \\ `LENGTH ys = LENGTH ys` by REWRITE_TAC []
  \\ Q.PAT_ASSUM `!xs'. b ==> c:bool` 
           (STRIP_ASSUME_TAC o UD_ALL o Q.SPECL [`w+1w`,`y`] o UD_ALL o Q.SPEC `ys`));

val xR_list_sem_PERM_LEMMA = prove(
  ``!xs ys h. xR_list_sem (xs++h::ys) = xR_list_sem (h::(xs++ys))``,
  Induct \\ SIMP_TAC std_ss [xR_list_def,FUN_EQ_THM,APPEND]
  \\ Cases_on `h` \\ Cases_on `r` \\ ASM_REWRITE_TAC [xR_list_sem_def]
  \\ Cases_on `h'` \\ Cases_on `r` \\ ASM_REWRITE_TAC [xR_list_sem_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SIMP_TAC std_ss []);

val xR_list_sem_PERM = prove(
  ``!xs ys. PERM xs ys ==> (xR_list_sem xs = xR_list_sem ys)``,
  REWRITE_TAC [FUN_EQ_THM] 
  \\ Induct \\ SIMP_TAC bool_ss [PERM_NIL,PERM_CONS_EQ_APPEND] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [xR_list_sem_PERM_LEMMA]
  \\ Cases_on `h` \\ Cases_on `r` \\ ASM_REWRITE_TAC [xR_list_sem_def]
  \\ METIS_TAC []);

val PERM_MAP = prove(
  ``!xs ys. PERM xs ys ==> PERM (MAP f xs) (MAP f ys)``,
  Induct \\ SIMP_TAC bool_ss [PERM_NIL,PERM_CONS_EQ_APPEND,PERM_REFL] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [MAP,MAP_APPEND] \\ ONCE_REWRITE_TAC [PERM_SYM]
  \\ MATCH_MP_TAC APPEND_PERM_SYM \\ REWRITE_TAC [APPEND,PERM_CONS_IFF]
  \\ MATCH_MP_TAC APPEND_PERM_SYM \\ ONCE_REWRITE_TAC [PERM_SYM]
  \\ ASM_SIMP_TAC bool_ss [GSYM MAP_APPEND]);

val SORTS_QSORT_FST_LOWER_EQ = prove(
  ``SORTS QSORT (\x y. FST x <=+ FST y)``,
  MATCH_MP_TAC QSORT_SORTS \\ REWRITE_TAC [transitive_def,total_def] 
  \\ REPEAT STRIP_TAC \\ Cases_on `x` \\ Cases_on `y`
  \\ FULL_SIMP_TAC std_ss [WORD_LOWER_EQ_CASES]
  \\ Cases_on `z` \\ FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC WORD_LOWER_EQ_TRANS 
  \\ Q.EXISTS_TAC `q'` \\ ASM_REWRITE_TAC []);

val LENGTH_reg_values = prove(
  ``!xs. LENGTH (reg_values xs) = LENGTH xs``,
  SIMP_TAC std_ss [reg_values_def,LENGTH_MAP] \\ REPEAT STRIP_TAC 
  \\ MATCH_MP_TAC PERM_LENGTH \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF,PERM_SYM]);

val xR_list_sem_QSORT_INTRO = prove(
  ``!f xs. 
       xR_list_sem (MAP f xs) = xR_list_sem ((MAP f o QSORT (\x y. FST x <=+ FST y)) xs)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC xR_list_sem_PERM \\ SIMP_TAC std_ss []
  \\ MATCH_MP_TAC PERM_MAP \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF]);

val MEM_ALL_MEM_ALL_MAP = prove(
  ``!xs ys. (!a. MEM a xs = MEM a ys) ==> (!a. MEM a (MAP f xs) = MEM a (MAP f ys))``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [MEM_MAP] \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `y` \\ ASM_REWRITE_TAC [] \\ METIS_TAC []);

val MEM_MAP_QSORT_INTRO = prove(
  ``!xs a. MEM a (MAP FST xs) = MEM a ((MAP FST o QSORT (\x y. FST x <=+ FST y)) xs)``,
  SIMP_TAC std_ss [] \\ STRIP_TAC \\ MATCH_MP_TAC MEM_ALL_MEM_ALL_MAP
  \\ MATCH_MP_TAC PERM_IMP_MEM_EQUALITY \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF]);

val PERM_IMP_ALL_DISTINCT_EQ = prove(
  ``!xs ys. PERM xs ys ==> (ALL_DISTINCT xs = ALL_DISTINCT ys)``,
  Induct \\ SIMP_TAC bool_ss [PERM_NIL,PERM_CONS_EQ_APPEND] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [ALL_DISTINCT] \\ IMP_RES_TAC PERM_IMP_MEM_EQUALITY
  \\ `!M'. ALL_DISTINCT (M' ++ h::N) = ALL_DISTINCT (h::(M' ++ N))` by     
        (Induct \\ ASM_SIMP_TAC bool_ss [APPEND,ALL_DISTINCT,MEM,MEM_APPEND]
         \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC bool_ss [ALL_DISTINCT] \\ METIS_TAC []);

val ALL_DISTINCT_QSORT_INTRO = prove(
  ``!xs. ALL_DISTINCT (MAP FST xs) =
         ALL_DISTINCT ((MAP FST o QSORT (\x y. FST x <=+ FST y)) xs)``,
  STRIP_TAC \\ MATCH_MP_TAC PERM_IMP_ALL_DISTINCT_EQ \\ SIMP_TAC std_ss []
  \\ MATCH_MP_TAC PERM_MAP \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF]);

val LENGTH_QSORT_INTRO = prove(
  ``!xs. LENGTH (MAP FST xs) = LENGTH (QSORT (\x y. FST x <=+ FST y) xs)``,
  STRIP_TAC \\ REWRITE_TAC [LENGTH_MAP] \\ MATCH_MP_TAC PERM_LENGTH 
  \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF]);

val SORTED_MAP = prove(
  ``!xs f g. SORTED g (MAP f xs) = SORTED (\x y. g (f x) (f y)) xs``,
  Induct \\ REWRITE_TAC [SORTED_DEF,MAP]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [SORTED_DEF,MAP]);

val LEAST_SORT_EQ_QSORT = prove(
  ``!xs. ALL_DISTINCT (MAP FST xs) ==>
         (LEAST_SORT (MAP FST xs) = MAP FST (QSORT (\x y. FST x <=+ FST y) xs))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC SORTED_LO_IMP_EQ  
  \\ REWRITE_TAC [SORTED_LEAST_SORT,MEM_LEAST_SORT] \\ REPEAT STRIP_TAC << [
    MATCH_MP_TAC SORTED_LO
    \\ ASM_REWRITE_TAC [SIMP_RULE std_ss [] (GSYM ALL_DISTINCT_QSORT_INTRO)]
    \\ REWRITE_TAC [SORTED_MAP] \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF],
    SIMP_TAC std_ss [SIMP_RULE std_ss [] (GSYM MEM_MAP_QSORT_INTRO)]]);

val xR_list_sem_IGNORE_REG_WRITE = prove(
  ``!xs r q ax regs.
      ~MEM q (MAP FST xs) ==>
      (xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs)
         <| registers := REG_WRITE regs (state_mode s) q r; 
            psrs := s.psrs; memory := mt; undefined := bt |> =
       xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs)
         <| registers := regs; psrs := s.psrs; memory := mt; undefined := bt |>)``,
  Induct THEN1 REWRITE_TAC [xR_list_sem_def,MAP] \\ Cases
  \\ SIMP_TAC std_ss [MAP,xR_list_sem_def,MEM] \\ Cases_on `q = 15w`
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!s.b` IMP_RES_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [reg_def,state_mode_simp,REG_READ_WRITE_NEQ2]
  \\ `~(15w = q')` by METIS_TAC [] \\ ASM_SIMP_TAC std_ss [REG_WRITE_r15]);

val xR_list_sem_LDM_STATE = prove(
  ``ALL_DISTINCT (MAP FST xs) /\ 
    ms_sem (ADDR_MODE4_ADDR am4 x xs) (reg_values xs) s ==>
    xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) (LDM_STATE am4 x xs a s)``,
  REWRITE_TAC [LDM_STATE_def,ADDR_MODE4_ADDR_def,reg_values_def]     
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP]
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ REWRITE_TAC [GSYM ADDR_MODE4_ADDR_def] 
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST xs)`,`ax`)
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))`,`y`)
  \\ SIMP_TAC bool_ss [LEAST_SORT_EQ_QSORT]
  \\ REWRITE_TAC [xR_list_sem_QSORT_INTRO,MEM_MAP_QSORT_INTRO,
                  ALL_DISTINCT_QSORT_INTRO,LENGTH_QSORT_INTRO]
  \\ SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`QSORT (\x y. FST x <=+ FST y) xs`,`xs`)
  \\ Induct \\ REWRITE_TAC [MAP,xR_list_sem_def]
  \\ Cases \\ SIMP_TAC (srw_ss()) [xR_list_sem_def,reg_def,MEM,state_mode_simp,ms_sem_def]
  \\ SIMP_TAC std_ss [ADDRESS_LIST'_def,MAP,ADDR30_def,GSYM addr30_def,addr30_addr32,ZIP]
  \\ SIMP_TAC bool_ss [REG_WRITEL_def,REG_READ_WRITE,mem_def,REG_WRITE_15]
  \\ ASM_SIMP_TAC bool_ss [xR_list_sem_IGNORE_REG_WRITE,GSYM addr32_SUC] \\ METIS_TAC []);

val status_LDM_STATE = prove(
  ``status (LDM_STATE am4 x xs a s) = status s``,
  SRW_TAC [] [LDM_STATE_def,status_def,statusN_def,statusZ_def,statusC_def,statusV_def]);

val mem_LDM_STATE = prove(
  ``mem p (LDM_STATE am4 x xs a s) = mem p s``,
  SRW_TAC [] [LDM_STATE_def,mem_def]);

val ms_sem_LDM_STATE = prove(
  ``ms_sem x xs (LDM_STATE am4 y ys a s) = ms_sem x xs s``,
  Q.SPEC_TAC (`x`,`x`) \\ Induct_on `xs` \\ ASM_REWRITE_TAC [ms_sem_def,mem_LDM_STATE]);

val undef_LDM_STATE = prove(
  ``(LDM_STATE am4 x xs a s).undefined = F``, SRW_TAC [] [LDM_STATE_def]);

val owrt_visible_LDM_STATE = prove(
  ``owrt_visible (LDM_STATE am4 x xs a s) = owrt_visible s``,
  SRW_TAC [] [owrt_visible_def,LDM_STATE_def,set_status_def,owrt_visible_regs_def,
              state_mode_simp,REG_OWRT_ALL]);

val xs = `[(a1,SOME x1)]`;
val ys = `[(b1,xM_seq [y1])]`;
val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(F,g)`);
val NOP_sem = sep_pred_semantics (xs,ys,st,ud,rt,cd);

val IMP_ARM_NOP = prove(
  ``(!state cpsr.
       (state.memory ((31 >< 2) (state.registers r15)) = cmd) /\
       Abbrev (cpsr = CPSR_READ state.psrs) /\
       ~CONDITION_PASSED2 (NZCV cpsr) c /\ ~state.undefined ==>
       (NEXT_ARM_MEM state =
        <|registers := INC_PC state.registers; psrs := state.psrs;
          memory := state.memory; undefined := F|>)) ==>
    ARM_NOP c [cmd]``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [ARM_NOP_def,ARM_PROG1_EQ,nPASS_def]  
  \\ MOVE_STAR_TAC `st*cc*mp*pc*ud` `cc*(st*mp*pc*ud)`
  \\ REWRITE_TAC [cond_STAR]
  \\ MOVE_STAR_TAC `st*mp*pc*ud` `pc*mp*st*ud`
  \\ SIMP_TAC bool_ss [NOP_sem,ALL_DISTINCT,MEM,ALL_DISJOINT_def,EVERY_DEF,mem_def,reg_def]
  \\ FULL_SIMP_TAC bool_ss [markerTheory.Abbrev_def,GSYM addr30_def,GSYM status_THM]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `1` \\ REWRITE_TAC [STATE_ARM_MEM_1]
  \\ `s.memory (addr30 (s.registers r15)) = cmd` by METIS_TAC [addr30_addr32]
  \\ Q.PAT_ASSUM `!state. b:bool` (STRIP_ASSUME_TAC o Q.SPEC `s`)
  \\ FULL_SIMP_TAC (srw_ss()) [status_THM,INC_PC_r15,pcADD_def,GSYM addr32_SUC]
  \\ STRIP_TAC THEN1 METIS_TAC [WORD_ADD_COMM] 
  \\ REWRITE_TAC [arm2set''_EQ,IN_INSERT,NOT_IN_EMPTY]
  \\ ASM_SIMP_TAC (srw_ss()) [reg_def,mem_def,REG_READ_INC_PC,state_mode_def,
      owrt_visible_def,set_status_def,owrt_visible_regs_def,REG_OWRT_ALL]);  

fun MAKE_ARM_NOP nop_rule = 
  MATCH_MP IMP_ARM_NOP ((Q.GEN `state` o Q.GEN `cpsr` o SPEC_ALL) nop_rule);

val IMP_ARM_PROG2 = prove(
  ``ARM_NOP c cs ==> (ARM_PROG P cs {} Q Z ==> ARM_PROG2 c P cs Q Z)``,
  SIMP_TAC std_ss [ARM_PROG2_def]);

fun MAKE_PROG2 th nop_rule = 
  MATCH_MP (MATCH_MP IMP_ARM_PROG2 (MAKE_ARM_NOP nop_rule)) th;

val raw_LDM = prove(
  ``ARM_PROG 
     (R30 a x * 
      xR_list (MAP (\x.(FST x,NONE)) xs) * 
      ms (ADDR_MODE4_ADDR am4 x xs) (reg_values xs) * S st * PASS c st) 
     [enc (LDM c F (ADDR_MODE4_CMD am4) a (reg_bitmap (MAP FST xs)))] {}
     (R30 a (ADDR_MODE4_WB am4 x xs) *
      xR_list (MAP (\x.(FST x,SOME (SND x))) xs) *
      ms (ADDR_MODE4_ADDR am4 x xs) (reg_values xs) * S st) {}``,
  ARM_PROG_INIT_TAC 
  \\ ASM_MOVE_STAR_TAC `a*xs*mm*st*cd*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud*cd`
  \\ MOVE_STAR_TAC `a*xs*mm*st*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud`
  \\ FULL_SIMP_TAC bool_ss [R30_def,LDM_PRE_EXPANSION,LDM_POST_EXPANSION,
         LDM_SIMP_LEMMA,ALL_DISTINCT,MEM]
  \\ `CONDITION_PASSED2 (status s) c` by METIS_TAC []
  \\ `mem (addr30 (reg 15w s)) s =
      enc (LDM c F (ADDR_MODE4_CMD am4) a (reg_bitmap (MAP FST xs)))` 
         by METIS_TAC [addr30_addr32]
  \\ `~(a = 15w)` by METIS_TAC []
  \\ ASSUME_TAC ((UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o 
                  Q.INST [`p`|->`x`,`Rd`|->`a`]) ldm)
  \\ ASM_REWRITE_TAC [] \\ PAT_ASSUM `` NEXT_ARM_MEM s = s'`` (fn th => ALL_TAC)
  \\ STRIP_TAC 
  THEN1 ASM_SIMP_TAC bool_ss [reg_15_LDM_STATE,reg_wb_LDM_STATE,xR_list_sem_LDM_STATE,
     status_LDM_STATE,mem_LDM_STATE,ms_sem_LDM_STATE,undef_LDM_STATE]
  \\ REWRITE_TAC [arm2set''_EQ,mem_LDM_STATE,owrt_visible_LDM_STATE]
  \\ SIMP_TAC (srw_ss()) [IN_INSERT,IN_LIST_TO_SET,LDM_STATE_def,reg_def,state_mode_simp]
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP]
  \\ ASM_SIMP_TAC bool_ss [LEAST_SORT_EQ_QSORT]
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST xs)`,`ax`)
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))`,`y`)
  \\ REWRITE_TAC [xR_list_sem_QSORT_INTRO,MEM_MAP_QSORT_INTRO,
                  ALL_DISTINCT_QSORT_INTRO,LENGTH_QSORT_INTRO]
  \\ SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`QSORT (\x y. FST x <=+ FST y) xs`,`xs`)
  \\ Induct \\ REWRITE_TAC [REG_WRITEL_def,MAP,LENGTH,ADDRESS_LIST'_def,ZIP]
  \\ ASM_SIMP_TAC std_ss [REG_READ_INC_PC,REG_READ_WRITE_NEQ2,MEM,GSYM addr32_SUC]);

val arm_LDM = MAKE_PROG2 raw_LDM ARM_LDM_NOP;
val arm_LDM = Q.INST [`c`|->`c_flag`,`st`|->`(sN,sZ,sC,Sv)`,`am4`|->`a_mode`] arm_LDM;

val raw_LDM_PC = prove(
  ``ARM_PROG 
     (R30 a x * 
      xR_list (MAP (\x.(FST x,NONE)) xs) * 
      ms (ADDR_MODE4_ADDR am4 x ((15w,addr32 p)::xs)) 
         (reg_values ((15w,addr32 p)::xs)) * S st * PASS c st) 
     [enc (LDM c F (ADDR_MODE4_CMD am4) a (reg_bitmap (15w :: MAP FST xs)))] {} SEP_F
     {(R30 a (ADDR_MODE4_WB am4 x ((15w,addr32 p)::xs)) *
       xR_list (MAP (\x.(FST x,SOME (SND x))) xs) *
       ms (ADDR_MODE4_ADDR am4 x ((15w,addr32 p)::xs)) (reg_values ((15w,addr32 p)::xs)) * S st,pcSET p)}``,
  ARM_PROG_INIT_TAC \\ SIMP_TAC (bool_ss++sep_ss) [pcSET_def] \\ REWRITE_TAC [SEP_F_def]
  \\ ASM_MOVE_STAR_TAC `a*xs*mm*st*cd*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud*cd`
  \\ MOVE_STAR_TAC `a*xs*mm*st*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud`
  \\ FULL_SIMP_TAC bool_ss [R30_def,LDM_PRE_EXPANSION,LDM_POST_EXPANSION,
         LDM_SIMP_LEMMA,ALL_DISTINCT,MEM]
  \\ `CONDITION_PASSED2 (status s) c` by METIS_TAC []
  \\ `mem (addr30 (reg 15w s)) s =
      enc (LDM c F (ADDR_MODE4_CMD am4) a (reg_bitmap (15w::MAP FST xs)))` 
         by METIS_TAC [addr30_addr32]
  \\ `~(a = 15w)` by METIS_TAC []
  \\ ASSUME_TAC ((UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o 
                  SIMP_RULE std_ss [MAP,ALL_DISTINCT,GSYM AND_IMP_INTRO] o
                  Q.INST [`p`|->`x`,`Rd`|->`a`,`xs`|->`(15w,addr32 p)::xs`]) ldm)
  \\ ASM_REWRITE_TAC [] \\ PAT_ASSUM `` NEXT_ARM_MEM s = s'`` (fn th => ALL_TAC)
  \\ `ALL_DISTINCT (MAP FST ((15w,addr32 p)::xs))` by ASM_SIMP_TAC std_ss [ALL_DISTINCT,MAP]
  \\ `~MEM a (MAP FST ((15w,addr32 p)::xs))` by ASM_SIMP_TAC std_ss [MEM,MAP]
  \\ ASM_SIMP_TAC bool_ss [reg_15_LDM_STATE,reg_wb_LDM_STATE,xR_list_sem_LDM_STATE,
       status_LDM_STATE,mem_LDM_STATE,ms_sem_LDM_STATE,undef_LDM_STATE]
  \\ STRIP_TAC THEN1 
    (ONCE_REWRITE_TAC [GSYM xR_list_sem_def]
     \\ `(15w,SOME (addr32 p))::MAP (\x. (FST x,SOME (SND x))) xs = 
         MAP (\x. (FST x,SOME (SND x))) ((15w,addr32 p)::xs)` by SIMP_TAC std_ss [MAP]  
     \\ ASM_SIMP_TAC bool_ss [xR_list_sem_LDM_STATE])
  \\ REWRITE_TAC [arm2set''_EQ,mem_LDM_STATE,owrt_visible_LDM_STATE]
  \\ SIMP_TAC (srw_ss()) [IN_INSERT,IN_LIST_TO_SET,LDM_STATE_def,reg_def,state_mode_simp]
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP]
  \\ `15w::(MAP FST xs) = MAP FST ((15w,addr32 p)::xs)` by SIMP_TAC std_ss [MAP]
  \\ ASM_SIMP_TAC bool_ss [LEAST_SORT_EQ_QSORT]
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST ((15w,addr32 p)::xs))`,`ax`)
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB am4 x (MAP FST ((15w,addr32 p)::xs)))`,`y`)
  \\ `!r a. ~(r = 15w) /\ ~(r = a) /\ ~MEM r (MAP FST xs) =
         ~(r = 15w) /\ ~(r = a) /\ ~MEM r (MAP FST ((15w,addr32 p)::xs))` by 
            (SIMP_TAC std_ss [MEM,MAP] \\ METIS_TAC [])
  \\ `!p. SUC (LENGTH (MAP FST xs)) = LENGTH (MAP FST ((15w,addr32 p)::xs))` by 
                         (SIMP_TAC std_ss [MEM,MAP,LENGTH] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [] \\ REWRITE_TAC [xR_list_sem_QSORT_INTRO,
       MEM_MAP_QSORT_INTRO,ALL_DISTINCT_QSORT_INTRO,LENGTH_QSORT_INTRO]
  \\ SIMP_TAC std_ss [] 
  \\ Q.SPEC_TAC (`QSORT (\x y. FST x <=+ FST y) ((15w,addr32 p)::xs)`,`xs`)
  \\ Induct \\ REWRITE_TAC [REG_WRITEL_def,MAP,LENGTH,ADDRESS_LIST'_def,ZIP]
  \\ ASM_SIMP_TAC std_ss [REG_READ_INC_PC,REG_READ_WRITE_NEQ2,MEM,GSYM addr32_SUC]);

val arm_LDM_PC = MAKE_PROG2 raw_LDM_PC ARM_LDM_NOP;
val arm_LDM_PC = Q.INST [`c`|->`c_flag`,`st`|->`(sN,sZ,sC,Sv)`,`am4`|->`a_mode`] arm_LDM_PC;

val _ = save_thm("arm_LDM",arm_LDM);
val _ = save_thm("arm_LDM_PC",arm_LDM_PC);


(* STM instruction ------------------------------------------------------------- *)

val STM_STATE_def = Define `
  STM_STATE am4 x xs a s =
           <|registers :=
               INC_PC
                 (REG_WRITE s.registers (state_mode s) a
                    (addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))));
             psrs := s.psrs;
             memory :=
               FOLDL
                 (\mem (rp,rd).
                    MEM_WRITE_WORD mem rd
                      (REG_READ
                         (if HD (LEAST_SORT (MAP FST xs)) = a then
                            INC_PC s.registers
                          else
                            INC_PC
                              (REG_WRITE s.registers (state_mode s) a
                                 (addr32
                                    (ADDR_MODE4_WB am4 x (MAP FST xs)))))
                         (state_mode s) rp)) s.memory
                 (ZIP
                    (LEAST_SORT (MAP FST xs),
                     ADDR_MODE4_ADDRESSES am4 x (MAP FST xs)));
             undefined := F|>`;

val stm = simple_clean ARM_STM [``~(Rd = 15w:word4)``]
val stm = Q.INST [`opt`|->`ADDR_MODE4_CMD am4`] stm
val stm = Q.INST [`list`|->`reg_bitmap (MAP FST (xs:(word4 # word32) list))`] stm
val stm = Q.INST [`s_flag`|->`F`] stm
val stm = DISCH ``reg Rd s = addr32 p`` stm
val stm = DISCH ``ALL_DISTINCT (MAP FST (xs:(word4 # word32) list))`` stm
val stm = SIMP_RULE bool_ss [ADDR_MODE4_FORMAT,FST,SND,ADDR_MODE4_WB_THM] stm
val stm = REWRITE_RULE [GSYM STM_STATE_def] stm

val status_STM_STATE = prove(
  ``status (STM_STATE am4 x xs a s) = status s``,
  SRW_TAC [] [STM_STATE_def,status_def,statusN_def,statusZ_def,statusC_def,statusV_def]);

val undef_STM_STATE = prove(
  ``(STM_STATE am4 x xs a s).undefined = F``, SRW_TAC [] [STM_STATE_def]);

val owrt_visible_STM_STATE = prove(
  ``owrt_visible (STM_STATE am4 x xs a s) = owrt_visible s``,
  SRW_TAC [] [owrt_visible_def,STM_STATE_def,set_status_def,owrt_visible_regs_def,
              state_mode_simp,REG_OWRT_ALL]);

val reg_15_STM_STATE = prove(
  ``~(a = 15w) /\ (reg 15w s = addr32 p) ==> 
    (reg 15w (STM_STATE am4 x xs a s) = addr32 (pcADD 1w p))``,
  SIMP_TAC (srw_ss()) [STM_STATE_def,reg_def,INC_PC_r15,pcADD_def,
                       REG_WRITE_r15,GSYM addr32_SUC] \\ METIS_TAC [WORD_ADD_COMM]);

val reg_wb_STM_STATE = prove(
  ``~(a = 15w) ==> 
    (reg a (STM_STATE am4 x xs a s) = addr32 (ADDR_MODE4_WB am4 x xs))``,
  SIMP_TAC (srw_ss()) [STM_STATE_def,reg_def,state_mode_simp,REG_READ_INC_PC,
                       REG_READ_WRITE,ADDR_MODE4_WB_def,LENGTH_MAP]);

val reg_STM_STATE = prove(
  ``~(r = 15w) /\ ~(r = a) ==> (reg r (STM_STATE am4 x xs a s) = reg r s)``,
  SIMP_TAC (srw_ss()) [STM_STATE_def,reg_def,state_mode_simp,REG_READ_INC_PC,
                       REG_READ_WRITE_NEQ2,LENGTH_MAP]);

val xR_list_sem_STM_STATE = prove(
  ``xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) s /\
    ~MEM 15w (MAP FST xs) /\ ~MEM a (MAP FST xs) ==>
    (xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) (STM_STATE am4 x xs a s) = 
     xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) s)``,
  REWRITE_TAC [STM_STATE_def]
  \\ Q.SPEC_TAC (`FOLDL
      (\mem (rp,rd). MEM_WRITE_WORD mem rd (REG_READ
      (if HD (LEAST_SORT (MAP FST xs)) = a then INC_PC s.registers else
      INC_PC (REG_WRITE s.registers (state_mode s) a
      (addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))))) (state_mode s) rp)) s.memory
      (ZIP (LEAST_SORT (MAP FST xs), ADDR_MODE4_ADDRESSES am4 x (MAP FST xs)))`,`fff`)
  \\ Q.SPEC_TAC (`ADDR_MODE4_WB am4 x (MAP FST xs)`,`wbwb`)
  \\ Induct_on `xs` \\ SIMP_TAC std_ss [xR_list_sem_def,MAP]
  \\ Cases \\ Cases_on `q = 15w` \\ ASM_SIMP_TAC std_ss [MEM] 
  \\ ASM_SIMP_TAC (srw_ss()) [MEM,reg_def,state_mode_simp,
       REG_READ_INC_PC,REG_READ_WRITE_NEQ2]);

val DISJOINT_SING = prove(
  ``!p s. DISJOINT {p} s = ~(p IN s)``,
  SRW_TAC [] [DISJOINT_DEF,EXTENSION,IN_INTER,IN_INSERT,NOT_IN_EMPTY]);

val mem_STM_STATE = prove(
  ``ALL_DISTINCT (MAP FST xs) /\
    ~(p IN ms_address_set (ADDR_MODE4_ADDR am4 x xs) (LENGTH xs)) ==>
    (mem p (STM_STATE am4 x xs a s) = mem p s)``,
  REWRITE_TAC [STM_STATE_def,ADDR_MODE4_WB_def,LENGTH_MAP]
  \\ Q.SPEC_TAC (`HD (LEAST_SORT (MAP FST xs)) = a`,`rt`)
  \\ Q.SPEC_TAC (`(if ADDR_MODE4_wb am4 then ADDR_MODE4_WB' am4 x (LENGTH xs) else x)`,`rt'`)
  \\ REWRITE_TAC [GSYM ADDR_MODE4_WB_def,ADDR_MODE4_ADDRESSES_def]  
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP] 
  \\ ASM_REWRITE_TAC [ADDR_MODE4_ADDR_def]
  \\ REWRITE_TAC [GSYM ADDR_MODE4_ADDR_def]
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST xs)`,`ax`)
  \\ SIMP_TAC bool_ss [LEAST_SORT_EQ_QSORT,mem_def]
  \\ REWRITE_TAC [xR_list_sem_QSORT_INTRO,MEM_MAP_QSORT_INTRO,
                  ALL_DISTINCT_QSORT_INTRO,LENGTH_QSORT_INTRO]
  \\ Q.SPEC_TAC (`s.memory`,`mmm`)
  \\ SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`QSORT (\x y. FST x <=+ FST y) xs`,`xs`)
  \\ SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Induct \\ ASM_SIMP_TAC std_ss [LENGTH,ADDRESS_LIST'_def,MAP,ZIP,
       FOLDL,GSYM addr32_SUC,ALL_DISTINCT,ms_address_set_def,IN_INSERT]
  \\ SIMP_TAC std_ss [MEM_WRITE_WORD_def,SUBST_def,ADDR30_def,GSYM addr30_def,addr30_addr32]);

val ms_sem_STM_STATE_LEMMA = prove(
  ``!mmm bx f. 
      ~MEM (addr32 ax) (ADDRESS_LIST' (addr32 bx) (LENGTH xs)) ==> 
      (FOLDL
         (\mem (rp,rd). MEM_WRITE_WORD mem rd (f rp))
         (MEM_WRITE_WORD mmm (addr32 ax) r)
         (ZIP (MAP FST xs,ADDRESS_LIST' (addr32 bx) (LENGTH xs))) =
      MEM_WRITE_WORD
       (FOLDL
         (\mem (rp,rd). MEM_WRITE_WORD mem rd (f rp)) mmm
         (ZIP (MAP FST xs,ADDRESS_LIST' (addr32 bx) (LENGTH xs))))
     (addr32 ax) r)``,
  Induct_on `xs` 
  \\ SIMP_TAC std_ss [MAP,LENGTH,ADDRESS_LIST'_def,ZIP,FOLDL,MEM,GSYM addr32_SUC]
  \\ Cases \\ REPEAT STRIP_TAC
  \\ `!x. MEM_WRITE_WORD (MEM_WRITE_WORD mmm (addr32 ax) r) (addr32 bx) x = 
          MEM_WRITE_WORD (MEM_WRITE_WORD mmm (addr32 bx) x) (addr32 ax) r` by
        (SRW_TAC [] [MEM_WRITE_WORD_def,SUBST_def,FUN_EQ_THM,ADDR30_def,
           GSYM addr30_def,addr30_addr32] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [] \\ ASM_SIMP_TAC std_ss []);

val MEM_ADDRESS_LIST' = prove(
  ``!n a b. MEM (addr32 a) (ADDRESS_LIST' (addr32 b) n) = a IN ms_address_set b n``,
  Induct \\ ASM_REWRITE_TAC [ADDRESS_LIST'_def,MEM,ms_address_set_def,
     NOT_IN_EMPTY,IN_INSERT,GSYM addr32_SUC,addr32_11]);

val no_overlap_ADDRESS_LIST' = prove(
  ``!xs ax. LENGTH xs < 2**30 ==> 
            ~MEM (addr32 ax) (ADDRESS_LIST' (addr32 (ax+1w)) (LENGTH xs))``,
  SIMP_TAC bool_ss [MEM_ADDRESS_LIST',IN_ms_address_set]
  \\ REPEAT STRIP_TAC \\ Cases_on `k < LENGTH xs` \\ ASM_REWRITE_TAC []
  \\ `n2w k + (ax + 1w) = ax + n2w (k + 1)` by 
       METIS_TAC [word_add_n2w,WORD_ADD_COMM,WORD_ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_REWRITE_TAC [WORD_ADD_RID_UNIQ]  
  \\ `k + 1 < 2**30` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11]);
  
val ms_sem_STM_STATE = prove(
  ``LENGTH xs <= 2**30 /\
    ~MEM a (MAP FST xs) /\ ~MEM 15w (MAP FST xs) /\ ALL_DISTINCT (MAP FST xs) /\ 
    xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) s ==>
    ms_sem (ADDR_MODE4_ADDR am4 x xs) (reg_values xs) (STM_STATE am4 x xs a s)``,
  REWRITE_TAC [STM_STATE_def,ADDR_MODE4_WB_def,LENGTH_MAP]
  \\ Q.SPEC_TAC (`HD (LEAST_SORT (MAP FST xs)) = a`,`rt`)
  \\ Q.SPEC_TAC (`(if ADDR_MODE4_wb am4 then ADDR_MODE4_WB' am4 x (LENGTH xs) else x)`,`rt'`)
  \\ REWRITE_TAC [GSYM ADDR_MODE4_WB_def,ADDR_MODE4_ADDRESSES_def]  
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP] 
  \\ ASM_REWRITE_TAC [ADDR_MODE4_ADDR_def]
  \\ REWRITE_TAC [GSYM ADDR_MODE4_ADDR_def]
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST xs)`,`ax`)
  \\ SIMP_TAC bool_ss [LEAST_SORT_EQ_QSORT,mem_def]
  \\ REWRITE_TAC [xR_list_sem_QSORT_INTRO,MEM_MAP_QSORT_INTRO,
                  ALL_DISTINCT_QSORT_INTRO,LENGTH_QSORT_INTRO]
  \\ Q.SPEC_TAC (`s.memory`,`mmm`)
  \\ SIMP_TAC std_ss [reg_values_def] 
  \\ Q.SPEC_TAC (`QSORT (\x y. FST x <=+ FST y) xs`,`xs`)
  \\ SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Induct THEN1 REWRITE_TAC [ms_sem_def,MAP]
  \\ Cases \\ SIMP_TAC std_ss [MAP,HD,MEM,LENGTH,ADDRESS_LIST'_def,ZIP,FOLDL,
       ALL_DISTINCT,xR_list_sem_def,ms_sem_def,GSYM addr32_SUC] 
  \\ Cases_on `q = 15w` \\ ASM_REWRITE_TAC []
  \\ NTAC 5 STRIP_TAC \\ `LENGTH xs <= 1073741824` by DECIDE_TAC
  \\ `LENGTH xs < 1073741824` by DECIDE_TAC 
  \\ FULL_SIMP_TAC bool_ss [GSYM (EVAL ``2**30``)] 
  \\ `~MEM (addr32 ax) (ADDRESS_LIST' (addr32 (ax + 1w)) (LENGTH xs))` 
        by METIS_TAC [no_overlap_ADDRESS_LIST']
  \\ ASM_SIMP_TAC bool_ss [ms_sem_STM_STATE_LEMMA]
  \\ SIMP_TAC (srw_ss()) [mem_def,MEM_WRITE_WORD_def,ADDR30_def,
         GSYM addr30_def,addr30_addr32,SUBST_def]
  \\ `REG_READ s.registers (state_mode s) q = r` by METIS_TAC [reg_def]
  \\ Cases_on `rt` \\ FULL_SIMP_TAC std_ss [REG_READ_INC_PC,REG_READ_WRITE_NEQ2]);

val STM_PRE_EXPANSION = let
  val xs = `(15w,SOME x1)::(a,SOME x2)::xs`;
  val ys = `[(b1,xM_seq [y1]);(b3,xM_blank y3)]`;
  val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(T,g)`);
  val th = sep_pred_semantics (xs,ys,st,ud,rt,cd);
  in th end;

val STM_POST_EXPANSION = LDM_POST_EXPANSION;

val raw_STM = prove(
  ``ARM_PROG 
     (R30 a x * 
      xR_list (MAP (\x.(FST x,SOME (SND x))) xs) * 
      blank_ms (ADDR_MODE4_ADDR am4 x xs) (LENGTH xs) * S st * PASS c st) 
     [enc (STM c F (ADDR_MODE4_CMD am4) a (reg_bitmap (MAP FST xs)))] {}
     (R30 a (ADDR_MODE4_WB am4 x xs) *
      xR_list (MAP (\x.(FST x,SOME (SND x))) xs) *
      ms (ADDR_MODE4_ADDR am4 x xs) (reg_values xs) * S st) {}``,
  ARM_PROG_INIT_TAC 
  \\ ASM_MOVE_STAR_TAC `a*xs*mm*st*cd*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud*cd`
  \\ MOVE_STAR_TAC `a*xs*mm*st*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud`
  \\ FULL_SIMP_TAC bool_ss [R30_def,STM_PRE_EXPANSION,STM_POST_EXPANSION,DISJOINT_SING,
         LDM_SIMP_LEMMA,ALL_DISTINCT,MEM,LENGTH_reg_values,ALL_DISJOINT_def,EVERY_DEF]
  \\ `CONDITION_PASSED2 (status s) c` by METIS_TAC []
  \\ `mem (addr30 (reg 15w s)) s =
      enc (STM c F (ADDR_MODE4_CMD am4) a (reg_bitmap (MAP FST xs)))` 
         by METIS_TAC [addr30_addr32]
  \\ `~(a = 15w)` by METIS_TAC []
  \\ ASSUME_TAC ((UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o 
                  Q.INST [`p`|->`x`,`Rd`|->`a`]) stm)
  \\ ASM_REWRITE_TAC [] \\ PAT_ASSUM `` NEXT_ARM_MEM s = s'`` (fn th => ALL_TAC)
  \\ ASM_SIMP_TAC bool_ss [status_STM_STATE,undef_STM_STATE,reg_15_STM_STATE,
       reg_wb_STM_STATE,xR_list_sem_STM_STATE,mem_STM_STATE,ms_sem_STM_STATE]
  \\ ASM_SIMP_TAC bool_ss [arm2set''_EQ,owrt_visible_STM_STATE,IN_INSERT,
       reg_STM_STATE,mem_STM_STATE]);

val arm_STM = MAKE_PROG2 raw_STM ARM_STM_NOP;
val arm_STM = Q.INST [`c`|->`c_flag`,`st`|->`(sN,sZ,sC,Sv)`,`am4`|->`a_mode`] arm_STM;

val _ = save_thm("arm_STM",arm_STM);


val _ = export_theory();

