
(*
  val armDir = concat Globals.HOLDIR "/examples/elliptic/arm";
  val yaccDir = concat Globals.HOLDIR "/tools/mlyacc/mlyacclib";
  loadPath := !loadPath @ [armDir,yaccDir];
  quietdec := true;
*)

open HolKernel boolLib bossLib;

open pred_setTheory res_quanTheory wordsTheory arithmeticTheory;
open arm_rulesTheory arm_rulesLib arm_evalTheory armTheory instructionTheory; 
open bsubstTheory listTheory rich_listTheory;

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

val arm2set''_THM = prove(
  ``arm2set'' (rs,ns,st,ud,rt) s =
    {Reg a (reg a s) |a| ~(a IN rs)} UNION 
    {Mem a (mem a s) |a| ~(a IN ns)} UNION
    (if ~ st then {Status (status s)} else {}) UNION
    (if ~ ud then {Undef s.undefined} else {}) UNION
    (if ~ rt then {Rest (owrt_visible s)} else {})``,
  REWRITE_TAC [arm2set''_def,arm2set'_def,EXTENSION,arm2set_def]
  \\ FULL_SIMP_TAC bool_ss 
        [IN_UNION,IN_DIFF,IN_INSERT,NOT_IN_EMPTY,GSPECIFICATION,PAIR_EQ]
  \\ STRIP_TAC \\ EQ_TAC \\ STRIP_TAC << [
    METIS_TAC [],
    METIS_TAC [],
    Cases_on `st` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],
    Cases_on `ud` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],
    Cases_on `rt` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],
    `!k. ?a. x = Reg a (reg a s)` by METIS_TAC []
    \\ SRW_TAC [] [] \\ METIS_TAC [],    
    `!k. ?a. x = Mem a (mem a s)` by METIS_TAC []
    \\ SRW_TAC [] [] \\ METIS_TAC [],
    Cases_on `st` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] [],
    Cases_on `ud` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] [],    
    Cases_on `rt` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] []]);

val arm2set''_EQ = store_thm ("arm2set''_EQ", 
``!rs ns st ud rt s s'.
(arm2set'' (rs,ns,st,ud,rt) s = arm2set'' (rs,ns,st,ud,rt) s') = 
(
	(!r. (~(r IN rs)) ==> (arm_prog$reg r s = arm_prog$reg r s')) /\
	(!p. (~(p IN ns)) ==> (arm_prog$mem p s = arm_prog$mem p s')) /\
	((~st) ==> (status s = status s')) /\
	((~ud) ==> (s.undefined = s'.undefined)) /\
	((~rt) ==> (owrt_visible s = owrt_visible s'))
)``,

SIMP_TAC std_ss [arm2set''_THM, EXTENSION, IN_UNION, IN_DIFF, IN_INSERT, NOT_IN_EMPTY, GSPECIFICATION, prove (``x IN (if c then S1 else S2) =
												   if c then x IN S1 else x IN S2``, PROVE_TAC[])] THEN
REPEAT GEN_TAC THEN EQ_TAC THENL [
	REPEAT STRIP_TAC THEN (
		CCONTR_TAC THEN
		Q.PAT_ASSUM `!x. P x` MP_TAC THEN
		SIMP_TAC std_ss []) THENL [

		Q_TAC EXISTS_TAC `Reg r (arm_prog$reg r s)` THEN
		FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],

		Q_TAC EXISTS_TAC `Mem p (arm_prog$mem p s)` THEN
		FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],

		Q_TAC EXISTS_TAC `Status (status s)` THEN
		FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],

		Q_TAC EXISTS_TAC `Undef s.undefined` THEN
		FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],

		Q_TAC EXISTS_TAC `Rest (owrt_visible s)` THEN
		FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct]
	],
	
	SIMP_TAC std_ss [] THEN
	REPEAT STRIP_TAC THEN
	EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [ARMel_11, ARMel_distinct]
])

val REG_READ_WRITE_NEQ2 = prove(
  ``!n1 n2 r m1 m2 d. ~(n1 = n2) /\ ~(n2 = 15w) ==> 
      (REG_READ (REG_WRITE r m1 n1 d) m2 n2 = REG_READ r m2 n2)``,
  METIS_TAC [REG_READ6_def,REG_READ_WRITE_NEQ]);

val SHAPE_LEMMA_TAC = 
  EQ_TAC \\ STRIP_TAC \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [] [reg_def,state_mode_def,set_status_def]
  \\ CONV_TAC PSR_CONV
  \\ REWRITE_TAC [GSYM state_mode_def]
  \\ ASM_SIMP_TAC bool_ss [REG_READ_INC_PC,REG_READ_WRITE_NEQ2];

val SHAPE_LEMMA_TERM_FORMAT =
  ``(x = Reg a (reg a <|registers := rx; psrs := px; 
                        memory := v; undefined := v'|>)) /\ bx =
    (x = Reg a (reg a s)) /\ bx``;

fun MK_SHAPE_LEMMA_TERM (rx,bx) px =
  subst [``rx:registers``|-> rx,
         ``px:psrs``    |-> px,
         ``bx:bool``              |-> bx] SHAPE_LEMMA_TERM_FORMAT;

fun MK_SHAPE_LEMMA (rx,bx) px = prove(MK_SHAPE_LEMMA_TERM (rx,bx) px, SHAPE_LEMMA_TAC);

val n = ``s.psrs``;
val s = ``set_status (sN,sZ,sC,sV) s``;

val b = (``REG_WRITE s.registers usr 15w z``,``~(a = 15w:word4)``);
val br = (``REG_WRITE (REG_WRITE s.registers (state_mode s) R1 z') usr 15w z``,``~(a = 15w:word4) /\ ~(a = R1)``);
val rb = (``REG_WRITE (REG_WRITE s.registers usr 15w z') (state_mode s) R1 z``,``~(a = 15w:word4) /\ ~(a = R1)``);

val i = (``INC_PC s.registers``,``~(a = 15w:word4)``);
val ir = (``INC_PC (REG_WRITE s.registers (state_mode s) R1 z)``,``~(a = 15w:word4) /\ ~(a = R1)``);
val ri = (``REG_WRITE (INC_PC s.registers) (state_mode s) R1 z``,``~(a = 15w:word4) /\ ~(a = R1)``);
val irr = (``INC_PC (REG_WRITE (REG_WRITE s.registers (state_mode s) R1 z') (state_mode s) R2 z)``,``~(a = 15w:word4) /\ ~(a = R1) /\ ~(a = R2)``);
val rir = (``REG_WRITE (INC_PC (REG_WRITE s.registers (state_mode s) R1 z')) (state_mode s) R2 z``,``~(a = 15w:word4) /\ ~(a = R1) /\ ~(a = R2)``);
val rri = (``REG_WRITE (REG_WRITE (INC_PC s.registers) (state_mode s) R1 z') (state_mode s) R2 z``,``~(a = 15w:word4) /\ ~(a = R1) /\ ~(a = R2)``);

fun cross f [] ys = []
  | cross f (x::xs) ys = map (f x) ys @ cross f xs ys;

val SHAPE_REGISTER_LEMMAS = cross MK_SHAPE_LEMMA [b,rb,br,i,ir,ri,irr,rir,rri] [n,s]

val SHAPE_MEM_LEMMA = prove( 
  ``(x = Mem a (MEM_WRITE_WORD s.memory M2 q a)) /\ 
    ~(a = M1) /\ ~(a = addr30 M2) =
    (x = Mem a (mem a s)) /\ ~(a = M1) /\ ~(a = addr30 M2)``,
  REWRITE_TAC [MEM_WRITE_WORD_def,ADDR30_def,mem_def,GSYM addr30_def]
  \\ EQ_TAC \\ STRIP_TAC \\ ASM_REWRITE_TAC []    
  \\ ASM_SIMP_TAC bool_ss [SUBST_def]);

val SHAPE_LEMMAS = map (RW [CONJ_ASSOC]) (SHAPE_MEM_LEMMA::SHAPE_REGISTER_LEMMAS);

val DEFS = [owrt_visible_def,set_status_def,owrt_visible_regs_def,state_mode_def,
            status_def,statusN_def,statusZ_def,statusC_def,statusV_def,mem_def];

val EXPAND_DEFS_ss = rewrites DEFS
val CONTRACT_DEFS_ss = rewrites (map GSYM DEFS)

val SHAPE_TAC = 
  STRIP_TAC
  \\ REWRITE_TAC [arm2set''_THM]
  \\ SRW_TAC [] [EXTENSION]
  \\ SIMP_TAC (bool_ss++EXPAND_DEFS_ss) []
  \\ SRW_TAC [] []
  \\ CONV_TAC PSR_CONV
  \\ SIMP_TAC (bool_ss++CONTRACT_DEFS_ss) [REG_OWRT_ALL]
  \\ REWRITE_TAC [CONJ_ASSOC]
  \\ REWRITE_TAC SHAPE_LEMMAS;

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

val REG_WRITE_r15 = prove(
  ``!r m n d. ~(15w = n) ==> ((REG_WRITE r m n d) r15 = r r15)``,
  METIS_TAC [(RW [REG_READ6_def,FETCH_PC_def] o Q.INST [`n2`|->`15w`] o SPEC_ALL) 
             arm_evalTheory.REG_READ_WRITE_NEQ]);

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

val NOT_REG_SHIFT = prove(
  ``!Op2. ~IS_REG_SHIFT Op2 ==> (~IS_DP_IMMEDIATE Op2 /\
      ((11 >< 0) (addr_mode1_encode Op2)):word12 %% 4 = F)``,
  Cases \\ SRW_TAC []
    [IS_REG_SHIFT_def, IS_DP_IMMEDIATE_def, shift_immediate_shift_register]);

val shift_imm_SELECT4 = prove(
  ``!m. ((11 >< 0) (addr_mode1_encode (Dp_shift_immediate m 0w))):word12 %% 4 = F``,
  METIS_TAC [IS_DP_IMMEDIATE_def,shift_immediate_shift_register,NOT_REG_SHIFT]);

val ADDR_MODE1_ONE_REG_LEMMA =
  (REWRITE_CONV [IS_DP_IMMEDIATE_def] THENC 
   REWRITE_CONV [ADDR_MODE1_def,shift_immediate_enc] THENC
   SIMP_CONV (srw_ss()) [LSL_def,shift_imm_SELECT4])
    ``ADDR_MODE1 state.registers mode (cpsr %% 29)
       (IS_DP_IMMEDIATE (Dp_shift_immediate (LSL m) 0w))
         ((11 >< 0) (addr_mode1_encode (Dp_shift_immediate (LSL m) 0w)))``;

val ADDR_MODE1_ONE_IMM_LEMMA =
  (REWRITE_CONV [IS_DP_IMMEDIATE_def] THENC
   REWRITE_CONV [ADDR_MODE1_def,immediate_enc] THENC 
   SIMP_CONV (srw_ss()) [ROR_def,LSL_def] THENC
   RATOR_CONV EVAL THENC SIMP_CONV bool_ss [GSYM w2w_def])
     ``ADDR_MODE1 state.registers mode (cpsr %% 29)
         (IS_DP_IMMEDIATE (Dp_immediate 0w k))
            ((11 >< 0) (addr_mode1_encode (Dp_immediate 0w k)))``

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
  \\ REWRITE_TAC [ADDR_MODE1_ONE_REG_LEMMA,ADDR_MODE1_ONE_IMM_LEMMA]);

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
  (ADDR_MODE2_CMD1' (RegOff' (pre,up,wb,imm)) = <| Pre:=pre; Up:=up; BSN:=F; Wb:=wb |>)`;

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
  \\ SIMP_TAC bool_ss [REG_WRITE_def,REG_READ_def]
  \\ SRW_TAC [] [SUBST_def]);

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

val ADDR_MODE2_WORD_ONLY = prove(
  ``!c. (ADDR_MODE2_CMD1' c).BSN = F``,
  AM2'_Cases \\ SRW_TAC [] [ADDR_MODE2_CMD1'_def]);

(* address mode 2 aligned *)

val _ = Hol_datatype `
  abbrev_addr2 = RegOff of bool # bool # bool # word8`;

val MAKE_NONALIGNED_def = Define `
  (MAKE_NONALIGNED (RegOff (pre,up,wb,imm)) = RegOff' (pre,up,wb,w2w imm << 2))`;

val ADDR_MODE2_CMD1_def = Define `
  (ADDR_MODE2_CMD1 (RegOff (pre,up,wb,imm)) = <| Pre:=pre; Up:=up; BSN:=F; Wb:=wb |>)`;

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

val _ = save_thm("ARM_B_AL",ARM_UNCONDITIONAL_JUMP);

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

val _ = save_thm("ARM_B",ARM_CONDITIONAL_JUMP);


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

val _ = save_thm("ARM_CALL",ARM_UNCONDITIONAL_CALL);


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
  in save_thm("aMOV_PC",th) end;


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

val _ = store_thms "a" "1" MK_COMPARE1 cmps
val _ = store_thms "a" "2" MK_COMPARE2 cmps


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

val _ = store_thms "a" "1" MK_MONOP1 monops
val _ = store_thms "a" "2" MK_MONOP2 monops


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

val _ = store_thms "a" "1" MK_BINOP1 binops
val _ = store_thms "a" "2" MK_BINOP2 binops
val _ = store_thms "a" "2'" MK_BINOP2' binops
val _ = store_thms "a" "2''" MK_BINOP2'' binops
val _ = store_thms "a" "3" MK_BINOP3 binops


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

val _ = save_thm("aMUL3",MUL3);
val _ = save_thm("aMUL2",MUL2);
val _ = save_thm("aMUL2''",MUL2'');

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

val _ = save_thm("aMLA4",MLA4);
val _ = save_thm("aMLA3",MLA3);
val _ = save_thm("aMLA3'",MLA3');
val _ = save_thm("aMLA3''",MLA3'');


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

val _ = store_thms "a" "4" MK_MULL4 mulls
val _ = store_thms "a" "3" MK_MULL3 mulls
val _ = store_thms "a" "3'" MK_MULL3' mulls
val _ = store_thms "a" "3''" MK_MULL3'' mulls


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
  in save_thm("aSWP3_NONALIGNED",th) end;

val SWP3 = 
  let
    val th = Q.INST [`z`|->`addr32 z`] SWP3_NONALIGNED
    val th = RW [ADDRESS_ROTATE,addr30_addr32,GSYM R30_def] th    
  in save_thm("aSWP3",th) end;

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
  in save_thm("aSWP2_NONALIGNED",th) end;

val SWP2 = 
  let
    val th = Q.INST [`y`|->`addr32 y`] SWP2_NONALIGNED
    val th = RW [ADDRESS_ROTATE,addr30_addr32,GSYM R30_def] th    
  in save_thm("aSWP2",th) end;


(* ----------------------------------------------------------------------------- *)
(* LDR and STR INSTRUCTIONS                                                      *)
(* ----------------------------------------------------------------------------- *)

fun FIX_ADDR_MODE2 th = 
  let
    val th = SPEC_ALL th
    val th = DISCH_ALL (ASM_UNABBREV_ALL_RULE (UD_ALL th))
    val th = RW [GSYM state_mode_def] th
    val th = Q.GEN `opt` (Q.GEN `offset` th)
    val th = Q.ISPEC `ADDR_MODE2_CMD1' a_mode` th
    val th = Q.ISPEC `ADDR_MODE2_CMD2' a_mode` th
    val th = RW [ADDR_MODE2_WORD_ONLY] th
    val th = SIMP_RULE bool_ss [ADDR_MODE2_WB'_THM,ADDR_MODE2_ADDR'_THM] th
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
  in save_thm("aSTR_NONALIGNED",th) end;

val STR = save_thm("aSTR",AM2_ALIGN_ADDRESSES `y` STR_NONALIGNED);

val LDR_NONALIGNED =
  let
    val (th,nop) = FIX_ADDR_MODE2_PAIR (ARM_LDR,ARM_LDR_NOP)
    val rs = [``Rn:word4``,``Rd:word4``]
    val (conds,shape,prog) = (c32TTF,Srir32TTF,P3_STR)
    val insts = [``M2:word32``|->``(ADDR_MODE2_ADDR' a_mode x1):word32``]
    val i = STR_INST
    val th = MK_PROG2 (conds,shape,insts,prog) rs (th,nop) i
  in save_thm("aLDR_NONALIGNED",th) end;

val LDR = save_thm("aLDR",AM2_ALIGN_ADDRESSES `y` LDR_NONALIGNED);

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
  in save_thm("aLDR1_NONALIGNED",th) end;

val LDR1 = save_thm("aLDR1",AM2_ALIGN_ADDRESSES `y` LDR1_NONALIGNED);

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
  in save_thm("aLDR_PC",th) end;


(* ----------------------------------------------------------------------------- *)
(* LDM and STM INSTRUCTIONS                                                      *)
(* ----------------------------------------------------------------------------- *)

(*

(* quick sort *)

val total_def = Define `total f = !x y. f x y \/ f y x`;
val transitive_def = Define `transitive f = !x y z. f x y /\ f y z ==> f x z`;

val SORTED_def = Define `
  (SORTED f  [] = T) /\  
  (SORTED f [x] = T) /\  
  (SORTED f (x::y::xs) = f x y /\ SORTED f (y::xs))`;

val PERM_def = Define `PERM xs ys = !x. FILTER ($= x) xs = FILTER ($= x) ys`;

val PERM_refl = prove(``!xs. PERM xs xs``,METIS_TAC[PERM_def]);

val LENGTH_FILTER_LESS = prove( 
  ``!xs. LENGTH (FILTER g xs) < SUC (LENGTH xs)``,
  Induct_on `xs`  
  \\ SRW_TAC [] [LENGTH,FILTER]
  \\ METIS_TAC [DECIDE ``!x. x < SUC x``,LESS_TRANS]);

val QSORT_defn = Hol_defn "QSORT" `
  (QSORT f [] = []) /\
  (QSORT f (x::xs) = QSORT f (FILTER ($~ o f x) xs) ++ [x] ++
                     QSORT f (FILTER (f x) xs))`;

val (QSORT_def,QSORT_ind) = Defn.tprove(QSORT_defn,
  WF_REL_TAC `measure (LENGTH o SND)`
  \\ METIS_TAC [LENGTH_FILTER_LESS,LENGTH]);

val QSORT_MEM_stable = prove(
  ``!f xs x. MEM x (QSORT f xs) = MEM x xs``,
  recInduct QSORT_ind 
  \\ SIMP_TAC list_ss [QSORT_def,MEM_APPEND,MEM,MEM_FILTER]
  \\ METIS_TAC []);

val SORTED_eq = prove(
  ``!f xs x. transitive f
         ==> (SORTED f (x::xs) = SORTED f xs /\ !y. MEM y xs ==> f x y)``,
  Induct_on `xs`
  \\ SRW_TAC [] [SORTED_def,MEM]
  \\ METIS_TAC [transitive_def]);

val QSORT_perm = prove(
  ``!f xs. PERM xs (QSORT f xs)``,
  recInduct QSORT_ind
  \\ SIMP_TAC list_ss [QSORT_def,PERM_refl,APPEND] 
  \\ REPEAT STRIP_TAC
  THEN MATCH_MP_TAC CONS_PERM
  THEN MATCH_MP_TAC PERM_trans1
  THEN Q.EXISTS_TAC`APPEND (FILTER(\x. r x h) t) (FILTER(\x. ~r x h) t)`
  THEN RW_TAC std_ss [BETA_RULE(REWRITE_RULE[o_DEF] PERM_split),PERM_cong]);

val SORTED_APPEND = prove(
  ``!f xs ys.
     transitive f /\ SORTED f xs /\ SORTED f ys /\ 
     (!x y. MEM x xs /\ MEM y ys ==> f x y) ==>
     SORTED f (APPEND xs ys)``,
  Induct_on `xs`
  \\ SIMP_TAC list_ss [MEM] \\ REPEAT STRIP_TAC
  \\ `SORTED f xs /\ !y. MEM y xs ==> f h y` by PROVE_TAC [SORTED_eq]
  \\ ASM_SIMP_TAC bool_ss [SORTED_eq] \\ REPEAT STRIP_TAC
  \\ `MEM y xs \/ MEM y ys` by METIS_TAC [MEM_APPEND]
  \\ METIS_TAC []);

val QSORT_sorts = prove(
  ``!f xs. transitive f /\ total f ==> SORTED f (QSORT f xs)``,
  recInduct QSORT_ind
  \\ SIMP_TAC list_ss [QSORT_def,SORTED_def]
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [GSYM APPEND_ASSOC]
  \\ REWRITE_TAC [APPEND]
  \\ MATCH_MP_TAC SORTED_APPEND
  \\ IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th]) SORTED_eq
  \\ SIMP_TAC list_ss [MEM_FILTER,MEM,QSORT_MEM_stable]
  \\ METIS_TAC [transitive_def,total_def]);

(* do something better... use Slind's stuff literally *)

val SORTED_LESS = prove(
  ``!xs:('a word) list. SORTED $<= xs /\ ALL_DISTINCT xs ==> SORTED $< xs``,
  Induct
  \\ SRW_TAC [] [ALL_DISTINCT,SORTED_def]
  \\ Cases_on `xs`
  \\ SRW_TAC [] [ALL_DISTINCT,SORTED_def]
  \\ `~(h = h') /\ (h <= h')` by METIS_TAC [SORTED_def,MEM]
  \\ METIS_TAC [WORD_LESS_OR_EQ,SORTED_def]);

  ``!xs:('a word) list. ALL_DISTINCT xs ==> SORTED $< (QSORT $<= xs)``
  REPEAT STRIP_TAC
  MATCH_MP_TAC SORTED_LESS

ALL_DISTINCT
word_le_def

(* still to come, honestly *)

val ALL_DISTINCT_def = Define `
  (ALL_DISTINCT [] = T) /\ 
  (ALL_DISTINCT (x::xs) = ~(MEM x xs) /\ ALL_DISTINCT xs)`;

val GEN_REGLIST_def = Define `
  GEN_REGLIST (xs:word4 list) = (FCP i. MEM (n2w i) xs):word16`;

val w2n_lt_16 = 
  SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] (Q.INST_TYPE [`:'a`|->`:i4`] w2n_lt);

val w2n_FCP_BETA = 
  let
    val th' = Q.INST_TYPE [`:'a`|->`:i4`] w2n_lt
    val th' = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] th'
    val th = Q.SPEC `w2n (x:word4)` fcpTheory.FCP_BETA
    val th = Q.INST_TYPE [`:'b`|->`:i16`] th
    val th = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] th
  in
    MP th (Q.SPEC `x` th')
  end;

val GEN_REGLIST_MEM = prove(
  ``!x xs. MEM x xs = GEN_REGLIST xs %% w2n x``,
  SIMP_TAC std_ss [GEN_REGLIST_def,w2n_FCP_BETA,n2w_w2n]);

val MEM_EQ_LEMMA = prove(
  ``!x xs. MEM x ((MAP SND o FILTER FST) xs) = MEM (T,x) xs``,        
  Induct_on `xs`
  THEN1 SRW_TAC [] [] 
  \\ Cases_on `h`
  \\ Cases_on `q`
  \\ FULL_SIMP_TAC std_ss [FILTER,MAP,MEM]);

val MEM_EQ_LEMMA2 = prove(
  ``!xs x y. MEM x (SNOC y xs) = MEM x (CONS y xs)``,
  Induct_on `xs` \\ SRW_TAC [] [MEM,SNOC] \\ METIS_TAC []);

val MEM_EQ_LEMMA3 = prove(
  ``!n x f g. 
       MEM (T,x) (GENLIST (\i. (f i, g i)) n) = ?i. i < n /\ f i /\ (x = g i)``,
  Induct
  THEN1 SIMP_TAC std_ss [MEM,GENLIST]
  \\ SRW_TAC [] [MEM,GENLIST,MEM_EQ_LEMMA2]
  \\ Cases_on `f n /\ (x = g n)`
  \\ ASM_REWRITE_TAC []
  THEN1 (Q.EXISTS_TAC `n` \\ SRW_TAC [] [])
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `i` 
    \\ METIS_TAC [LESS_TRANS,LESS_EQ_IMP_LESS_SUC,LESS_EQ_REFL],
    Cases_on `i = n` THEN1 METIS_TAC []
    \\ `i < n` by DECIDE_TAC \\ METIS_TAC []]);

val MEM_EQ_REGISTER_LIST_GEN_REGLIST = prove(
  ``!x xs. MEM x xs = MEM x (REGISTER_LIST (GEN_REGLIST xs))``,  
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [REGISTER_LIST_def,MEM_EQ_LEMMA]
  \\ REWRITE_TAC [GEN_REGLIST_MEM]
  \\ REWRITE_TAC [MEM_EQ_LEMMA3]
  \\ EQ_TAC \\ STRIP_TAC
  THEN1 (Q.EXISTS_TAC `w2n (x:word4)` \\ SRW_TAC [] [n2w_w2n,w2n_lt_16])
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2n_n2w]);

val MEM_IMP_SPLIT = prove(   
  ``!ys y. MEM y ys ==> ?zs zs'. ys = zs ++ [y] ++ zs'``,
  Induct 
  THEN1 SRW_TAC [] []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `y = h` << [
    Q.EXISTS_TAC `[]` 
    \\ Q.EXISTS_TAC `ys` 
    \\ ASM_SIMP_TAC std_ss [APPEND],
    FULL_SIMP_TAC std_ss [MEM]
    \\ `?zs zs'. ys = zs ++ [y] ++ zs'` by METIS_TAC []
    \\ Q.EXISTS_TAC `h::zs`
    \\ Q.EXISTS_TAC `zs'`
    \\ ASM_SIMP_TAC std_ss [APPEND]]);

val rs_def = Define `
  (rs [] = emp) /\ 
  (rs ((r,x)::xs) = R r x * rs xs)`;

val rs'_def = Define `
  (rs' [] = emp) /\ 
  (rs' ((r,x)::xs) = ~ (R r) * rs' xs)`;

val ms_def = Define `
  (ms a [] = emp) /\
  (ms a (x::xs) = M (addr30 a) x * ms (a+4w:word32) xs)`;

val ms'_def = Define `
  (ms' a [] = emp) /\
  (ms' a (x::xs) = ~ (M (addr30 a)) * ms' (a+4w:word32) xs)`;

val LENGTH_FILTER_LESS = prove( 
  ``!xs. LENGTH (FILTER g xs) < SUC (LENGTH xs)``,
  Induct_on `xs`  
  \\ SRW_TAC [] [LENGTH,FILTER]
  \\ METIS_TAC [DECIDE ``!x. x < SUC x``,LESS_TRANS]);

val QSORT_defn = Hol_defn "QSORT" `
  (QSORT f [] = []) /\
  (QSORT f (x::xs) = QSORT f (FILTER ($~ o f x) xs) ++ [x] ++
                     QSORT f (FILTER (f x) xs))`;

val (QSORT_def,QSORT_ind) = Defn.tprove(QSORT_defn,
  WF_REL_TAC `measure (LENGTH o SND)`
  \\ METIS_TAC [LENGTH_FILTER_LESS,LENGTH]);

val SORTED_def = Define `
  SORTED f xs = !ys y z zs. (xs = ys ++ [y;z] ++ zs) ==> f y z`;

val SORTED_QSORT_LEMMA = prove(
 ``!xs g. ALL_DISTINCT xs ==> ALL_DISTINCT (FILTER g xs)``,
  Induct \\ SRW_TAC [] [ALL_DISTINCT_def]
  \\ `~MEM h xs ==> ~MEM h (FILTER g xs)` by ALL_TAC << [
    POP_ASSUM_LIST (fn thms => ALL_TAC)
    \\ Induct_on `xs` \\ SRW_TAC [] [MEM,FILTER],
    METIS_TAC []]);

val MEM_FILTER_IMP = prove(
  ``!xs x g. MEM x (FILTER g xs) ==> MEM x xs``,
  Induct \\ SRW_TAC [] [] \\ METIS_TAC []);

val SAME_PREFIX = prove(
  ``!xs ys zs zs'. (LENGTH xs = LENGTH ys) /\ (xs ++ zs = ys ++ zs') ==> (xs = ys)``,
  Induct THEN1 METIS_TAC [LENGTH_NIL,LENGTH]
  \\ SRW_TAC [] [LENGTH]
  \\ `?h' ys'. (LENGTH xs = LENGTH ys') /\ (ys = h'::ys')` by METIS_TAC [LENGTH_CONS]
  \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11]
  \\ METIS_TAC []);

  ``!xs:'a word list h ys. 
      SORTED $< xs /\ SORTED $< ys /\ 
      (!x. MEM x xs ==> x < h) /\ (!y. MEM y ys ==> h < y) ==> 
      SORTED $< (xs ++ [h] ++ ys)``,
  REWRITE_TAC [SORTED_def]
  REPEAT STRIP_TAC
  Cases_on `LENGTH xs = LENGTH ys'`

    `xs = ys'` by METIS_TAC [SAME_PREFIX,APPEND_ASSOC]
    \\ FULL_SIMP_TAC std_ss [APPEND_11,GSYM APPEND_ASSOC]
    \\ Cases_on `ys`
    \\ FULL_SIMP_TAC bool_ss [APPEND]    

      open listTheory;
    

val SORTED_QSORT = prove(
  ``!xs:'a word list. 
       ALL_DISTINCT xs ==> 
       SORTED $< (QSORT $< xs) /\ (!x. MEM x xs = MEM x (QSORT $< xs))``,
  STRIP_TAC \\ completeInduct_on `LENGTH xs` \\ Cases_on `v`

    REPEAT STRIP_TAC
    \\ `xs = []` by METIS_TAC [LENGTH_NIL]
    \\ SRW_TAC [] [QSORT_def,SORTED_def]

    NTAC 3 STRIP_TAC
    \\ `?h xs'. (LENGTH xs' = n) /\ (xs = h::xs')` by METIS_TAC [LENGTH_CONS]
    \\ ASM_REWRITE_TAC [QSORT_def]
    \\ `LENGTH (FILTER ($~ o $< h) xs') < SUC n` by METIS_TAC [LENGTH_FILTER_LESS] 
    \\ `LENGTH (FILTER ($< h) xs') < SUC n` by METIS_TAC [LENGTH_FILTER_LESS]    
    \\ `ALL_DISTINCT xs'` by METIS_TAC [ALL_DISTINCT_def]
    \\ `ALL_DISTINCT (FILTER ($~ o $< h) xs')` by METIS_TAC [SORTED_QSORT_LEMMA]
    \\ `ALL_DISTINCT (FILTER ($< h) xs')` by METIS_TAC [SORTED_QSORT_LEMMA]
    \\ STRIP_TAC
      
      `SORTED $< (QSORT $< (FILTER ($~ o $< h) xs'))` by METIS_TAC []
      \\ `SORTED $< (QSORT $< (FILTER ($< h) xs'))` by METIS_TAC []
      
      REWRITE_TAC [MEM_APPEND,MEM] 
      \\ REPEAT STRIP_TAC 
      \\ EQ_TAC << [
        STRIP_TAC \\ Cases_on `x = h` \\ ASM_REWRITE_TAC []      
        THEN1 METIS_TAC []      
        \\ `(($< h) x) \/ (($~ o $< h) x)` by SRW_TAC [] []      
        \\ METIS_TAC [MEM_FILTER],
        METIS_TAC [MEM_FILTER_IMP]]
        
        

val REGSORT_def = Define `
  (REGSORT:(word4#word32) list->(word4#word32) list) = QSORT (\x y. FST x < FST y)`;

val MBLOCK_WB_def = Define `
  MBLOCK_WB wb U base xs = 
    if wb then WB_ADDRESS U base (LENGTH xs) else base`;

val MBLOCK_ADDR_def = Define `
  MBLOCK_ADDR P U base xs = 
    FIRST_ADDRESS P U base (MBLOCK_WB T U base xs)`;

val MBLOCK_def = Define `
  MBLOCK P U base xs = ms (MBLOCK_ADDR P U base xs) (MAP SND (REGSORT xs))`;


val MAP_FST_REGSORT_LEMMA = prove(
  ``!xs f h. FILTER f (MAP FST xs) = MAP FST (FILTER (\y. f (FST y)) xs)``,
  Induct 
  \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss []);

val MAP_FST_REGSORT = prove(
  ``!xs. MAP FST (REGSORT xs) = QSORT ($<) (MAP FST xs)``,
  STRIP_TAC
  \\ completeInduct_on `LENGTH xs`
  \\ Cases_on `v`
  \\ REPEAT STRIP_TAC << [    
    `xs = []` by METIS_TAC [LENGTH_NIL]
    \\ ASM_SIMP_TAC std_ss [REGSORT_def,MAP,QSORT_def],
    `?h xs'. (LENGTH xs' = n) /\ (xs = h::xs')` by METIS_TAC [LENGTH_CONS]
    \\ ASM_REWRITE_TAC [QSORT_def,REGSORT_def]
    \\ Cases_on `h`
    \\ FULL_SIMP_TAC bool_ss [REGSORT_def,MAP_APPEND,MAP,QSORT_def]
    \\ REWRITE_TAC [MAP_FST_REGSORT_LEMMA]
    \\ FULL_SIMP_TAC std_ss []
    \\ `LENGTH (FILTER (\y. ~(q < FST y)) xs') < SUC n` by METIS_TAC [LENGTH_FILTER_LESS] 
    \\ `LENGTH (FILTER (\y. q < FST y) xs') < SUC n` by METIS_TAC [LENGTH_FILTER_LESS]    
    \\ METIS_TAC []]);


(*

  ``!ys xs h. 
      ALL_DISTINCT xs /\ ALL_DISTINCT ys /\ 
      SORTED f xs /\ SORTED f ys /\ (!x. MEM x xs ==> f x h) ==> 
      SORTED f (ISORT_INSERT f h xs ys)``
  Induct

    REWRITE_TAC [ISORT_INSERT_def]
    \\ REWRITE_TAC [SORTED_def]
    \\ REPEAT STRIP_TAC        
    \\ Cases_on `zs`    


val SORTED_ISORT' = prove(
  ``!f xs ys. ALL_DISTINCT xs /\ SORTED f ys ==> SORTED f (ISORT' f xs ys)``,
  Induct_on `xs`
  THEN1 SRW_TAC [] [ISORT'_def]

  ``!f xs. ALL_DISTINCT xs ==> SORTED f (ISORT f xs)``
  STRIP_TAC
  \\ REWRITE_TAC [ISORT_def]
  \\ `!xs ys. ALL_DISTINCT xs /\ SORTED f ys ==> SORTED f (ISORT' f xs ys)` by ALL_TAC

    Induct THEN1 SRW_TAC [] [ISORT'_def]
    `!ys xs h. 
       SORTED f xs /\ SORTED f ys /\ (!x. MEM x xs ==> f x h) ==> 
       SORTED f (ISORT_INSERT f h xs ys)` by ALL_TAC

      Induct 

        REWRITE_TAC [ISORT_INSERT_def]
        REPEAT STRIP_TAC        
        REWRITE_TAC [SORTED_def]

*)


val SORTED_TRANS = prove(
  ``!xs f h h' ys.
      (!x y z. f x y /\ f y z ==> f x z) /\ 
      SORTED f (h::xs ++ [h'] ++ ys) ==> f h h'``,
  Induct THEN1 METIS_TAC [SORTED_def,APPEND]
  \\ REPEAT STRIP_TAC
  \\ `h'::h::xs ++ [h''] ++ ys = [] ++ [h';h]++ (xs ++ [h''] ++ ys)` by METIS_TAC [APPEND]
  \\ `f h' h` by METIS_TAC [SORTED_def]
  \\ `!x xs. SORTED f (x::xs) ==> SORTED f xs` by METIS_TAC [SORTED_def,APPEND]
  \\ METIS_TAC [APPEND]);

val SORTED_IMP_EQ = prove(
  ``!f xs ys.
      (!x y z. f x y /\ f y z ==> f x z) /\ (!x y. ~(f x y /\ f y x)) /\ 
      SORTED f xs /\ SORTED f ys /\
      (!x. MEM x xs = MEM x ys) ==> (xs = ys)``,
  STRIP_TAC
  \\ Induct 
  THEN1 METIS_TAC [MEM]
  \\ REPEAT STRIP_TAC  
  \\ `MEM h ys` by METIS_TAC []
  \\ `?zs zs'. ys = zs ++ [h] ++ zs'` by METIS_TAC [MEM_IMP_SPLIT]
  \\ Cases_on `zs` << [
    ASM_REWRITE_TAC [APPEND]
    \\ `!x xs. SORTED f (x::xs) ==> SORTED f xs` by METIS_TAC [SORTED_def,APPEND]
    \\ METIS_TAC [],
    `MEM h' (h::xs)` by METIS_TAC [MEM]
    \\ Cases_on `h = h'` THEN1 METIS_TAC [ALL_DISTINCT_def,MEM]
    \\ `MEM h' xs` by METIS_TAC [MEM]
    \\ `?zs1 zs1'. xs = zs1 ++ [h'] ++ zs1'` by METIS_TAC [MEM_IMP_SPLIT]
    \\ `f h h'` by METIS_TAC [SORTED_TRANS]
    \\ `f h' h` by METIS_TAC [SORTED_TRANS]
    \\ METIS_TAC []]);


  ``ALL_DISTINCT (MAP FST ys) ==>
    (FST (ADDR_MODE4 P U x (GEN_REGLIST (MAP FST ys))) = MAP FST (REGSORT ys))``
  SIMP_TAC std_ss [ADDR_MODE4_def,LET_DEF]
  \\ REWRITE_TAC [MAP_FST_REGSORT]
  \\ Q.ABBREV_TAC `x = MAP FST ys`  

  WORD_LESS_TRANS
  WORD_LESS_ANTISYM

  Q.SPEC `$<:word4->word4->bool` (Q.INST_TYPE [`:'a`|->`:word4`] SORTED_IMP_EQ)

  MEM_EQ_REGISTER_LIST_GEN_REGLIST
  Q.ISPEC `$<:word4->word4->bool` SORTED_QSORT

show_types := false
show_types_verbosely := false

(*

  target specs, sketches only:

  STM pre:    R a x * rs ys * MBLOCK' P U x ys * cond ~(ys = [])
  STM post:   R a (MBLOCK_WB wb U x ys) * rs ys * MBLOCK P U x ys

  LDM pre:    R a x * rs' ys * MBLOCK P U x ys * cond ~(ys = [])
  LDM post:   R a (MBLOCK_WB wb U x ys) * rs ys * MBLOCK P U x ys

*)


ADDR_MODE4_def
REGISTER_LIST_def
WB_ADDRESS_def
FIRST_ADDRESS_def
ADDRESS_LIST_def
GENLIST

    val th = ARM_LDM
    val th = SPEC_ALL th
    val th = DISCH_ALL (ASM_UNABBREV_ALL_RULE (UD_ALL th))
    val th = RW [GSYM state_mode_def] th
    val th = Q.INST [`opt`|->`<| Pre:=P; Up:=U; BSN:=F; Wb:=wb |>`] th
    val th = DISCH ``~(Rd:word4 = 15w)`` th
    val th = SIMP_RULE (srw_ss()) [] th
    val th = Q.INST [`list`|->`GEN_REGLIST (MAP FST ys)`] th

    val th = Q.INST [`list`|->`3w:word16`] th

*)

val _ = export_theory();

