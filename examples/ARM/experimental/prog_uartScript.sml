
open HolKernel boolLib bossLib Parse;
open decompilerLib;

open pred_setTheory wordsTheory wordsLib arithmeticTheory;
open set_sepTheory progTheory toy_systemTheory;
open listTheory pairTheory combinTheory addressTheory;
open helperLib;

open toy_systemTheory toy_uartTheory prog_toyTheory prog_toyLib;
open toy_coreTheory;


val _ = new_theory "prog_uart";
val _ = map Parse.hide ["r1","r2","r3"];

infix \\ val op \\ = op THEN;


(* -------------------------------------------------------------------------- *)
(*  Prove SPEC theorems for accessing UART0 state                             *)
(* -------------------------------------------------------------------------- *)

val tUART0_IO_def = Define `
  tUART0_IO (inl,outl) = SEP_EXISTS int outt. tUART0 (inl,int,outl,outt)`;

val SEP_EXISTS_THM = prove(
  ``!p s. (SEP_EXISTS x. p x) s = ?x. p x s``,
  SIMP_TAC std_ss [SEP_EXISTS]);

val SPEC_UART0_READ_LEMMA = prove(
  ``uart0_ok t s /\ (s.input_list = w::inl) /\
    int <= t /\ (s.input_time = int) ==> s.U0LSR ' 0``,
  SIMP_TAC std_ss [uart0_ok_def,NOT_CONS_NIL]);

val SPEC_UART0_READ = prove(
  ``SPEC TOY_MODEL 
      (tR a 0xE000C000w * tUART0 (inl,int,outl,outt) * tPC p * tT t * cond (int <= t /\ ~(inl = []))) 
      {(p,iLDR a (a,0w))} 
      (tR a (w2w (HD inl)) * tUART0_IO (TL inl,outl) * tPC (p + 4w) * tT (t + 1))``,
  Cases_on `inl` 
  \\ SIMP_TAC std_ss [progTheory.SPEC_MOVE_COND,HD,TL] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC IMP_TOY_SPEC
  \\ SIMP_TAC std_ss [tUART0_IO_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ SIMP_TAC std_ss [pairTheory.FORALL_PROD,pairTheory.EXISTS_PROD]
  \\ SIMP_TAC std_ss [STAR_toy2set,GSYM STAR_ASSOC,tPC_def,
         pred_setTheory.IN_DELETE,cond_STAR,TOY_NEXT_def,CODE_POOL_toy2set]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [TOY_READ_REG_def,NEXT_def,TOY_READ_INSTR_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [NEXT_INST_def,LET_DEF,ATTACH_MEMORY_ACCESS_def,INC_PC_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,TOY_READ_UNDEF_def]
  \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [PERIPHERALS_OK_def,ALL_PERIPHERALS_def,UART0_DEVICE_def,
      COMPOSE_DEVICES_def,ROM_DEVICE_def,RAM_DEVICE_def,EMPTY_DEVICE_def,
      pairTheory.FORALL_PROD,LET_DEF,PERIPHERALS_NEXT_def,FILTER_ACCESSES_def,
      listTheory.FILTER,ROM_NEXT_def,RAM_NEXT_def,UPDATE_RAM_def,
      pairTheory.EXISTS_PROD,ACCESS_ADDRESS_def,IN_UNION,IN_DIFF,UART0_addresses_def,
      WORD_ADD_0,IN_INSERT,IN_DISJOINT,NOT_IN_EMPTY,TOY_READ_TIME_def]
    \\ FULL_SIMP_TAC std_ss [TOY_READ_UART0_def,UART0_READ_def]
    \\ IMP_RES_TAC SPEC_UART0_READ_LEMMA    
    \\ IMP_RES_TAC UART0_READ
    \\ Q.EXISTS_TAC `s2` \\ ASM_SIMP_TAC std_ss []
    \\ METIS_TAC [FILTER])
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [TOY_READ_TIME_def]
  \\ FULL_SIMP_TAC std_ss [PERIPHERALS_OK_def,ALL_PERIPHERALS_def,UART0_DEVICE_def,
      COMPOSE_DEVICES_def,ROM_DEVICE_def,RAM_DEVICE_def,EMPTY_DEVICE_def,
      pairTheory.FORALL_PROD,LET_DEF,PERIPHERALS_NEXT_def,FILTER_ACCESSES_def,
      listTheory.FILTER,ROM_NEXT_def,RAM_NEXT_def,UPDATE_RAM_def,INIT_MEMORY_def,
      pairTheory.EXISTS_PROD,ACCESS_ADDRESS_def,IN_UNION,IN_DIFF,UART0_addresses_def,
      WORD_ADD_0,IN_INSERT,IN_DISJOINT,NOT_IN_EMPTY,TOY_READ_TIME_def]
  \\ FULL_SIMP_TAC std_ss [TOY_READ_UART0_def,UART0_READ_def,UART0_read_def]
  \\ `~(0xE000C000w IN domain p_1''')` by METIS_TAC [] 
  \\ `~(0xE000C000w IN domain p_1'''')` by METIS_TAC [] 
  \\ FULL_SIMP_TAC std_ss [UPDATE_RAM_def,UART0_NEXT_def]
  \\ FULL_SIMP_TAC std_ss [uart0_ok_def,MEM,HD,TL,memory_access_distinct]
  \\ REPEAT STRIP_TAC  
  \\ FULL_SIMP_TAC std_ss [toy2set''_thm,TOY_READ_UNDEF_def,IN_DELETE,FILTER,
         oneTheory.one,IN_INSERT,NOT_IN_EMPTY,TOY_READ_REG_def,TOY_READ_UART0_def,
         TOY_READ_STATUS_def,APPLY_UPDATE_THM,TOY_READ_INSTR_def,TOY_READ_RAM_def,
         UART0_NEXT_NIL,ACCESS_ADDRESS_def,IN_UNION,WORD_ADD_0,UART0_addresses_def]
  \\ METIS_TAC []);

val SPEC_UART0_WRITE_LEMMA = prove(
  ``uart0_ok t s /\ outt <= t /\ (s.output_time = outt) ==> s.U0LSR ' 5``,
  SIMP_TAC std_ss [uart0_ok_def,NOT_CONS_NIL]);

val SPEC_UART0_WRITE = prove(
  ``SPEC TOY_MODEL 
      (tR a 0xE000C000w * tR b w * tUART0 (inl,int,outl,outt) * tPC p * tT t * cond (outt <= t)) 
      {(p,iSTR b (a,0w))} 
      (tR a 0xE000C000w * tR b w * tUART0_IO (inl,w2w w::outl) * tPC (p + 4w) * tT (t + 1))``,
  SIMP_TAC std_ss [progTheory.SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC IMP_TOY_SPEC
  \\ SIMP_TAC std_ss [tUART0_IO_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ SIMP_TAC std_ss [pairTheory.FORALL_PROD,pairTheory.EXISTS_PROD]
  \\ SIMP_TAC std_ss [STAR_toy2set,GSYM STAR_ASSOC,tPC_def,
         pred_setTheory.IN_DELETE,cond_STAR,TOY_NEXT_def,CODE_POOL_toy2set]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [TOY_READ_REG_def,NEXT_def,TOY_READ_INSTR_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [NEXT_INST_def,LET_DEF,ATTACH_MEMORY_ACCESS_def,INC_PC_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,TOY_READ_UNDEF_def]
  \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [PERIPHERALS_OK_def,ALL_PERIPHERALS_def,UART0_DEVICE_def,
      COMPOSE_DEVICES_def,ROM_DEVICE_def,RAM_DEVICE_def,EMPTY_DEVICE_def,
      pairTheory.FORALL_PROD,LET_DEF,PERIPHERALS_NEXT_def,FILTER_ACCESSES_def,
      listTheory.FILTER,ROM_NEXT_def,RAM_NEXT_def,UPDATE_RAM_def,
      pairTheory.EXISTS_PROD,ACCESS_ADDRESS_def,IN_UNION,IN_DIFF,UART0_addresses_def,
      WORD_ADD_0,IN_INSERT,IN_DISJOINT,NOT_IN_EMPTY,TOY_READ_TIME_def]
    \\ FULL_SIMP_TAC std_ss [TOY_READ_UART0_def,UART0_READ_def]
    \\ IMP_RES_TAC SPEC_UART0_WRITE_LEMMA    
    \\ IMP_RES_TAC UART0_WRITE
    \\ METIS_TAC [FILTER])  
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [TOY_READ_TIME_def]
  \\ FULL_SIMP_TAC std_ss [PERIPHERALS_OK_def,ALL_PERIPHERALS_def,UART0_DEVICE_def,
      COMPOSE_DEVICES_def,ROM_DEVICE_def,RAM_DEVICE_def,EMPTY_DEVICE_def,
      pairTheory.FORALL_PROD,LET_DEF,PERIPHERALS_NEXT_def,FILTER_ACCESSES_def,
      listTheory.FILTER,ROM_NEXT_def,RAM_NEXT_def,UPDATE_RAM_def,INIT_MEMORY_def,
      pairTheory.EXISTS_PROD,ACCESS_ADDRESS_def,IN_UNION,IN_DIFF,UART0_addresses_def,
      WORD_ADD_0,IN_INSERT,IN_DISJOINT,NOT_IN_EMPTY,TOY_READ_TIME_def]
  \\ FULL_SIMP_TAC std_ss [TOY_READ_UART0_def,UART0_READ_def,UART0_read_def]
  \\ `~(0xE000C000w IN domain p_1''')` by METIS_TAC [] 
  \\ `~(0xE000C000w IN domain p_1'''')` by METIS_TAC [] 
  \\ FULL_SIMP_TAC std_ss [UPDATE_RAM_def,UART0_NEXT_def]
  \\ FULL_SIMP_TAC std_ss [uart0_ok_def,MEM,HD,TL,memory_access_distinct,
       memory_access_11,MEM_WRITE_VALUE_def]
  \\ REPEAT STRIP_TAC  
  \\ FULL_SIMP_TAC std_ss [toy2set''_thm,TOY_READ_UNDEF_def,IN_DELETE,FILTER,
         oneTheory.one,IN_INSERT,NOT_IN_EMPTY,TOY_READ_REG_def,TOY_READ_UART0_def,
         TOY_READ_STATUS_def,APPLY_UPDATE_THM,TOY_READ_INSTR_def,TOY_READ_RAM_def,
         UART0_NEXT_NIL,ACCESS_ADDRESS_def,IN_UNION,WORD_ADD_0,UART0_addresses_def]
  \\ METIS_TAC []);

val BIT_UPDATE_w2w = prove(
  ``!i x w. i < 8 ==> (w ' i = x) ==> 
            (BIT_UPDATE i x ((w2w:word8->word32) w) = w2w w)``,
  SIMP_TAC (std_ss++wordsLib.SIZES_ss) [fcpTheory.CART_EQ,w2w,
    BIT_UPDATE_def,fcpTheory.FCP_BETA] \\ METIS_TAC []);

val SPEC_UART0_STATUS = prove(
  ``SPEC TOY_MODEL 
      (tR a 0xE000C000w * tR b w * tUART0 (inl,int,outl,outt) * tPC p * tT t) 
      {(p,iLDR b (a,0x14w))} 
      (SEP_EXISTS w. tR a 0xE000C000w * 
         tR b (BIT_UPDATE 0 (int <= t /\ inl <> []) 
              (BIT_UPDATE 5 (outt <= t) w)) * 
         tUART0 (inl,int,outl,outt) * tPC (p + 4w) * tT (t + 1))``,
  SIMP_TAC std_ss [progTheory.SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC IMP_TOY_SPEC
  \\ SIMP_TAC std_ss [tUART0_IO_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ SIMP_TAC std_ss [pairTheory.FORALL_PROD,pairTheory.EXISTS_PROD]
  \\ SIMP_TAC std_ss [STAR_toy2set,GSYM STAR_ASSOC,tPC_def,
         pred_setTheory.IN_DELETE,cond_STAR,TOY_NEXT_def,CODE_POOL_toy2set]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [TOY_READ_REG_def,NEXT_def,TOY_READ_INSTR_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [NEXT_INST_def,LET_DEF,ATTACH_MEMORY_ACCESS_def,INC_PC_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,TOY_READ_UNDEF_def]
  \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [PERIPHERALS_OK_def,ALL_PERIPHERALS_def,UART0_DEVICE_def,
      COMPOSE_DEVICES_def,ROM_DEVICE_def,RAM_DEVICE_def,EMPTY_DEVICE_def,
      pairTheory.FORALL_PROD,LET_DEF,PERIPHERALS_NEXT_def,FILTER_ACCESSES_def,
      listTheory.FILTER,ROM_NEXT_def,RAM_NEXT_def,UPDATE_RAM_def,
      pairTheory.EXISTS_PROD,ACCESS_ADDRESS_def,IN_UNION,IN_DIFF,UART0_addresses_def,
      WORD_ADD_0,IN_INSERT,IN_DISJOINT,NOT_IN_EMPTY,TOY_READ_TIME_def,word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [TOY_READ_UART0_def,UART0_READ_def]
    \\ METIS_TAC [FILTER,UART0_NEXT_EXISTS])
  \\ FULL_SIMP_TAC std_ss [word_add_n2w]
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [TOY_READ_TIME_def]
  \\ FULL_SIMP_TAC std_ss [PERIPHERALS_OK_def,ALL_PERIPHERALS_def,UART0_DEVICE_def,
      COMPOSE_DEVICES_def,ROM_DEVICE_def,RAM_DEVICE_def,EMPTY_DEVICE_def,
      pairTheory.FORALL_PROD,LET_DEF,PERIPHERALS_NEXT_def,FILTER_ACCESSES_def,
      listTheory.FILTER,ROM_NEXT_def,RAM_NEXT_def,UPDATE_RAM_def,INIT_MEMORY_def,
      pairTheory.EXISTS_PROD,ACCESS_ADDRESS_def,IN_UNION,IN_DIFF,UART0_addresses_def,
      WORD_ADD_0,IN_INSERT,IN_DISJOINT,NOT_IN_EMPTY,TOY_READ_TIME_def]
  \\ FULL_SIMP_TAC std_ss [TOY_READ_UART0_def,UART0_READ_def,UART0_read_def]
  \\ `~(0xE000C014w IN domain p_1''')` by METIS_TAC [] 
  \\ `~(0xE000C014w IN domain p_1'''')` by METIS_TAC [] 
  \\ FULL_SIMP_TAC std_ss [UPDATE_RAM_def,UART0_NEXT_def]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [uart0_ok_def,MEM,HD,TL,
       memory_access_distinct,memory_access_11,MEM_WRITE_VALUE_def,n2w_11]
  \\ REPEAT STRIP_TAC THEN1
   (Q.EXISTS_TAC `w2w p_1'''''.U0LSR`
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC (MATCH_MP BIT_UPDATE_w2w (DECIDE ``5 < 8``))
    \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (GSYM (RW [AND_IMP_INTRO] BIT_UPDATE_w2w))
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (REPEAT STRIP_TAC  
    \\ FULL_SIMP_TAC std_ss [toy2set''_thm,TOY_READ_UNDEF_def,IN_DELETE,FILTER,
         oneTheory.one,IN_INSERT,NOT_IN_EMPTY,TOY_READ_REG_def,TOY_READ_UART0_def,
         TOY_READ_STATUS_def,APPLY_UPDATE_THM,TOY_READ_INSTR_def,TOY_READ_RAM_def,
         UART0_NEXT_NIL,ACCESS_ADDRESS_def,IN_UNION,WORD_ADD_0,UART0_addresses_def]
    \\ METIS_TAC []));

val SPEC_UART0_STATUS_BIT = prove(
  ``SPEC TOY_MODEL 
      (tR b w * tPC p * tS c * tT t)
      {(p,iCMP b b (\x y. ~(x ' i)))}
      (tR b w * tPC (p + 4w) * tS (~(w ' i)) * tT (t + 1))``,
  toy_spec_tac);

val TOY_READ_INT = let
  val th = SPEC_COMPOSE_RULE [SPEC_UART0_STATUS,Q.INST [`i`|->`0`] SPEC_UART0_STATUS_BIT]
  val lemma = RW [] (EVAL ``0 < dimindex (:32)``)
  val th = SIMP_RULE std_ss [MATCH_MP APPLY_BIT_UPDATE_THM lemma,GSYM ADD_ASSOC] th
  val th = HIDE_POST_RULE ``tR b`` th
  val th = DISCH ``~(inl = []:word8 list)`` th
  val th = RW [GSYM SPEC_MOVE_COND] (SIMP_RULE std_ss [STAR_ASSOC] th)
  val th = Q.INST [`a`|->`1w`,`b`|->`2w`,`w`|->`r2`] th
  in th end;

val TOY_READ_OUTT = let
  val th = SPEC_COMPOSE_RULE [SPEC_UART0_STATUS,Q.INST [`i`|->`5`] SPEC_UART0_STATUS_BIT]
  val lemma = RW [] (EVAL ``5 < dimindex (:32)``)
  val th = SIMP_RULE std_ss [MATCH_MP APPLY_BIT_UPDATE_THM lemma,GSYM ADD_ASSOC] th
  val th = HIDE_POST_RULE ``tR b`` th
  val th = HIDE_PRE_RULE ``tR b`` th
  val th = RW [GSYM SPEC_MOVE_COND] (SIMP_RULE std_ss [STAR_ASSOC] th)
  val th = Q.INST [`a`|->`1w`,`b`|->`2w`,`w`|->`r2`] th
  in th end;

val TOY_READ_INL = let
  val th = SPEC_UART0_READ
  val th = RW [GSYM SPEC_MOVE_COND] (SIMP_RULE std_ss [STAR_ASSOC] th)
  val th = Q.INST [`a`|->`1w`] th
  in th end;  


(* -------------------------------------------------------------------------- *)
(*  Prove SPEC theorem for reading a byte from UART0                          *)
(* -------------------------------------------------------------------------- *)

val _ = add_decompiled ("TOY_READ_INT",TOY_READ_INT,8,SOME 8)

val (uart_read_spec,uart_read_def) = basic_decompile toy_tools "uart_read" NONE `
  insert:TOY_READ_INT 
  iBCC (-8w)`;

val uart_read_thm = prove(
  ``!t int.
       ~(inl = []) ==>
       ?t2. uart_read_pre (inl,int,outl,outt,t) /\ int <= t2 /\
            (uart_read (inl,int,outl,outt,t) = (inl,int,outl,outt,t2))``,
  completeInduct_on `int - t:num`
  THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss []
  THEN Cases_on `int <= t`
  THEN ONCE_REWRITE_TAC [uart_read_def]
  THEN FULL_SIMP_TAC std_ss [LET_DEF,NOT_CONS_NIL,GSYM ADD_ASSOC]
  THEN1 DECIDE_TAC
  THEN `int - (t + 3) < int - t` by DECIDE_TAC
  THEN RES_TAC THEN METIS_TAC []);

val SPEC_COMPOSE_IMP = METIS_PROVE [SPEC_COMPOSE,SPEC_WEAKEN]
  ``SPEC m p1 c1 q1 ==> SPEC m p2 c2 q2 ==> SEP_IMP q1 p2 ==> SPEC m p1 (c1 UNION c2) q2``;

val UART0_READ_THM = let
  val th = SPEC_BOOL_FRAME_RULE uart_read_spec ``~(inl = []:word8 list)``
  val th2 = HIDE_POST_RULE ``tT`` SPEC_UART0_READ
  val th2 = Q.INST [`a`|->`1w`,`p`|->`p + 0xCw`] th2
  val th2 = SPEC_FRAME_RULE th2 ``~(tR 2w) * ~tS``
  val th2 = SEP_EXISTS_PRE_RULE ``t:num`` th2
  val th = MATCH_MP (MATCH_MP SPEC_COMPOSE_IMP th) th2
  val th = remove_primes th
  val goal = (fst o dest_imp o concl) th
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC uart_read_thm    
    \\ POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `t2`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [INSERT_UNION_EQ,UNION_EMPTY,word_arith_lemma1,STAR_ASSOC] th
  val th = SEP_EXISTS_PRE_RULE ``t:num`` th
  val th = SEP_EXISTS_PRE_RULE ``int:num`` th
  val th = SEP_EXISTS_PRE_RULE ``outt:num`` th
  val (th,goal) = SPEC_STRENGTHEN_RULE th 
       ``tR 0x1w 0xE000C000w * ~tR 0x2w * tUART0_IO (inl,outl) *
         tPC p * ~tS * ~tT * cond (inl <> [])``
  val lemma = prove(goal,
    SIMP_TAC std_ss [tUART0_IO_def,SEP_CLAUSES,ISPEC ``tT`` SEP_HIDE_def]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `outt` \\ Q.EXISTS_TAC `int` \\ Q.EXISTS_TAC `x` 
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ METIS_TAC [uart_read_thm])
  val th = MP th lemma
  val ((th2,_,_),_) = toy_spec "iREG 1w 1w 1w (\\x y. 0xE000C000w)"
  val th2 = HIDE_POST_RULE ``tT`` th2
  val th2 = HIDE_PRE_RULE ``tT`` th2
  val th2 = HIDE_PRE_RULE ``tR 1w`` th2
  val th = RW [STAR_ASSOC] (SPEC_COMPOSE_RULE [th2,th])
  in th end;

val _ = save_thm("UART0_READ_THM",UART0_READ_THM);  
  

(* -------------------------------------------------------------------------- *)
(*  Prove SPEC theorem for writing a byte to UART0                            *)
(* -------------------------------------------------------------------------- *)

val _ = add_decompiled ("TOY_READ_OUTT",TOY_READ_OUTT,8,SOME 8)

val (uart_read2_spec,uart_read2_def) = basic_decompile toy_tools "uart_read2" NONE `
  insert:TOY_READ_OUTT 
  iBCC (-8w)`;

val uart_read2_thm = prove(
  ``!t outt.
       ?t2. uart_read2_pre (inl,int,outl,outt,t) /\ outt <= t2 /\
            (uart_read2 (inl,int,outl,outt,t) = (inl,int,outl,outt,t2))``,
  completeInduct_on `outt - t:num`
  THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss []
  THEN Cases_on `outt <= t`
  THEN ONCE_REWRITE_TAC [uart_read2_def]
  THEN FULL_SIMP_TAC std_ss [LET_DEF,NOT_CONS_NIL,GSYM ADD_ASSOC]
  THEN1 DECIDE_TAC
  THEN `outt - (t + 3) < outt - t` by DECIDE_TAC
  THEN RES_TAC THEN METIS_TAC []);

val SPEC_COMPOSE_IMP = METIS_PROVE [SPEC_COMPOSE,SPEC_WEAKEN]
  ``SPEC m p1 c1 q1 ==> SPEC m p2 c2 q2 ==> SEP_IMP q1 p2 ==> SPEC m p1 (c1 UNION c2) q2``;

val UART0_WRITE_THM = let
  val th = SPEC_FRAME_RULE uart_read2_spec ``tR 3w r3``
  val th2 = HIDE_POST_RULE ``tT`` SPEC_UART0_WRITE
  val th2 = Q.INST [`a`|->`1w`,`p`|->`p + 0xCw`,`b`|->`3w`,`w`|->`r3:word32`] th2
  val th2 = SPEC_FRAME_RULE th2 ``~(tR 2w) * ~tS``
  val th2 = SEP_EXISTS_PRE_RULE ``t:num`` th2
  val th = MATCH_MP (MATCH_MP SPEC_COMPOSE_IMP th) th2
  val th = remove_primes th
  val goal = (fst o dest_imp o concl) th
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND]
    \\ REPEAT STRIP_TAC
    \\ STRIP_ASSUME_TAC (SPEC_ALL uart_read2_thm)    
    \\ POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `t2`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [INSERT_UNION_EQ,UNION_EMPTY,word_arith_lemma1,STAR_ASSOC] th
  val th = SEP_EXISTS_PRE_RULE ``t:num`` th
  val th = SEP_EXISTS_PRE_RULE ``int:num`` th
  val th = SEP_EXISTS_PRE_RULE ``outt:num`` th
  val (th,goal) = SPEC_STRENGTHEN_RULE th 
       ``tR 0x1w 0xE000C000w * ~tR 0x2w * tR 0x3w r3 * tUART0_IO (inl,outl) *
         tPC p * ~tS * ~tT``
  val lemma = prove(goal,
    SIMP_TAC std_ss [tUART0_IO_def,SEP_CLAUSES,ISPEC ``tT`` SEP_HIDE_def]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR] 
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `outt` \\ Q.EXISTS_TAC `int` \\ Q.EXISTS_TAC `x` 
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ METIS_TAC [uart_read2_thm]) 
  val th = MP th lemma
  val ((th2,_,_),_) = toy_spec "iREG 1w 1w 1w (\\x y. 0xE000C000w)"
  val th2 = HIDE_POST_RULE ``tT`` th2
  val th2 = HIDE_PRE_RULE ``tT`` th2
  val th2 = HIDE_PRE_RULE ``tR 1w`` th2
  val th = RW [STAR_ASSOC] (SPEC_COMPOSE_RULE [th2,th])
  in th end;

val _ = save_thm("UART0_WRITE_THM",UART0_WRITE_THM);  


val _ = export_theory();

