structure prog_toyLib :> prog_toyLib =
struct

open HolKernel boolLib bossLib;
open toy_coreTheory toy_uartTheory toy_systemTheory prog_toyTheory;

open wordsLib stringLib addressTheory pred_setTheory combinTheory;
open set_sepTheory progTheory helperLib wordsTheory listTheory;

infix \\
val op \\ = op THEN;

val toy_spec_tac =
  SIMP_TAC std_ss [progTheory.SPEC_MOVE_COND,HD,TL] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC IMP_TOY_SPEC
  \\ SIMP_TAC std_ss [pairTheory.FORALL_PROD,pairTheory.EXISTS_PROD]
  \\ SIMP_TAC std_ss [STAR_toy2set,GSYM STAR_ASSOC,tPC_def,
         pred_setTheory.IN_DELETE,cond_STAR,TOY_NEXT_def,CODE_POOL_toy2set]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [TOY_READ_REG_def,NEXT_def,TOY_READ_INSTR_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [NEXT_INST_def,LET_DEF,ATTACH_MEMORY_ACCESS_def,INC_PC_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,TOY_READ_UNDEF_def,NO_MEMORY_ACCESS_def]
  \\ REPEAT STRIP_TAC
  THEN1 (IMP_RES_TAC (SIMP_RULE std_ss [pairTheory.EXISTS_PROD] PERIPHERALS_NEXT_EXISTS)
    \\ METIS_TAC [])
  \\ IMP_RES_TAC IMP_PERIPHERALS_OK \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [PERIPHERALS_OK_def,ALL_PERIPHERALS_def,UART0_DEVICE_def,
      COMPOSE_DEVICES_def,ROM_DEVICE_def,RAM_DEVICE_def,EMPTY_DEVICE_def,
      pairTheory.FORALL_PROD,LET_DEF,PERIPHERALS_NEXT_def,FILTER_ACCESSES_def,
      listTheory.FILTER,ROM_NEXT_def,RAM_NEXT_def,UPDATE_RAM_def,INIT_MEMORY_def,
      pairTheory.EXISTS_PROD,ACCESS_ADDRESS_def,IN_UNION,IN_DIFF,UART0_addresses_def,
      WORD_ADD_0,IN_INSERT,IN_DISJOINT,NOT_IN_EMPTY,TOY_READ_TIME_def,
      TOY_READ_STATUS_def]
  \\ FULL_SIMP_TAC std_ss [toy2set''_thm,TOY_READ_UNDEF_def,IN_DELETE,FILTER,
         oneTheory.one,IN_INSERT,NOT_IN_EMPTY,TOY_READ_REG_def,TOY_READ_UART0_def,
         TOY_READ_STATUS_def,APPLY_UPDATE_THM,TOY_READ_INSTR_def,TOY_READ_RAM_def,
         UART0_NEXT_NIL,ACCESS_ADDRESS_def,IN_UNION,WORD_ADD_0,UART0_addresses_def]
  \\ METIS_TAC [];

val iBCC_LEMMA = prove(
  ``SPEC TOY_MODEL 
      (tPC p * tS c * tT t * precond c)
      {(p,iBCC imm)}
      (tPC (p + imm) * tS c * tT (t + 1))``,
  SIMP_TAC std_ss [precond_def,SPEC_MOVE_COND] \\ toy_spec_tac);
  
val iBCC_NOP_LEMMA = prove(
  ``SPEC TOY_MODEL 
      (tPC p * tS c * tT t * precond ~c)
      {(p,iBCC imm)}
      (tPC (p + 4w) * tS c * tT (t + 1))``,
  SIMP_TAC std_ss [precond_def,SPEC_MOVE_COND] \\ toy_spec_tac);

val iREG_aaa = prove(
  ``SPEC TOY_MODEL 
      (tPC p * tR a x * tT t)
      {(p,iREG a a a f)}
      (tPC (p + 4w) * tR a (f x x) * tT (t + 1))``,
  toy_spec_tac);

fun toy_prove_specs s = let
  val tm = Parse.Term [QUOTE s]
  val (m,_) = match_term ``iBCC imm`` tm
  val th1 = INST m iBCC_LEMMA  
  val th2 = INST m iBCC_NOP_LEMMA  
  val th1 = RW [GSYM word_sub_def] th1
  val tm = find_term (can (match_term ``tPC (f (w:word32) ((n2w n):word32))``)) (concl th1)
  val n = tm |> cdr |> cdr |> cdr |> numSyntax.dest_numeral |> Arbnum.toInt
  val n = if (tm |> cdr |> car |> car |> dest_const |> fst) = "word_sub" 
          then 0-n else n
  in ((th1,4,SOME n),SOME (th2,4,SOME 4)) end handle e => let
  val tm = Parse.Term [QUOTE s]
  val (m,_) = match_term ``iREG a a a f`` tm
  val th1 = INST m iREG_aaa
  val th1 = SIMP_RULE std_ss [] th1
  in ((th1,4,SOME 4),NONE) end            
  
fun toy_jump (tm1:term) (tm2:term) (jump_length:int) (forward:bool) = ("",0)
val toy_status = REFL ``~tS``;
val toy_pc = ``tPC``;
val toy_spec = cache toy_prove_specs;
val toy_tools = ((toy_spec, toy_jump, toy_status, toy_pc) : decompiler_tools)

end
