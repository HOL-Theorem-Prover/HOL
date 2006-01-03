structure Verify =
struct

local open HolKernel Parse boolLib bossLib pairLib word32Lib goalstackLib
        numSyntax listSyntax
        pairTheory arithmeticTheory listTheory optionTheory preARMTheory word32Theory
in

(*------------------------------------------------------------------------------------------------------*)
(* mk_pred - Given an (instB,byn), (initial pc, final pc), (inputs, outputs), a list of unchanged       *)
(* registers/memory slots, the number of steps to be executed n, and a function f, it sets up a goal on *)
(* the property of the segment of code within initial pc to final pc.					*) 
(*------------------------------------------------------------------------------------------------------*)

val init_sp = ref 100;

fun mk_pred runT tr_iB (pc1,pc2) (ins,outs) ls_unchanged n tr_f =
   let

    exception invalidExp;

    fun mk_reads s (Assem.PAIR (e1,e2)) =
	    mk_pair(mk_reads s e1, mk_reads s e2)
     |  mk_reads s exp =
            mk_comb ( mk_comb (Term`read`, s), preARMSyntax.eval_exp exp)

    fun mk_unchanged s1 s2 =
        let fun one_var v =
              let val v1 = mk_comb(mk_comb(Term`read`, s1), preARMSyntax.eval_exp v)
                  val v2 = mk_comb(mk_comb(Term`read`, s2), preARMSyntax.eval_exp v)
              in
                  mk_eq (v2,v1)
              end
        in
	      List.foldl (fn (v,p) => mk_conj(p, one_var v)) (Term`T`) ls_unchanged
        end

    fun mk_pc pc value =
	mk_eq (pc, term_of_int value);

    val (pre_pc, post_pc) = ( mk_var ("pc0", Type `:ADDR`),
			      mk_var ("pc1", Type `:ADDR`));	
    val (pre_cpsr, post_cpsr) = (mk_var ("cpsr0", Type `:CPSR`),
				 mk_var ("cpsr1", Type `:CPSR`));

    val (pre_reg, post_reg) = 
	( mk_var ("regs0", Type `:(ADDR->DATA)`),  mk_var ("regs1", Type `:(ADDR->DATA)`));
    val (pre_mem, post_mem) =
	( mk_var ("mems0", Type `:(ADDR->DATA)`),  mk_var ("mems1", Type `:(ADDR->DATA)`));

    val (pre_st, post_st) = 
	( mk_pair (pre_reg, pre_mem ),
	  mk_pair (post_reg, post_mem)
	);

    fun mk_outF outs =
	let 
	    val outP0 = mk_pc post_pc pc2;							(* pc's values *)
	    val outP1 = mk_conj(outP0, mk_unchanged pre_st post_st);				(* unchanged values *)
	    val outP2 = mk_conj(outP1, mk_eq(mk_reads post_st outs, mk_comb (tr_f, mk_reads pre_st ins)));
												(* equality to the original function *)
	    val s1 = if runT then
			mk_comb (mk_comb(Term`terRun`, tr_iB),
                                        list_mk_pair [pre_pc, pre_cpsr, pre_st])
		     else
			mk_comb (mk_comb(mk_comb(Term`run`,term_of_int n), tr_iB), 
					list_mk_pair [pre_pc, pre_cpsr, pre_st]);

	    val outP3 = mk_let(mk_pabs(list_mk_pair [post_pc, post_cpsr, post_st],
				outP2), s1)
	in
	    outP3
	end

    val assumption = mk_pc pre_pc pc1;
    val assumption = if runT then 
		let val assum1 = 
			list_mk_conj [mk_eq( mk_comb(pre_reg,Term`13`), mk_comb (Term`n2w`, term_of_int (!init_sp))),
			      assumption,
			      mk_comb(mk_comb(Term`terminated`, tr_iB), list_mk_pair [pre_pc, pre_cpsr, pre_st])]
		in
			mk_conj(mk_eq(mk_comb(pre_reg,Term`14`), mk_comb (Term`n2w`, #2 (dest_pair (tr_iB)))), 
				assum1)
		end
	else 
		assumption

    val pred = mk_imp(assumption, mk_outF outs)

   in
        list_mk_forall( [pre_pc, pre_cpsr, pre_reg, pre_mem], pred)
   end;



(*------------------------------------------------------------------------------------------------------*)
(* Upload the instructions into the instruction buffer					                *)
(*------------------------------------------------------------------------------------------------------*)

val INSTB_LEM : (thm ref) = ref (DECIDE (Term`T`)); 
val cur_insts : (Assem.instr list) ref = ref [];

(* Upload the code to the instruction buffer, store the lemma about this buffer as INSTB_LEM		*) 

fun uploadCode stms =
 let

     (* Upload the instruction list into the instruction buffer,                *)
     (* and give theorems about access individual instruction in the buffer     *)

     fun mk_Segs L =
        if length L < 10 then [mk_list(L, Type `:INST`)]
        else mk_list(List.take(L,10),Type `:INST`) :: (mk_Segs (List.drop(L,10)));

     val segs = mk_list(mk_Segs (#1 (dest_list stms)),  Type `:INST list`);

     val instB_def  =  SIMP_RULE list_ss [LENGTH]
          (Define `instB = uploadSeg ((LENGTH ^segs)) ^segs (\addr.ARB)`);

     val tr_instL = #1 (dest_list stms);

     val mk_instB_items = #2 (List.foldl (fn (elm, (i,tr)) =>
        (i+1, mk_conj (tr, mk_eq (mk_comb (Term`instB`, term_of_int i), List.nth(tr_instL, i))))) (0,Term`T`) tr_instL);

     val _ = INSTB_LEM := prove (mk_instB_items, EVAL_TAC);

     val tr_byn = term_of_int (length tr_instL);
     val cur_instB = mk_pair(Term`instB`, tr_byn)
  in
     cur_instB
  end

(*------------------------------------------------------------------------------------------------------*)
(* Simulate a ARM program for n steps                                                                   *)
(*------------------------------------------------------------------------------------------------------*)

fun simN (fname, ftype, args, stms, outs) n =
  let
     val cur_instB = uploadCode stms;
     val cur_byn = #2 (dest_pair cur_instB)
  in
     set_goal ( [], 
		mk_pred true cur_instB 
		(0, int_of_term cur_byn) 
		(args,outs) 
		[] 
		n 
		(mk_const (fname, ftype))
	      )
  end;		

(*------------------------------------------------------------------------------------------------------*)
(* Simulate a ARM program until it terminates                                                           *)
(*------------------------------------------------------------------------------------------------------*)

fun simT (arm : (string * hol_type * Assem.exp * Assem.instr list * Assem.exp * (Assem.exp Binaryset.set)) list,insts) 
  =
  let
     val (fname, ftype, args, stms, outs, rs) = hd arm;
     val cur_instB = uploadCode insts;
     val cur_byn = #2 (dest_pair cur_instB)
     val _ = cur_insts := List.foldl (fn ((name,tp,ins,stms,outs,rs),stms1) =>
                                		stms1 @ stms) [] arm 
  in
     set_goal ( [],
                mk_pred true cur_instB
                (0, int_of_term cur_byn)
                (args,outs)
                []
                0
                (mk_const (fname, ftype))
              )
  end;

fun simR (arm : (string * hol_type * Assem.exp * Assem.instr list * Assem.exp * (Assem.exp Binaryset.set)) list,insts)
  =
  let
     val (fname, ftype, args, stms, outs, rs) = hd arm;
     val cur_instB = uploadCode insts;
     val cur_byn = #2 (dest_pair cur_instB)
     val _ = cur_insts := List.foldl (fn ((name,tp,ins,stms,outs,rs),stms1) =>
                                                stms1 @ stms) [] arm
  in
     set_goal ( [Term`!x. ~(x < 0w)`],
                mk_pred true cur_instB
                (0, int_of_term cur_byn)
                (args,outs)
                []
                0
                (mk_const (fname, ftype))
              )
  end;

(*------------------------------------------------------------------------------------------------------*)
(* TACs for simulation									                *)
(*------------------------------------------------------------------------------------------------------*)

val MOVE_TAC = 
    REWRITE_TAC [decode1_thm, HD, write_thm, read_thm];

val ARITH_TAC = 
    REWRITE_TAC [decode1_thm, HD, TL, write_thm, read_thm];

val LOGICAL_TAC = ARITH_TAC

val LDR_TAC = MOVE_TAC

val STR_TAC = 
    MOVE_TAC;

val [FOLDL_NIL, FOLDL_CONS] = CONJUNCTS FOLDL;

val LDM_TAC = 
    REWRITE_TAC [decode1_thm] THEN
    CONV_TAC (DEPTH_CONV ((REWR_CONV FOLDL_CONS ORELSEC REWR_CONV FOLDL_NIL)
        THENC RATOR_CONV (RAND_CONV (DEPTH_CONV GEN_BETA_CONV 
		THENC REWRITE_CONV [read_thm]
        	THENC WORD_CONV
        	THENC reduceLib.REDUCE_CONV
        	THENC REWRITE_CONV [write_thm]))))
    THEN WORD_TAC;

val STM_TAC = 
    REWRITE_TAC [decode1_thm, REVERSE_DEF, LENGTH, APPEND] THEN
    CONV_TAC (DEPTH_CONV ((REWR_CONV FOLDL_CONS ORELSEC REWR_CONV FOLDL_NIL)
        THENC RATOR_CONV (RAND_CONV (DEPTH_CONV GEN_BETA_CONV
                THENC REWRITE_CONV [read_thm, write_thm, pair_case_def]
                THENC reduceLib.REDUCE_CONV)))) THEN
    ASM_REWRITE_TAC [];

val CMP_TAC = 
     REWRITE_TAC [decode1_thm, read_thm, HD, TL, setS_thm] THEN
     WORD_TAC THEN ASM_REWRITE_TAC [];       

val BRANCH_TAC = 
     REWRITE_TAC [getS_thm] THEN WORD_TAC THEN
     REWRITE_TAC [decode1_thm, read_thm, write_thm, goto_thm, read_pc_def]


val BRANCH_LINK_TAC = 
     BRANCH_TAC



fun STOP_TAC defs = 
    RW_TAC std_ss [run_def, TERRUN_STOP] THEN
    RW_TAC list_ss ([LET_THM] @ defs) THEN
    REPEAT (CHANGED_TAC WORD_TAC)

(*------------------------------------------------------------------------------------------------------*)
(* Automatic reasoning                                                                                  *)
(*------------------------------------------------------------------------------------------------------*)

(*
fun get_pc (tassum, tg) = 
  let   
      fun toDecode2 t = 
	  let val (fterm, ts) = 
		strip_comb t
	  in 
	      if same_const fterm (Term`run`) then
		 int_of_term (hd (strip_pair (List.nth(ts, length ts - 1))))
	      else toDecode2 (List.nth (ts, length ts - 1))
	  end
  in
	toDecode2 tg
  end
*)

fun get_pc (tassum, tg) =
  let
      fun found t = 
	let val (fterm, ts) = strip_comb t in
	  same_const fterm (Term`run`)
	end
      val ts = #2 (strip_comb (find_term found tg)) 
  in 
     int_of_term (hd (strip_pair (List.nth(ts, length ts - 1))))
  end
  handle e => raise ERR "get_pc" "";

exception tacError;

fun select_tac (Assem.MOVE {...}) = MOVE_TAC
 |  select_tac (Assem.OPER {oper = (Assem.MRS,cond,flag), ...}) = MOVE_TAC
 |  select_tac (Assem.OPER {oper = (Assem.MSR,cond,flag), ...}) = MOVE_TAC

 |  select_tac (Assem.OPER {oper = (Assem.ADD,cond,flag), ...}) = ARITH_TAC
 |  select_tac (Assem.OPER {oper = (Assem.SUB,cond,flag), ...}) = ARITH_TAC
 |  select_tac (Assem.OPER {oper = (Assem.RSB,cond,flag), ...}) = ARITH_TAC
 |  select_tac (Assem.OPER {oper = (Assem.MUL,cond,flag), ...}) = ARITH_TAC
 |  select_tac (Assem.OPER {oper = (Assem.MLA,cond,flag), ...}) = ARITH_TAC
 |  select_tac (Assem.OPER {oper = (Assem.LSL,cond,flag), ...}) = ARITH_TAC
 |  select_tac (Assem.OPER {oper = (Assem.LSR,cond,flag), ...}) = ARITH_TAC
 |  select_tac (Assem.OPER {oper = (Assem.ASR,cond,flag), ...}) = ARITH_TAC
 |  select_tac (Assem.OPER {oper = (Assem.ROR,cond,flag), ...}) = ARITH_TAC

 |  select_tac (Assem.OPER {oper = (Assem.CMP,cond,flag), ...}) = CMP_TAC
 |  select_tac (Assem.OPER {oper = (Assem.TST,cond,flag), ...}) = CMP_TAC

 |  select_tac (Assem.OPER {oper = (Assem.AND,cond,flag), ...}) = LOGICAL_TAC
 |  select_tac (Assem.OPER {oper = (Assem.ORR,cond,flag), ...}) = LOGICAL_TAC
 |  select_tac (Assem.OPER {oper = (Assem.EOR,cond,flag), ...}) = LOGICAL_TAC

 |  select_tac (Assem.OPER {oper = (Assem.LDR,cond,flag), ...}) = LDR_TAC
 |  select_tac (Assem.OPER {oper = (Assem.STR,cond,flag), ...}) = STR_TAC
 |  select_tac (Assem.OPER {oper = (Assem.LDMFD,cond,flag), ...}) = LDM_TAC
 |  select_tac (Assem.OPER {oper = (Assem.STMFD,cond,flag), ...}) = STM_TAC

 |  select_tac (Assem.OPER {oper = (Assem.B,cond,flag), ...}) = BRANCH_TAC
 |  select_tac (Assem.OPER {oper = (Assem.BL,cond,flag), ...}) = BRANCH_LINK_TAC

 |  select_tac _ = raise tacError;


fun TAC0 n = 
  REWRITE_TAC [read_thm] THEN
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC (SPEC (term_of_int n) TERRUN_THM) THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC);


val ONE_STEP_TAC =
  (fn g =>
     ( let val g1 = hd (#1 (ONCE_ASM_REWRITE_TAC [] g))
	    val tac1 = select_tac (List.nth(!cur_insts, get_pc g1))
       in
	  ( ASM_REWRITE_TAC [] THEN
	    REWRITE_TAC [Once run_def, !INSTB_LEM] THEN
            reduceLib.REDUCE_TAC THEN
	    REWRITE_TAC [decode2_thm] THEN
	    tac1 THEN REWRITE_TAC [set_pc_def, write_thm, read_thm] THEN
	    WORD_TAC THEN
	    SIMP_TAC bool_ss []
	  ) g
       end
     )
  );

fun ONE_INST_TAC tac1 =
  (fn g =>
     (   ( ASM_REWRITE_TAC [] THEN
            REWRITE_TAC [Once run_def, !INSTB_LEM] THEN
            reduceLib.REDUCE_TAC THEN
            REWRITE_TAC [decode2_thm, decode1_thm] THEN
            tac1 THEN REWRITE_TAC [set_pc_def, write_thm, read_thm] THEN
            WORD_TAC THEN
            SIMP_TAC bool_ss []
          ) g
     )
  );


fun prove_arm defs =
  let 
      fun one_step (asl,g) =
		(    let val pc = get_pc (asl,g)
		    in if pc = length (!cur_insts) then
			STOP_TAC defs (asl,g)
		       else (ONE_INST_TAC (select_tac (List.nth(!cur_insts,pc))) THEN
			     one_step) (asl,g)
		    end
		)
  in
     (  TAC0 (length (!cur_insts)) THEN
	ONCE_ASM_REWRITE_TAC [] THEN
       one_step
     )
  end 

(*------------------------------------------------------------------------------------------------------*)
(* Some theorems about words					                                        *)
(*------------------------------------------------------------------------------------------------------*)

val WORD_IND_LEM = Q.prove (
 `!v x. (SUC v = w2n x) ==>
          ((v = w2n (x - 1w)) /\ ~(x = 0w))`,
   REPEAT STRIP_TAC THENL [
        `n2w v = x - 1w` by METIS_TAC [w2n_ELIM, SUC_ONE_ADD, ADD_EVAL, WORD_EQ_SUB_RADD, WORD_ADD_COMM] THEN
                `SUC v < 2 ** WL` by METIS_TAC [w2n_LT] THEN
                `v < 2 ** WL` by RW_TAC list_ss [LESS_EQ_SUC_REFL] THEN
                `v MOD 2 ** WL = w2n (x - 1w)` by METIS_TAC [w2n_EVAL, MOD_WL_def] THEN
                METIS_TAC [LESS_MOD],
        FULL_SIMP_TAC arith_ss [] THEN
                NTAC 2 (POP_ASSUM MP_TAC) THEN
                WORD_TAC THEN
                RW_TAC arith_ss []]
   );

(*
val TAC1 = 
  (fn g => 
    (   ONCE_ASM_REWRITE_TAC [] THEN
  	REWRITE_TAC [Once run_def, !INSTB_LEM] THEN
  	reduceLib.REDUCE_TAC THEN
  	REWRITE_TAC ([decode2_def] @ type_rws "option") THEN BETA_TAC THEN
	REWRITE_TAC (type_rws "COND") THEN
	REWRITE_TAC ([decode1_def, THE_DEF] @ type_rws "OPERATOR" @ type_rws "EXP") THEN
	reduceLib.REDUCE_TAC THEN 

	REWRITE_TAC [REVERSE_DEF, LENGTH, APPEND] THEN

        CONV_TAC (ONCE_DEPTH_CONV ((REWR_CONV FOLDL_CONS ORELSEC REWR_CONV FOLDL_NIL)
	    THENC RATOR_CONV (RAND_CONV (DEPTH_CONV GEN_BETA_CONV
                    THENC REWRITE_CONV ([read_def, write_def, STORE_def,pair_case_def] @ type_rws"EXP" @ type_rws "OFFSET")
                    THENC reduceLib.REDUCE_CONV
                    THENC DEPTH_CONV GEN_BETA_CONV
                    THENC reduceLib.REDUCE_CONV
		    THENC REWRITE_CONV (type_rws "OFFSET")
		    THENC DEPTH_CONV BETA_CONV
                    THENC TOP_DEPTH_CONV (REWR_CONV cond_thm)))))
	THEN ASM_REWRITE_TAC [] THEN


  	REWRITE_TAC ([decode1_def, read_def, write_def, STORE_def, setS, getS, 
                             goto_def, WORD_ADD1, listTheory.HD, listTheory.TL, THE_DEF]
                @ type_rws "COND" @ type_rws "OFFSET" @ type_rws "COND"
                @ type_rws "OPERATOR" @ type_rws "EXP" @ type_rws "SRS") THEN
  	reduceLib.REDUCE_TAC THEN
	MEM_TAC THEN
 
	REWRITE_TAC [w2n_ELIM, WORD_SUB_ADD] THEN 
  	WORD_TAC
    ) g
  ); 
*)
(*------------------------------------------------------------------------------------------------------*)
(* Find the inputs, outputs and changed registers/memory slots within a segment of code                 *)
(*------------------------------------------------------------------------------------------------------*)

(*

datatype ACCESS = READ | WRITE | PUSH | POP 
datatype ROLE = UNKNOWN | INPUT | OUTPUT | INSTACK;

fun mk_regL indexL = 
	List.map (fn n => Assem.REG n) indexL;

fun mk_memL indexL =
	List.map (fn n => Assem.MEM (Assem.NCONST n)) indexL;

fun mk_rmemL indexL =
        List.map (fn n => Assem.MEM (Assem.REG n)) indexL;


fun getIOC prog pc0 n =
  let
     val (regT:((ROLE * ROLE) T.table) ref, memCT:((ROLE * ROLE) T.table) ref, memRT:((ROLE * ROLE) T.table) ref) 
	  = (ref (T.empty), ref (T.empty), ref (T.empty)); 
     val accessT : ((int * int) T.table) ref = ref (T.empty);     

     fun peekT(t,index) = 
	case T.peek(t,index) of 
	     NONE => (UNKNOWN,UNKNOWN)
	 |   SOME v => v;

     exception invalidMode;
     exception unimplemented;

     fun ch_mode (UNKNOWN,UNKNOWN) READ = (INPUT,UNKNOWN)
      |  ch_mode (m,UNKNOWN) WRITE = (m, OUTPUT)
      |  ch_mode (m,OUTPUT) WRITE = (m,OUTPUT)
      |  ch_mode (m,OUTPUT) READ = (m,INSTACK)
      |  ch_mode (m,INSTACK) READ = (m,INSTACK)
      |  ch_mode (m,INSTACK) WRITE = (m,OUTPUT)
      |  ch_mode _ _ = raise invalidMode;

     fun beLoaded (Assem.REG r) (Assem.MEM(Assem.NCONST n)) = 
	   ( case T.peek (!accessT, r) of
		  NONE => ()
	      |   SOME (st, ld) => (accessT := T.enter (!accessT, r, (st, if n > ld then n else ld))))
      |  beLoaded _ _  = 
	    raise unimplemented;	

     fun beStored (Assem.REG r) (Assem.MEM(Assem.NCONST n)) =
           ( case T.peek (!accessT, r) of
                  NONE => (accessT := T.enter (!accessT, r, (n, ~1)))
              |   SOME v => ())
      |  beStored _ _  =
            raise unimplemented;

     fun update_mode (Assem.REG r) action = 
	  regT := T.enter (!regT, r, ch_mode (peekT(!regT, r)) action)
      |  update_mode (Assem.MEM (Assem.NCONST n)) action =
          memCT := T.enter (!memCT, n, ch_mode (peekT(!memCT, n)) action)
      |  update_mode (Assem.MEM (Assem.REG r)) action =
          memRT := T.enter (!memRT, r, ch_mode (peekT(!memRT, r)) action)
      |  update_mode _ _ = 
	  ();

     fun one_stm (Assem.OPER {oper = op1, dst = dst1, src = src1, jump = jp1}) =
	    let val _ = 
	        if op1 = Assem.LDR then beLoaded (hd dst1) (hd src1)
	        else if op1 = Assem.STR then beStored (hd src1) (hd dst1)	
	    	else if op1 = Assem.SWI then update_mode (Assem.REG 14) READ 
		else ()
	    in
		( List.map (fn exp => update_mode exp READ) src1;
		  List.map (fn exp => update_mode exp WRITE) dst1;
		  ()
		)
	    end
      | one_stm (Assem.MOVE {dst = dst1, src = src1}) =
	    ( update_mode src1 READ;
	      update_mode dst1 WRITE
	    )
      | one_stm _ = raise unimplemented;

     val (fname, ftype, args,stms,outs) = prog;
     val _ = 
	List.map one_stm (List.take( List.drop(stms,pc0), n));

     fun filter_inputs mode = 
	 mk_regL (List.filter (fn n => #1 (T.look (!regT,n)) = mode) (T.listKeys (!regT))) @ 
	 mk_memL (List.filter (fn n => #1 (T.look (!memCT,n)) = mode) (T.listKeys (!memCT))) @
         mk_rmemL (List.filter (fn n => #1 (T.look (!memRT,n)) = mode) (T.listKeys (!memRT))); 

     fun filter_out_stack mode =
         mk_regL (List.filter (fn n => #2 (T.look (!regT,n)) = mode) (T.listKeys (!regT))) @
         mk_memL (List.filter (fn n => #2 (T.look (!memCT,n)) = mode) (T.listKeys (!memCT))) @
         mk_rmemL (List.filter (fn n => #2 (T.look (!memRT,n)) = mode) (T.listKeys (!memRT)));

     val (ins, temps, outs) = (filter_inputs INPUT, filter_out_stack INSTACK, filter_out_stack OUTPUT);

     val changed = List.filter (fn Assem.REG n => 
				   ( case T.peek (!accessT, n) of
					  NONE => true
				      |   SOME (st,ld) =>
						not (st = ld)
				   )
				|  _ =>
				    true
			       )
		   (temps @ outs)      
     in
	(ins, changed, outs)
     end


*)

end (* local open *)
end (* structure *)

