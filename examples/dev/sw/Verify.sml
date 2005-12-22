structure Verify = 
struct

local open HolKernel Parse boolLib bossLib pairLib word32Lib goalstackLib
        numSyntax listSyntax
        pairTheory listTheory optionTheory preARMTheory word32Theory
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
           List.foldl (fn (v,p) => mk_conj(p, one_var v)) boolSyntax.T ls_unchanged
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
			mk_conj(mk_eq(mk_comb(Term`w2n`, mk_comb(pre_reg, Term`14`)), #2 (dest_pair (tr_iB))), 
				assum1)
		end
	else 
		assumption

    val pred = mk_imp(assumption, mk_outF outs)

   in
        list_mk_forall( [pre_pc, pre_cpsr, pre_reg, pre_mem], pred)
   end;



(*------------------------------------------------------------------------------------------------------*)
(* Simulate a ARM program for n steps					                                *)
(*------------------------------------------------------------------------------------------------------*)

val INSTB_LEM : thm ref = ref TRUTH; 

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
        (i+1, mk_conj (tr, mk_eq (mk_comb (Term`instB`, term_of_int i), List.nth(tr_instL, i))))) (0,boolSyntax.T) tr_instL);

     val _ = INSTB_LEM := prove (mk_instB_items, EVAL_TAC);

     val tr_byn = term_of_int (length tr_instL);
     val cur_instB = mk_pair(Term`instB`, tr_byn)
  in
     cur_instB
  end

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

fun simT (fname, ftype, args, stms, outs) =
  let
     val cur_instB = uploadCode stms;
     val cur_byn = #2 (dest_pair cur_instB)
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

(*
val (tr_iB,(pc1,pc2),(ins,outs), ls_unchanged, n,tr_f) = 
	(``(instB,2)``, (0,2),(args,outs), [Assem.REG 10], 3,``test0``);
set_goal ([], mk_pred ``(instB,3)`` (0,3) (args,outs) [] 3 ``test0``);
*)

(*------------------------------------------------------------------------------------------------------*)
(* TACs for simulation									                *)
(*------------------------------------------------------------------------------------------------------*)

val MEM_TAC = 
  REWRITE_TAC ([write_def, read_pc_def, set_pc_def, read_def] @ type_rws "EXP")
    THEN BETA_TAC 
    THEN CONV_TAC 
          (ONCE_DEPTH_CONV (REWRITE_CONV ([write_def, STORE_def] @ 
                                 type_rws "EXP" @ type_rws "OFFSET") 
		  THENC BETA_CONV 
		  THENC reduceLib.REDUCE_CONV))

fun TAC0 defs = 
  REWRITE_TAC (defs @ [read_def] @ (type_rws "EXP")) THEN
  GEN_BETA_TAC

val cond_thm = Q.prove
(`(if x then p else (if x then q else z)) = (if x then p else z)`,
 RW_TAC std_ss []);

val [FOLDL_NIL, FOLDL_CONS] = CONJUNCTS FOLDL;

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

        CONV_TAC (DEPTH_CONV ((REWR_CONV FOLDL_CONS ORELSEC REWR_CONV FOLDL_NIL)
	    THENC RATOR_CONV (RAND_CONV (DEPTH_CONV GEN_BETA_CONV
                    THENC REWRITE_CONV ([read_def, write_def, STORE_def,pair_case_def]@ type_rws"EXP")
                    THENC reduceLib.REDUCE_CONV
                    THENC DEPTH_CONV GEN_BETA_CONV
                    THENC reduceLib.REDUCE_CONV
		    THENC REWRITE_CONV (type_rws "OFFSET")
		    THENC DEPTH_CONV BETA_CONV
                    THENC TOP_DEPTH_CONV (REWR_CONV cond_thm)))))
	THEN ASM_REWRITE_TAC [] THEN


  	REWRITE_TAC ([decode1_def, read_def, write_def, STORE_def, setS_def, getS_def, 
                             goto_def, WORD_ADD1, listTheory.HD, listTheory.TL, THE_DEF]
                @ type_rws "COND" @ type_rws "OFFSET" @ type_rws "COND"
                @ type_rws "OPERATOR" @ type_rws "EXP" @ type_rws "SRS") THEN
  	reduceLib.REDUCE_TAC THEN
	MEM_TAC THEN
 
	REWRITE_TAC [w2n_ELIM, WORD_SUB_ADD] THEN 
  	WORD_TAC
    ) g
  ); 

end (* local open *)
end (* structure *)
