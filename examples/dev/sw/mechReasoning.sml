(*

loadPath := 
            (concat Globals.HOLDIR "/examples/dev/sw") :: 
            (concat Globals.HOLDIR "/examples/elliptic/arm") :: 
            (concat Globals.HOLDIR "/examples/temporal_deep/src/tools") :: 
            (concat Globals.HOLDIR "/examples/sep") ::
            !loadPath;

app load ["relationTheory", "pred_setSimps","pred_setTheory","whileTheory","finite_mapTheory","rich_listTheory", "listSyntax", 
          "ILTheory", "rulesTheory", "preARMSyntax", "annotatedIR", "funCall", "preARMTheory", "wordsLib"];

quietdec := true;
  open HolKernel Parse boolLib bossLib numLib pairLib relationTheory pairTheory arithmeticTheory listSyntax preARMTheory
     preARMSyntax Assem pred_setSimps pred_setTheory listTheory rich_listTheory whileTheory finite_mapTheory declFuncs
     annotatedIR ILTheory rulesTheory wordsLib wordsTheory IRSyntax;
quietdec := false;
*)

structure mechReasoning = struct
  local
  open HolKernel Parse boolLib bossLib numLib pairLib relationTheory pairTheory arithmeticTheory listSyntax preARMTheory
     preARMSyntax Assem pred_setSimps pred_setTheory listTheory rich_listTheory whileTheory finite_mapTheory declFuncs
     annotatedIR ILTheory rulesTheory wordsLib wordsTheory IRSyntax
  in

infix ++ THENC ORELSEC THEN THENL ORELSE |-> ##;

(*---------------------------------------------------------------------------------*)
(*      Simplifier on finite maps                                                  *) 
(*---------------------------------------------------------------------------------*)
fun mk_unchanged_set f_name =
	let
		val {regs=regs,...} = declFuncs.getFunc f_name;
		val univ_set = Binaryset.addList (Binaryset.empty Int.compare, [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14])
		val neg_regs = Binaryset.difference(univ_set,regs)
	in
		neg_regs
	end;

fun mk_unchanged_term set =
	let
		val int_list = Binaryset.listItems set;
		val mreg_list = map (fn n => 
			let 
				val n_term = term_of_int n 
			in  
				rhs (concl (EVAL (mk_comb (Term `from_reg_index`, n_term))))
			end) int_list;
		val changed_list = mk_list (mreg_list, Type `:MREG`);
	in
		changed_list
	end;


val fupdate_normalizer =
 let val thm = SPEC_ALL FUPDATE_LT_COMMUTES
     val pat = lhs(snd(dest_imp(concl thm)))
 in
   {name = "Finite map normalization",
    trace = 2,
    key = SOME([],pat),
    conv = let fun reducer tm =
                 let val (theta,ty_theta) = match_term pat tm
                     val thm' = INST theta (INST_TYPE ty_theta thm)
                     val constraint = fst(dest_imp(concl thm'))
                     val cthm = EQT_ELIM(reduceLib.REDUCE_CONV constraint)
                 in MP thm' cthm
                 end
           in
               K (K reducer)
           end}
 end;

val finmap_conv_frag =
 simpLib.SSFRAG
     {convs = [fupdate_normalizer],
      rewrs = [], ac=[],filter=NONE,dprocs=[],congs=[]};

val finmap_ss = std_ss ++ finmap_conv_frag ++  rewrites [FUPDATE_EQ, FAPPLY_FUPDATE_THM];

val set_ss = std_ss ++ SET_SPEC_ss ++ PRED_SET_ss;

(*---------------------------------------------------------------------------------*)
(*   Assistant Functions                                                           *) 
(*---------------------------------------------------------------------------------*)



(* make variable tuple, e.g. ((v0,v1),v2,...) *)

fun mk_vars exp =
  let
    val i = ref (~1);
    fun set_vars (IRSyntax.PAIR (e1,e2)) =
          mk_pair(set_vars e1, set_vars e2)
     |  set_vars exp =
          mk_var ("v" ^ (i := !i + 1; Int.toString (!i)) , Type `:DATA`)
  in
    set_vars exp 
  end

(* make mread tuple, e.g. ((st<v0>,st<v1>),st<v2>,...) *)

fun mk_mreads st (IRSyntax.PAIR (e1,e2)) =
        mk_pair(mk_mreads st e1, mk_mreads st e2)
 |  mk_mreads st (IRSyntax.REG e) =
      list_mk_comb (Term`mread`, [st, mk_comb (Term`RR`, IRSyntax.convert_reg (IRSyntax.REG e))])
 |  mk_mreads st (IRSyntax.MEM m) =
      list_mk_comb (Term`mread`, [st, mk_comb (Term`RM`, IRSyntax.convert_mem (IRSyntax.MEM m))])
 |  mk_mreads st _ =
      (print "mk_mreads: invalid incoming expression"; 
       raise ERR "" ("mk_mreads: invalid incoming expression"));


fun ADDR30_CONV t =
	let
		val (f, args) = dest_comb t;
		val _ = if same_const (Term `ADDR30`) f then () else Raise (ERR "" "Syntax");
      val num_term = rand (rand args);
		val num = dest_numeral num_term;
		val (c, r) = Arbnum.divmod(num, Arbnum.fromInt 4);
		val _ = if (r = Arbnum.zero) then () else  Raise (ERR "" "Syntax");
		val mult_term = mk_mult(mk_numeral c, term_of_int 4);
		val mult_thm = GSYM (EVAL mult_term);
		val thm = RAND_CONV (RAND_CONV (REWRITE_CONV [mult_thm])) t
	in
		thm
	end;

val word_extract_thm = GSYM ((SIMP_RULE std_ss [w2w_def, combinTheory.o_DEF, FUN_EQ_THM]) word_extract_def);


val SIM_REWRITE_CONV = 
	REWRITE_CONV ([mdecode_def, write_thm, read_thm, toMEM_def, toEXP_def, toREG_def, index_of_reg_def, WORD_ADD_0, FAPPLY_FUPDATE_THM, word4_distinct,
	GSYM WORD_ADD_ASSOC, FUPDATE_EQ, fupdate_lt_commutes_word4, word_sub_def]);


val SIM_CONV = 
		SIM_REWRITE_CONV THENC
		WORDS_CONV THENC
		REWRITE_CONV [word_extract_thm, WORD_ADD_0]
	
val SIM_MEM_CONV = 
		SIM_REWRITE_CONV THENC
		SIMP_CONV arith_ss [word4_distinct, ADDR30_ADD_CONST_MOD, GSYM WORD_ADD_ASSOC,
			WORD_EQ_ADD_LCANCEL] THENC
		WORDS_CONV THENC
		REWRITE_CONV [word_extract_thm, WORD_ADD_0]

val SIM_PUSH_CONV =
		REWRITE_CONV [mdecode_def, pushL_def, GSYM MAP_REVERSE, REVERSE_DEF, APPEND, MAP, LENGTH, FOLDL] THENC
		DEPTH_CONV GEN_BETA_CONV THENC
		SIM_REWRITE_CONV THENC
		SIMP_CONV arith_ss [ADDR30_ADD_CONST_MOD] THENC
		SIM_CONV;
	
val SIM_POP_CONV =
		REWRITE_CONV [mdecode_def, popL_def, GSYM MAP_REVERSE, REVERSE_DEF, APPEND, MAP, LENGTH, FOLDL] THENC
		DEPTH_CONV GEN_BETA_CONV THENC
		SIM_REWRITE_CONV THENC
		SIMP_CONV arith_ss [word4_distinct, ADDR30_ADD_CONST_MOD, GSYM WORD_ADD_ASSOC,
			WORD_EQ_ADD_LCANCEL] THENC
		SIM_CONV;

(* make a list of rules [exp0 <- v0, exp1 <- v1, ...] *)
fun mk_subst_rules expL =
  let
    val i = ref (~1);
  in 
    List.map (fn exp => (i := !i + 1; {redex = exp, residue = mk_var ("v" ^ (Int.toString (!i)), Type `:DATA`)})) expL
  end

fun read_one_var s exp =
  let
     val v0 = IRSyntax.read_exp s exp;
	  fun conv (IRSyntax.MEM (b, off)) = SIM_MEM_CONV |
			conv _ = SIM_CONV
     val v1 = rhs (concl ((conv exp) v0))
  in
     v1
  end


(*---------------------------------------------------------------------------------*)
(*      Symbolic Simulation of Instructions                                        *) 
(*---------------------------------------------------------------------------------*)

val ACCESS_CONV = SIMP_CONV finmap_ss [mread_def, write_thm, read_thm, toMEM_def, toEXP_def, toREG_def, index_of_reg_def];
val ACCESS_RULE = SIMP_RULE finmap_ss [mread_def, write_thm, read_thm, toMEM_def, toEXP_def, toREG_def, index_of_reg_def];

(*  Basic RULE for instructions execpt for PUSH and POP                            *) 



(* Find the first instruction to be simulated next   *)
 
fun locate_first_inst t = 
    if type_of t = Type `:DOPER` then true
    else false;


fun is_mdecode_exp t =
	(let
	  val const = #1 (strip_comb t)
	in
	  (same_const const (Term `mdecode`))
   end) handle _ => false;


fun find_innermost_mdecode t = 	
	(let
		val state = (rand (rator t));
	in
		if is_mdecode_exp state then find_innermost_mdecode state else t
	end)
  handle e => (print "find_innermost_mdecode:syntax error"; Raise e);

(* eliminate all "decode"s and get the new state *) 
(*
fun step th =
	let
		val t1 = concl th
      val st = if is_imp t1 then rhs (#2 (dest_imp t1)) else rhs t1
		val t1 = find_term locate_first_inst st;
      val operator = #1 (strip_comb t1);
		val t2 = find_innermost_mdecode st;
		val conv = if same_const operator (Term `MPUSH`) then SIM_PUSH_CONV
						else if same_const operator (Term `MPOP`) then SIM_POP_CONV
						else if same_const operator (Term `MLDR`) then SIM_MEM_CONV
						else if same_const operator (Term `MSTR`) then SIM_MEM_CONV
						else SIM_CONV 
		val t2_thm = conv t2;
	in
		REWRITE_RULE [t2_thm] th
	end;

val th = th1

val th = step th
*)
fun elim_decode th = 
  let val t1 = concl th
      val st = if is_imp t1 then rhs (#2 (dest_imp t1)) else rhs t1
  in 
      if is_pair st then th
      else
          let val t1 = find_term locate_first_inst st;
              val operator = #1 (strip_comb t1);
              val _ = print ("Simulating a " ^ (#1 (dest_const operator)) ^ " instruction\n");
				  val t2 = find_innermost_mdecode st;
				  val conv = if same_const operator (Term `MPUSH`) then SIM_PUSH_CONV
									else if same_const operator (Term `MPOP`) then SIM_POP_CONV
									else if same_const operator (Term `MLDR`) then SIM_MEM_CONV
									else if same_const operator (Term `MSTR`) then SIM_MEM_CONV
									else SIM_CONV 
				  val t2_thm = conv t2;
              val th' =  REWRITE_RULE [t2_thm] th
          in  elim_decode th'
          end
  end
  handle e => (print "get_blk_spec: errors occur while symbolically simulating a block! "; Raise e);


(* Given a list of IR statements, return a theorem indicating the state after symolic simulation *)
(* pre_spec specifies the pre-conditions before the simulation                                   *)

(*
	val stms = instL*)
fun sim_stms blk = 
  let
     val st = mk_pair (mk_var ("regs", Type `:REGISTER |-> DATA`), mk_var ("mem", Type `:ADDR |-> DATA`));
     val instance = list_mk_comb (Term`run_ir:CTL_STRUCTURE -> DSTATE -> DSTATE`, [blk, st]);
     val th0 =  REWRITE_CONV [IR_SEMANTICS_BLK] instance;
     val th1 = SIMP_RULE std_ss [mread_def, toMEM_def, toREG_def, index_of_reg_def, read_thm] th0;
     val th2 = elim_decode th1              (* symbolically simulate the block *)
  in
     th2
  end;

(*---------------------------------------------------------------------------------*)
(*      PSPEC specification and Mechanized Reasoning                               *) 
(*---------------------------------------------------------------------------------*)

(* Make a PSPEC specification                                                                    *) 

val basic_outL = [IRSyntax.REG 11, IRSyntax.REG 13];               (* fp and sp *)


val PSPEC_term =
	Term `PSPEC:CTL_STRUCTURE ->
       ((bool ** i4 |-> bool ** i32) # (bool ** i30 |-> bool ** i32) ->
        bool) #
       ((bool ** i4 |-> bool ** i32) # (bool ** i30 |-> bool ** i32) ->
        bool) ->
       ((bool ** i4 |-> bool ** i32) # (bool ** i30 |-> bool ** i32) -> 'a)
       ->
       ((bool ** i4 |-> bool ** i32) # (bool ** i30 |-> bool ** i32) -> 'b)
       #
       ('b -> 'c) #
       ((bool ** i4 |-> bool ** i32) # (bool ** i30 |-> bool ** i32) -> 'c)
       -> bool`;


fun mk_PSPEC ir (pre_st,post_st) (ins,outs) = 
  let 

      fun calculate_outs st (IRSyntax.PAIR (a,b)) =
              mk_pair (calculate_outs st a, calculate_outs st b)
       |  calculate_outs st exp =
              read_one_var st exp

      fun clean_pair (IRSyntax.PAIR (a,b)) =
              IRSyntax.PAIR (clean_pair a, clean_pair b)
       |  clean_pair (IRSyntax.REG r) = IRSyntax.REG r
       |  clean_pair (IRSyntax.MEM (r, off)) = IRSyntax.MEM (r, off)
       |  clean_pair _ = IRSyntax.NA

		val ins = trim_pair (clean_pair ins);
		val outs = trim_pair (clean_pair outs);

      (* the characteristic function *)
      val rules = mk_subst_rules (List.map (read_one_var pre_st) (IRSyntax.pair2list ins));
      val (initV,out_vars) = (mk_vars ins, mk_vars outs);
      val f_c = mk_pabs (initV, subst rules (calculate_outs post_st outs));  (* the charateristic function *)

      (* the pre-condition and the post-condition *)

      val st' = mk_var ("st", Type `:DSTATE`);

      (* the stack function *)
      val stk_f = mk_pabs (st', Term `T`);  
      val stk_tp = hd (tl (#2 (dest_type (type_of stk_f))));

      (* the projective specification *)
      val (in_f,out_f) = (mk_pabs (st', mk_mreads st' ins), mk_pabs (st', mk_mreads st' outs));
      val pspec = list_mk_comb (inst [{redex = alpha, residue = stk_tp}, 
				       {redex = beta, residue = type_of initV}, 
                                       {redex = gamma, residue = type_of out_vars}] (PSPEC_term),
                         [ir, mk_pair(stk_f, stk_f), stk_f, list_mk_pair[in_f,f_c,out_f]]);
  in
     pspec
  end;

(*---------------------------------------------------------------------------------*)
(*      Symbolic Simulation of Basic Blocks                                        *) 
(*---------------------------------------------------------------------------------*)
      
(* Given an basic block, the charateristic function on inputs and outputs are derived by symbolic simulation *)
(* and the context about unchanged variables is maintained                                                   *) 
(* Finally well_formed information is given                                                                  *)
(*
fun extract (annotatedIR.BLK (instL,{ins = ins, outs = outs, context = context, ...})) =
(instL, ins, outs, context);
val (instL, ins, outs, context) = extract pre_ir;
val (unchanged_list, _) = unchanged_lists_weak
val unchanged_list = emptyset
mk_blk_spec pre_ir unchanged_lists_weak
val stack_size = 1
*)




fun mk_blk_spec (annotatedIR.BLK (instL,{ins = ins, outs = outs, context = context, ...})) unchanged_list = 
  let 	
		val (blk, stack_size) = IRSyntax.convert_instL instL;
      val th = sim_stms blk;
      val t1 = concl th;
      val spec_terms = (#2 (strip_comb (lhs t1)), rhs t1);
		val blk_ir = el 1 (#1 spec_terms);
		val pre_st = el 2 (#1 spec_terms);
		val post_st = #2 spec_terms;
      val ir_abbr = mk_var ("ir", Type `:CTL_STRUCTURE`);

      val f_spec = mk_PSPEC blk_ir (pre_st,post_st) (ins,outs);
      val f_spec' = subst [{redex = blk_ir, residue = ir_abbr}] f_spec;

      val unchanged_term = list_mk_comb (Term`UNCHANGED`, [mk_unchanged_term unchanged_list, blk_ir]);

		val unchanged_thm = prove (unchanged_term, (* set_goal ([],unchanged_term) *)
			REWRITE_TAC[UNCHANGED_THM, th, EVERY_DEF] THEN
			BETA_TAC THEN
			REWRITE_TAC[read_thm, toREG_def, index_of_reg_def, FAPPLY_FUPDATE_THM, word4_distinct]);

      val used_stack_term = list_mk_comb (Term`USED_STACK`, [ term_of_int stack_size, blk_ir]);

		val stack_size_thm =
			let
				val nterm = mk_comb (Term `LIST_COUNT`, (term_of_int stack_size));
			in
				(REDEPTH_CONV num_CONV) nterm handle UNCHANGED => REFL nterm
			end

		val used_stack_thm = prove (used_stack_term, (* set_goal ([],used_stack_term) *)
			REWRITE_TAC [USED_STACK_THM, th, MAP, read_thm, Once stack_size_thm, LIST_COUNT_def] THEN
			SIMP_TAC list_ss [] THEN
			CONV_TAC WORDS_CONV THEN
			ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM])

			
      val unchanged_spec = list_mk_comb (Term`UNCHANGED_STACK`, [mk_unchanged_term unchanged_list, term_of_int stack_size, ir_abbr]);


      (* well_formedness *)
      val wf_spec = mk_comb (Term`WELL_FORMED`, ir_abbr);

      (* specifiction of functional correctness *)
      val fspec = mk_let (mk_abs (ir_abbr, list_mk_conj [f_spec', wf_spec, unchanged_spec]), blk_ir); 

      val spec = prove (fspec,   (* set_goal ([],fspec) *)
             SIMP_TAC std_ss [LET_THM, PSPEC_def, HSPEC_def, FORALL_DSTATE, BLOCK_IS_WELL_FORMED, read_thm, unchanged_thm, UNCHANGED_STACK_def, used_stack_thm] THEN
 				 SIMP_TAC list_ss [mread_def, toMEM_def, toREG_def, index_of_reg_def, read_thm, th] THEN
             CONV_TAC SIM_MEM_CONV THEN
             SIMP_TAC std_ss [pair_induction]
            )
				
   in
     (spec, th)
   end
 | mk_blk_spec _ _ = 
     raise Fail "mk_blk_spec: BLK is expected!";



(* Obtain the specification associated with pointers                               *)
fun get_p_spec spec =
  let
      val th0 = CONJUNCT1 (SIMP_RULE std_ss [LET_THM] spec);
      val (t0,t1) = strip_comb (concl th0)
  in
      List.nth (t1,1) 
  end


	fun make_unchanged_stack_term u_spec1 u_spec2 ir =
		let
			val stack_size1 = rand (rator u_spec1)
			val stack_size2 = rand (rator u_spec2)
			val stack_size = list_mk_comb (Term `MAX`, [stack_size1, stack_size2]);
			val body = rator (rator (u_spec1))
		in
			list_mk_comb (body, [stack_size, ir])
		end

(*---------------------------------------------------------------------------------*)
(*      Specification for Sequential Composition                                   *) 
(*---------------------------------------------------------------------------------*)

(* retrieve information from a PSPEC specification *)
fun get_spec_info spec = 
    let val f_spec = hd (strip_conj spec);
        val (_, [ir, ps, stk_f, fs]) = strip_comb f_spec;
        val (ps1,ps2) = dest_pair ps;
        val list0 = strip_pair fs;
        val (in_f, f_c, out_f) = (#2 (dest_abs (hd list0)), List.nth(list0,1), #2 (dest_abs (List.nth(list0,2))))
    in
       (ir, (ps1, ps2), stk_f, (in_f, f_c, out_f))
    end
     handle e => (print "get_spec_info: the input is not valid PSPEC and UNCHANGED"; Raise e);

(*
val (ir1_spec, ir1_wf, ir2_spec, ir2_wf) = 
((el 1 preL), (el 2 preL), (el 1 bodyL), (el 2 bodyL));*)

fun mk_sc_spec___pre ir1_spec ir1_wf ir2_spec ir2_wf = 
  let 
      val (ir1,(pre_p1,post_p1),stk_f,(ins1,f1,outs1)) = get_spec_info (concl ir1_spec);
      val (ir2,(pre_p2,post_p2),stk_f,(ins2,f2,outs2)) = get_spec_info (concl ir2_spec);

      (* SC (ir1, ir2) *)
      val sc_ir = list_mk_comb (Term`IL$SC`, [ir1, ir2]);
      val ir_abbr = mk_var ("ir", Type `:CTL_STRUCTURE`);
      val st = mk_var ("st", Type `:DSTATE`);
      val instance = list_mk_comb (Term`run_ir:CTL_STRUCTURE -> DSTATE -> DSTATE`, [sc_ir, st]);
      
      (* the characteristic function of SC *)
      val sc_f = combinSyntax.mk_o (f2,f1); 
		val sc_f_thm = (SIMP_CONV std_ss [combinTheory.o_DEF, pairTheory.LAMBDA_PROD] sc_f);
      val (in_f,out_f) = (mk_pabs (st,ins1), mk_abs (st,outs2));
      val out_f1 = mk_pabs (st, outs1);       
      val stk_tp = hd (tl (#2 (dest_type (type_of stk_f))));

      (* the SC specification *)
      val f_spec = list_mk_comb (inst [alpha |-> stk_tp, beta |-> type_of ins1, gamma |-> type_of outs2] (PSPEC_term), 
                                [sc_ir, mk_pair(pre_p1, post_p2), stk_f, list_mk_pair[in_f,sc_f,out_f]]);

      val f_th =  prove (f_spec,   (* set_goal ([],f_spec) *)
                        MATCH_MP_TAC PRJ_SC_RULE THEN
                        EXISTS_TAC post_p1 THEN EXISTS_TAC out_f1 THEN
                        SIMP_TAC std_ss [ir1_spec, ir2_spec, ir1_wf, ir2_wf] THEN
								MP_TAC ir2_spec THEN
								SIMP_TAC std_ss [PSPEC_def, HSPEC_def]
		        )
		val f_th = REWRITE_RULE [sc_f_thm] f_th

      val well_formed_spec = mk_comb (Term`WELL_FORMED`, sc_ir);
      val well_formed_th = prove (well_formed_spec,   (* set_goal ([],well_formed_spec) *)
                      ONCE_REWRITE_TAC [GSYM IR_SC_IS_WELL_FORMED] THEN
                      SIMP_TAC std_ss [ir1_wf, ir2_wf]
	        );
	in
		(f_th, well_formed_th, sc_ir)
	end;
	  
(*
val (ir1_spec, ir2_spec) = (spec1, spec2)
*)
fun mk_sc_spec ir1_spec ir2_spec unchanged_list = 
  let 
		val ir1_spec = (SIMP_RULE std_ss [LET_THM] ir1_spec)
		val ir2_spec = (SIMP_RULE std_ss [LET_THM] ir2_spec)
      val specL1 = CONJUNCTS ir1_spec
      val specL2 = CONJUNCTS ir2_spec

		val (ir_spec, ir_wf, sc_ir) =
			mk_sc_spec___pre (el 1 specL1) (el 2 specL1) (el 1 specL2) (el 2 specL2);

		val unchanged_spec = make_unchanged_stack_term (concl (el 3 specL1)) (concl (el 3 specL2)) sc_ir

      val unchanged_th = prove (unchanged_spec,   (* set_goal ([],unchanged_spec) *)
                      MATCH_MP_TAC IR_SC_UNCHANGED_STACK THEN
                      SIMP_TAC list_ss [ir1_spec, ir2_spec]
	        );

      val ir_abbr = mk_var ("ir", Type `:CTL_STRUCTURE`);
      val spec = subst [sc_ir |-> ir_abbr] (list_mk_conj [concl ir_spec, concl ir_wf, unchanged_spec]);
      val spec' = mk_let (mk_abs (ir_abbr, spec), sc_ir);

      val th =  prove (spec',   (* set_goal ([],spec') *)
			SIMP_TAC std_ss [LET_THM, ir_spec, ir_wf, unchanged_th]
		      )

(*
      val sc_th_term = mk_comb(mk_comb (Term`run_ir`,sc_ir), Term `(r, m):DSTATE`);
	   val sc_th =
			(SIMP_CONV std_ss [IR_SEMANTICS_SC, 
									ir1_spec, ir2_spec, ir1_th, ir2_th] THENC
			SIM_MEM_CONV) sc_th_term;*)


   in
      th
   end;

(*---------------------------------------------------------------------------------*)
(*      Specification for Function Calls                                           *) 
(*---------------------------------------------------------------------------------*)

fun compute_outL modifiedRegL =
    let val i = ref 0   
    in
        List.map (fn e => (i := !i - 1; IRSyntax.MEM (11, !i))) ([12, 11] @ (List.rev modifiedRegL))  (* neglect pc and lr *)
    end


fun mk_fc_spec (pre_spec, body_spec, post_spec, pre_th, post_th, unchanged_list) = 
	let
		val pre_spec = (SIMP_RULE std_ss [LET_THM] pre_spec)
		val body_spec = (SIMP_RULE std_ss [LET_THM] body_spec)
		val post_spec = (SIMP_RULE std_ss [LET_THM] post_spec)

      val preL = CONJUNCTS pre_spec;
      val bodyL = CONJUNCTS body_spec;
      val postL = CONJUNCTS post_spec;

		fun fix_body_spec pre_spec body_spec post_spec =
		let
			val (_,_,_,(_,_,outs_pre)) = get_spec_info (concl pre_spec);
			val (_,_,_,(ins_post,_,_)) = get_spec_info (concl post_spec);
			val (ir,(pre_p,post_p),stk_f,(ins,f,outs)) = get_spec_info (concl body_spec);

			fun extend_f f 0  = f |
				extend_f f n =
					let
						val (vars, body) = dest_pabs f;
						val newvar = genvar (Type `:DATA`);
						val body' = mk_pair (newvar,body);
						val vars' = mk_pair (newvar,vars);
						val f' = mk_pabs (vars', body')					
					in
						extend_f f' (n-1)
					end;
	
				
			val ins_l = length (strip_pair ins)
			val new_ins_l = length (strip_pair outs_pre)
			val f' = extend_f f (new_ins_l - ins_l)
	
			val st = mk_var ("st", Type `:DSTATE`);
			val arg' = list_mk_pair [mk_abs(st, outs_pre), f', mk_abs(st, ins_post)]
	      val stk_tp = hd (tl (#2 (dest_type (type_of stk_f))));

			val spec_term = list_mk_comb (inst [alpha |-> stk_tp, beta |-> type_of outs_pre, gamma |-> type_of ins_post] (PSPEC_term), 
											[ir, mk_pair(pre_p, post_p), stk_f, 
											 arg']);
		in
			(spec_term, ir)
		end

		val (body_spec_term, body_ir) = fix_body_spec pre_spec body_spec post_spec;

		val new_stack = rand (rator (concl (el 3 preL)))
		val body_stack = rand (rator (concl (el 3 bodyL)))
		val new_stack_size_thm =
			let
				val nterm = mk_comb (Term `LIST_COUNT`, new_stack);
			in
				(REDEPTH_CONV num_CONV) nterm handle UNCHANGED => REFL nterm
			end

		val body_PSPEC = prove (body_spec_term, (*set_goal ([], body_spec_term)*)
			MP_TAC (el 1 bodyL) THEN
			SIMP_TAC std_ss [PSPEC_def, HSPEC_def, mread_def] THEN
			DISCH_TAC THEN POP_ASSUM (fn t => ALL_TAC) THEN
			REPEAT STRIP_TAC THEN (

				MP_TAC (el 3 bodyL) THEN
				MATCH_MP_TAC UNCHANGED_STACK___READ_STACK_IMP THEN
				SIMP_TAC list_ss []
			));

		val bodyL = body_PSPEC :: (tl bodyL);


		val (ir_spec1, ir_wf1, _) =
			mk_sc_spec___pre (el 1 preL) (el 2 preL) (el 1 bodyL) (el 2 bodyL);

		val (ir_spec, ir_wf, sc_ir) =
			mk_sc_spec___pre ir_spec1 ir_wf1 (el 1 postL) (el 2 postL);
	
(*
      val sc_th_term = mk_comb(mk_comb (Term`run_ir`,sc_ir), Term `(r, m):DSTATE`);

	   val sc_th =
			(SIMP_CONV std_ss [IR_SEMANTICS_SC, 
									pre_th, post_th, body_th,
									pre_spec, body_spec, post_spec, ir_wf1] THENC
			SIM_MEM_CONV) sc_th_term;*)
		
		val sum_stack = numSyntax.mk_plus (numSyntax.mk_plus (new_stack, body_stack), numSyntax.zero_tm)
      val unchanged_spec = list_mk_comb (Term`UNCHANGED_STACK`, [mk_unchanged_term unchanged_list, sum_stack, sc_ir]);


		val common_rewrites = LIST_CONJ [pre_spec, body_spec, post_spec,
			pre_th, post_th];
		val common_rewrites = SIMP_RULE std_ss [UNCHANGED_STACK_def,
			WELL_FORMED_thm] common_rewrites;
      val unchanged_th = prove (unchanged_spec,   (* set_goal ([],unchanged_spec) *)							
							 
							 REWRITE_TAC [UNCHANGED_STACK_def] THEN
							 CONJ_TAC THENL [
								SIMP_TAC std_ss [UNCHANGED_THM, common_rewrites,
									Once IR_SEMANTICS_SC, Once IR_SEMANTICS_SC,
									WELL_FORMED_thm, GSYM RIGHT_FORALL_IMP_THM,	EVERY_MEM] THEN
								REPEAT GEN_TAC THEN
								(fn (a, g) =>
									let
										val (_, t1) = dest_imp g;
										val t2 = (lhs t1);
										val t3 = rand (rand (rator t2));
										val t4 = Term `?r'' m''. ^t3 = (r'', m'')`
										val thm = METIS_PROVE [pairTheory.PAIR] t4
									in
										ASSUME_TAC thm (a,g)
									end) THEN
								FULL_SIMP_TAC std_ss [common_rewrites] THEN
								SPEC_TAC (Term `r:MREG`, Term `r:MREG`) THEN
								SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM, toREG_def, index_of_reg_def, read_thm] THEN
								CONV_TAC SIM_MEM_CONV THEN
								
								(fn (a, g) =>
								let
									val thm =CONJUNCT1 (
									REWRITE_RULE [UNCHANGED_STACK_def] (el 3 bodyL));
									val thm2 = SIMP_RULE std_ss [UNCHANGED_THM,
									EVERY_MEM, GSYM RIGHT_FORALL_IMP_THM] thm
									val (r,m) = dest_pair (rand (lhs (hd a)))
									val thm3 = SPECL [Term `r:MREG`, r, m] thm2;
									val thm4 = GEN (Term `r:MREG`) thm3;
								in 
									MP_TAC thm4 (a,g)
								end) THEN
								ASM_REWRITE_TAC[] THEN
									
								SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM, toREG_def, index_of_reg_def, read_thm] THEN
								CONV_TAC SIM_MEM_CONV THEN
								METIS_TAC[],

								MATCH_MP_TAC IR_SC_USED_STACK___FC_CASE1 THEN
								CONJ_TAC THENL [
									MATCH_MP_TAC IR_SC_USED_STACK___FC_CASE2 THEN
									SIMP_TAC std_ss [common_rewrites, WELL_FORMED_thm, read_thm] THEN
									CONV_TAC SIM_MEM_CONV THEN
									ONCE_REWRITE_TAC[GSYM n2w_mod] THEN
									SIMP_TAC std_ss [WORD_ADD_0, dimword_32, dimword_4],
									

									SIMP_TAC std_ss [common_rewrites, WELL_FORMED_thm, read_thm,
									Once IR_SEMANTICS_SC] THEN

									ASSUME_TAC (
										CONJUNCT1 (
										REWRITE_RULE [UNCHANGED_STACK_def] (el 3 bodyL))) (*body UNCHANGED*) THEN
									FULL_SIMP_TAC list_ss [UNCHANGED_THM, EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM, toREG_def, index_of_reg_def] THEN
									CONV_TAC SIM_MEM_CONV THEN
									ONCE_REWRITE_TAC[GSYM n2w_mod] THEN
									SIMP_TAC std_ss [WORD_ADD_0, dimword_32, dimword_4]
								]
							]
	        );

      val ir_abbr = mk_var ("ir", Type `:CTL_STRUCTURE`);
      val spec = subst [sc_ir |-> ir_abbr] (list_mk_conj [concl ir_spec, concl ir_wf, unchanged_spec]);
      val spec' = mk_let (mk_abs (ir_abbr, spec), sc_ir);

      val th =  prove (spec',   (* set_goal ([],spec') *)
			SIMP_TAC std_ss [LET_THM, unchanged_th, ir_spec, ir_wf]
		      )
	in
     th
	end;

(*---------------------------------------------------------------------------------*)
(*      Specification for input/output matching                                    *) 
(*---------------------------------------------------------------------------------*)

(*
PROJ_POST_RULE
 |- !ir in_f out_f convert_f.
         PSPEC ir (pre_p,post_p) (in_f,f,out_f) ==>
         PSPEC ir (pre_p,post_p) (in_f,convert_f o f,convert_f o out_f) : thm


fun mk_match_spec spec in_f2 = 
  let 
      
      val (_, (pre_p1, post_p1), (in_f1, f_c, out_f1), _) = get_spec_info spec;
      

   in
        th
   end;
*)



(*---------------------------------------------------------------------------------*)
(*      Specification for Tail Recursion                                           *) 
(*---------------------------------------------------------------------------------*)

(* Given a TR, the charateristic function on inputs and outputs are derived by the TR_RULE *)
(* and the context about unchanged variables is maintained                                 *) 

fun convert_cond (exp1, rop, exp2) =
  let
    val cond_t0 = list_mk_pair [IRSyntax.convert_reg exp1, 
				IRSyntax.convert_rop rop, 
				IRSyntax.convert_exp exp2];
  in
    cond_t0
  end
  handle e => (print "mk_cond: errors occur while converting the condition"; Raise e);

fun strip_pair2 t =
  if is_pair t then List.foldl (fn (t0,L0) => L0 @ (strip_pair2 t0)) [] (strip_pair t)
  else [t];


fun mk_cj_cond cond_t ins =
  let 
    val st = mk_var ("st", Type `:DSTATE`);
    val instance = list_mk_comb (Term`eval_il_cond`, [cond_t, st]);

    val read_const_th = prove (Term`!st v. read st (WCONST v) = v`, SIMP_TAC std_ss [FORALL_DSTATE, read_thm]); 

    val th0 = REWRITE_CONV [ARMCompositionTheory.eval_cond_def,
                            ILTheory.eval_il_cond_def,
                            ILTheory.translate_condition_def,
                            ILTheory.toREG_def,
                            ILTheory.toEXP_def,
                            ILTheory.index_of_reg_def] instance;
    val th1 = REWRITE_RULE [read_const_th] th0;
    val th1 = WORDS_RULE th1;
    val instance1 = rhs (concl th1);

    val rules = mk_subst_rules (List.map (fn t0 => rhs (concl (REWRITE_CONV [mread_def, toMEM_def, toREG_def, index_of_reg_def] t0))) (strip_pair2 ins));
    val cj_cond = subst rules instance1  (* the condition function *)
  in
     cj_cond
  end

fun mk_cond_f cond_t ins =                  (* the condition function *)
    let 
        val rules = mk_subst_rules (strip_pair2 ins)
    in 
        mk_pabs (subst rules ins, mk_cj_cond cond_t ins)
    end

fun guessR2 tp = 
    let val tp1 = List.nth(#2 (dest_type tp),1)
    in
        (Term`(measure (w2n o FST)):(word32#word32)->(word32#word32)->bool`)
    end

fun cheat_tac (asl,g) = ACCEPT_TAC(ASSUME g) (asl,g);

fun mk_tr_spec cond body_spec = 
  let 
      val specL = strip_conj (concl (SIMP_RULE std_ss [LET_THM] body_spec));
      val (body_ir,(pre_p,post_p),stk_f,(ins,f,outs)) = get_spec_info (hd specL);

      val t_cond = convert_cond cond;
      val tr_ir = list_mk_comb (Term`TR`, [t_cond, body_ir]);
      val ir_abbr = mk_var ("ir", Type `:CTL_STRUCTURE`);
      val st = mk_var ("st", Type `:DSTATE`);
      val instance = list_mk_comb (Term`run_ir:CTL_STRUCTURE -> DSTATE -> DSTATE`, [tr_ir, st]);
      
      val initV = #1 (dest_pabs f);

      val cond_f_0 = mk_cond_f t_cond ins;
      val cond_f = combinSyntax.mk_o (Term `$~:bool->bool`, cond_f_0);

      val tr_f = list_mk_comb (inst [alpha |-> type_of initV] (Term`WHILE:('a -> bool) -> ('a -> 'a) -> 'a -> 'a`), [cond_f, f]);
      val prj_f = mk_pabs (st,ins);
      val stk_tp = hd (tl (#2 (dest_type (type_of stk_f))));
       
      (* well_founded relation: WF (\st1 st0. ~eval_cond cond st0 /\ (st1 = run_ir ir st0)) *)
      
      val (st0,st1) = (mk_var ("st0", Type `:DSTATE`), mk_var ("st1", Type `:DSTATE`));
      val wf_t0 = mk_neg (list_mk_comb (Term`eval_il_cond`, [t_cond, st0]));
      val wf_t1 = mk_eq (st1, list_mk_comb (Term`run_ir`, [body_ir, st0]));
      val wf_t2 = list_mk_abs ([st1,st0],mk_conj(wf_t0,wf_t1));
      val wf_t3 = mk_comb (Term`WF:(DSTATE->DSTATE->bool)->bool`, wf_t2);
      val wf_th = prove (wf_t3, (* set_goal ([],wf_t3) *)
                         MATCH_MP_TAC (INST_TYPE [alpha |-> type_of initV] WF_TR_LEM_2) THEN
                         EXISTS_TAC prj_f THEN EXISTS_TAC f THEN EXISTS_TAC cond_f_0 THEN
                         SIMP_TAC std_ss [SIMP_RULE std_ss [PSPEC_def, HSPEC_def, LET_THM] body_spec] THEN
                         SIMP_TAC std_ss [ARMCompositionTheory.eval_cond_def, FORALL_DSTATE, mread_def,
                                         eval_il_cond_def, translate_condition_def,  toEXP_def,
                                         index_of_reg_def,toREG_def, toMEM_def, read_thm] THEN
                         WORDS_TAC THEN 
                         SIMP_TAC std_ss [] THEN
                         MATCH_MP_TAC (INST_TYPE [alpha |-> type_of initV] WF_TR_LEM_3) THEN
                         (let val r = guessR2 (type_of initV) in     
                              WF_REL_TAC `^r` THEN
                              WORDS_TAC THEN
                              RW_TAC std_ss [WORDS_RULE 
                                (INST_TYPE [alpha |-> Type `:i32`] WORD_PRED_THM)]
                          end
                          handle e => (print "fail to prove totalness, add statement into assumption list"; cheat_tac)
                         )
                         );
      (* the characteristic function *)
      val f_spec = list_mk_comb (inst [alpha |-> stk_tp, beta |-> type_of initV, gamma |-> type_of initV] (PSPEC_term), 
                                [tr_ir, mk_pair(pre_p, post_p), stk_f, list_mk_pair[prj_f,tr_f, prj_f]]);

      val f_th =  prove (f_spec,   (* set_goal ([],f_spec) *)
                        ASSUME_TAC wf_th THEN
                        MATCH_MP_TAC PRJ_TR_RULE THEN
                        SIMP_TAC std_ss [SIMP_RULE std_ss [LET_THM] body_spec] THEN
                        STRIP_TAC THENL [
                            RW_TAC std_ss [],
                            SIMP_TAC std_ss [ARMCompositionTheory.eval_cond_def, FORALL_DSTATE, mread_def, eval_il_cond_def, translate_condition_def,
                                         index_of_reg_def, toREG_def, toEXP_def, toMEM_def, read_thm] THEN
                            WORDS_TAC THEN
                            SIMP_TAC std_ss []
                            ]
		        )

      (* Well-formedness *)

      val well_formed_spec = mk_comb (Term`WELL_FORMED`, tr_ir);
      val well_formed_th = prove (well_formed_spec,   (* set_goal ([],well_formed_spec) *)
                      ASSUME_TAC wf_th THEN
                      MATCH_MP_TAC WELL_FORMED_TR_RULE THEN
                      SIMP_TAC std_ss [SIMP_RULE std_ss [LET_THM] body_spec] THEN
                      RW_TAC std_ss []
	        );

      (* unchanged *)
      val unchanged_spec = mk_comb (rator (el 3 specL), tr_ir);
      val unchanged_th = prove (unchanged_spec,   (* set_goal ([],unchanged_spec) *)
                      MATCH_MP_TAC UNCHANGED_STACK_TR_RULE THEN
                      SIMP_TAC list_ss [well_formed_th, SIMP_RULE std_ss [LET_THM] body_spec]
	        );


      val spec = subst [tr_ir |-> ir_abbr] (list_mk_conj [f_spec, well_formed_spec, unchanged_spec]);
      val spec' = mk_let (mk_abs (ir_abbr, spec), tr_ir);

      val th =  prove (spec',   (* set_goal ([],spec') *)
			SIMP_TAC std_ss [f_th, well_formed_th, unchanged_th, LET_THM]
		      )

(*
      val tr_th_term = mk_comb(mk_comb (Term`run_ir`,tr_ir), Term `(r, m):DSTATE`);

	   val tr_th =
			(SIMP_CONV std_ss [IR_SEMANTICS_TR, GSYM WELL_FORMED_thm,
									well_formed_th] THENC
			SIM_MEM_CONV) tr_th_term;*)

   in
      th
   end;


(*---------------------------------------------------------------------------------*)
(*      Specification for Conditional Jumps                                        *) 
(*---------------------------------------------------------------------------------*)
(*
val (ir1_spec, ir2_spec) = (spec1, spec2);
*)

fun mk_cj_spec cond ir1_spec ir2_spec unchanged_list = 
  let 
      val (specL1,specL2) = (strip_conj (concl (SIMP_RULE std_ss [LET_THM] ir1_spec)),strip_conj (concl (SIMP_RULE std_ss [LET_THM] ir2_spec)));
      val (ir1,(pre_p1,post_p1),stk_f,(ins1,f1,outs1)) = get_spec_info (hd specL1);
      val (ir2,(pre_p2,post_p2),stk_f,(ins2,f2,outs2)) = get_spec_info (hd specL2);
      val (spec1_thm, spec2_thm) = (SIMP_RULE std_ss [LET_THM] ir1_spec, SIMP_RULE std_ss [LET_THM] ir2_spec);

      val t_cond = convert_cond cond;
      val cj_ir = list_mk_comb (Term`CJ`, [t_cond, ir1, ir2]);
      val ir_abbr = mk_var ("ir", Type `:CTL_STRUCTURE`);
      val st = mk_var ("st", Type `:DSTATE`);
      val instance = list_mk_comb (Term`run_ir:CTL_STRUCTURE -> DSTATE -> DSTATE`, [cj_ir, st]);
      
      val initV = #1 (dest_pabs f1);
      val cj_cond = mk_cond_f t_cond ins1;
      val cj_f = mk_pabs(initV, list_mk_comb (inst [alpha |-> type_of outs1] (Term`COND:bool->'a->'a->'a`), 
                       [mk_comb(cj_cond,initV), mk_comb(f1,initV), mk_comb(f2,initV)]));

      val (in_f,out_f) = (mk_pabs (st,ins1), mk_abs (st,outs2));
      val stk_tp = hd (tl (#2 (dest_type (type_of stk_f))));

      (* the characteristic function *)
      val f_spec = list_mk_comb (inst [alpha |-> stk_tp, beta |-> type_of ins1, gamma |-> type_of outs2] (PSPEC_term), 
                                [cj_ir, mk_pair(pre_p1,post_p1), stk_f, list_mk_pair[in_f,cj_f,out_f]]);

      val f_th =  prove (f_spec,   (* set_goal ([],f_spec) *)
                        MATCH_MP_TAC (GEN_ALL (SIMP_RULE std_ss [LAMBDA_PROD] (INST_TYPE [beta |-> type_of initV] 
                                  (SPEC_ALL PRJ_CJ_RULE)))) THEN
                        SIMP_TAC std_ss [spec1_thm, spec2_thm] THEN
                        SIMP_TAC std_ss [ARMCompositionTheory.eval_cond_def,
                         ILTheory.eval_il_cond_def, 
                         ILTheory.translate_condition_def,
                         FORALL_DSTATE, mread_def, 
                                         index_of_reg_def, toREG_def,
                                         toEXP_def, read_thm, GSYM PFORALL_THM] THEN
                        WORDS_TAC THEN
                        SIMP_TAC std_ss []
		        )

      (* well-formedness *)

      val well_formed_spec = mk_comb (Term`WELL_FORMED`, cj_ir);
      val well_formed_th = prove (well_formed_spec,   (* set_goal ([],well_formed_spec) *)
                      REWRITE_TAC [GSYM IR_CJ_IS_WELL_FORMED] THEN
                      SIMP_TAC std_ss [spec1_thm, spec2_thm]
	        );

      (* unchanged *)

      val unchanged_spec = make_unchanged_stack_term (el 3 specL1) (el 3 specL2) cj_ir;
      val unchanged_th = prove (unchanged_spec,   (* set_goal ([],unchanged_spec) *)
      	MATCH_MP_TAC IR_CJ_UNCHANGED_STACK THEN
         SIMP_TAC std_ss [spec1_thm, spec2_thm]
	   );


      val spec = list_mk_conj [f_spec, well_formed_spec, unchanged_spec];

      val th =  prove (spec,   (* set_goal ([],spec) *)
			SIMP_TAC std_ss [f_th, well_formed_th, unchanged_th, LET_THM]
		      )
(*
      val cj_th_term = mk_comb(mk_comb (Term`run_ir`,cj_ir), Term `(r, m):DSTATE`);
	   val cj_th =
			(SIMP_CONV std_ss [IR_SEMANTICS_CJ, 
									spec1_thm, spec2_thm,
									ir1_th, ir2_th] THENC
			SIM_MEM_CONV) cj_th_term;*)
   in
      th
   end;


(*---------------------------------------------------------------------------------*)
(*      Application of the SHUFFLE rule                                            *) 
(*---------------------------------------------------------------------------------*)
 
fun mk_shuffle_spec spec (in_f', g) = 
  let 
      val spec_thm = SIMP_RULE std_ss [LET_THM] spec;
      val (ir,(pre_p,post_p),stk_f,(ins,f,outs)) = get_spec_info (hd (strip_conj (concl spec_thm)));
      val st = mk_var ("st", Type `:DSTATE`);
      val (in_f,out_f) = (mk_pabs(st,ins), mk_pabs(st,outs));

      (*  (g o in_f' = f o in_f)  *)
      val (g_tp,f_tp) = (#2 (dest_type (type_of g)), #2 (dest_type (type_of f)));
      val g_com = list_mk_comb (inst [alpha |-> hd g_tp, beta |-> hd (tl g_tp), gamma |-> Type`:DSTATE`] (Term`$o`), [g,in_f']);
      val f_com = list_mk_comb (inst [alpha |-> hd f_tp, beta |-> hd (tl f_tp), gamma |-> Type`:DSTATE`] (Term`$o`), [f,in_f]);
      val shuffle_th = prove (mk_eq(g_com,f_com),   (* set_goal ([],(mk_eq(g_com,f_com))) *)
                         SIMP_TAC std_ss [FUN_EQ_THM, FORALL_DSTATE, LET_THM, read_thm] THEN
			 SIMP_TAC list_ss [mread_def, toMEM_def, toREG_def, index_of_reg_def, read_thm] THEN
                         WORDS_TAC THEN
                         SIMP_TAC std_ss [pair_induction]
          );

      val fspec = subst [f |-> g, in_f |-> in_f'] (concl spec_thm);

      val spec = prove (fspec,   (* set_goal ([],fspec) *)
             SIMP_TAC std_ss [spec_thm] THEN
             MATCH_MP_TAC PRJ_SHUFFLE_RULE2 THEN
	     EXISTS_TAC in_f' THEN EXISTS_TAC g THEN
             RW_TAC std_ss [spec_thm, shuffle_th]
            )
   in
        spec
   end;

(*---------------------------------------------------------------------------------*)
(*      Application of the PUSH rule                                            *) 
(*---------------------------------------------------------------------------------*)
 
fun mk_push_spec spec = 
  let 
      val spec_thm = SIMP_RULE std_ss [LET_THM] spec;
      val (ir,(pre_p,post_p),stk_f,(ins,f,outs)) = get_spec_info (hd (strip_conj (concl spec_thm)));
      val st = mk_var ("st", Type `:DSTATE`);
      val (in_f,out_f) = (mk_pabs(st,ins), mk_pabs(st,outs));
      val (g,in_f') = (f,in_f);

      (*  (g o in_f' = f o in_f)  *)
      val (g_tp,f_tp) = (#2 (dest_type (type_of g)), #2 (dest_type (type_of f)));
      val g_com = list_mk_comb (inst [alpha |-> hd g_tp, beta |-> hd (tl g_tp), gamma |-> Type`:DSTATE`] (Term`$o`), [g,in_f']);
      val f_com = list_mk_comb (inst [alpha |-> hd f_tp, beta |-> hd (tl f_tp), gamma |-> Type`:DSTATE`] (Term`$o`), [f,in_f]);
      val push_th = prove (mk_eq(g_com,f_com),   (* set_goal ([],(mk_eq(g_com,f_com))) *)
                         SIMP_TAC std_ss [FUN_EQ_THM, FORALL_DSTATE, LET_THM, read_thm] THEN
			 SIMP_TAC list_ss [mread_def, toMEM_def, toREG_def, index_of_reg_def, read_thm] THEN
                         WORDS_TAC THEN
                         SIMP_TAC std_ss [pair_induction]
          );

      val fspec = subst [f |-> g, in_f |-> in_f'] (concl spec_thm);

      val spec = prove (fspec,   (* set_goal ([],fspec) *)
             SIMP_TAC std_ss [spec_thm] THEN
             MATCH_MP_TAC PRJ_PUSH_RULE THEN
	     EXISTS_TAC in_f' THEN EXISTS_TAC g THEN
             RW_TAC std_ss [spec_thm, push_th]
            )
   in
        spec
   end;

(*---------------------------------------------------------------------------------*)
(*      Application of the POP rule                                            *) 
(*---------------------------------------------------------------------------------*)
 
fun mk_pop_spec spec = 
  let 
      val spec_thm = SIMP_RULE std_ss [LET_THM] spec;
      val (ir,(pre_p,post_p),stk_f,(ins,f,outs)) = get_spec_info (hd (strip_conj (concl spec_thm)));
      val st = mk_var ("st", Type `:DSTATE`);
      val (in_f,out_f) = (mk_pabs(st,ins), mk_pabs(st,outs));
      val (g,in_f') = (f,in_f);

      (*  (g o in_f' = f o in_f)  *)
      val (g_tp,f_tp) = (#2 (dest_type (type_of g)), #2 (dest_type (type_of f)));
      val g_com = list_mk_comb (inst [alpha |-> hd g_tp, beta |-> hd (tl g_tp), gamma |-> Type`:DSTATE`] (Term`$o`), [g,in_f']);
      val f_com = list_mk_comb (inst [alpha |-> hd f_tp, beta |-> hd (tl f_tp), gamma |-> Type`:DSTATE`] (Term`$o`), [f,in_f]);
      val pop_th = prove (mk_eq(g_com,f_com),   (* set_goal ([],(mk_eq(g_com,f_com))) *)
                         SIMP_TAC std_ss [FUN_EQ_THM, FORALL_DSTATE, LET_THM, read_thm] THEN
			 SIMP_TAC list_ss [mread_def, toMEM_def, toREG_def, index_of_reg_def, read_thm] THEN
                         WORDS_TAC THEN
                         SIMP_TAC std_ss [pair_induction]
          );

      val fspec = subst [f |-> g, in_f |-> in_f'] (concl spec_thm);

      val spec = prove (fspec,   (* set_goal ([],fspec) *)
             SIMP_TAC std_ss [spec_thm] THEN
             MATCH_MP_TAC PRJ_POP_RULE THEN
	     EXISTS_TAC in_f' THEN EXISTS_TAC g THEN
             RW_TAC std_ss [spec_thm, pop_th]
            )
   in
        spec
   end;


(*---------------------------------------------------------------------------------*)
(*      Forward Reasoning                                                          *) 
(*---------------------------------------------------------------------------------*)

(*
fun extract (annotatedIR.SC (ir1, ir2, info)) = (ir1, ir2, info);
val (ir1, ir2, info) = extract f_ir;
val (ir1, ir2, info) = extract ir2;

fun extract (annotatedIR.CALL (fname, pre_ir, body_ir, post_ir,info)) = (fname, pre_ir, body_ir, post_ir, info);
val (fname, pre_ir, body_ir, post_ir, info) = extract ir1

fun extract (annotatedIR.SC (ir1, ir2, info)) = (ir1, ir2, info);
val (ir1, ir2, info) = extract ir1


fun extract (annotatedIR.TR (cond, body, {fspec = fspec1, ins = ins1, outs = outs1, context = contextL, ...})) = (cond, body)
val (cond, body) = extract ir1

fun extract (annotatedIR.CJ (cond, ir1, ir2, {fspec = fspec1, ins = ins1, outs = outs1, context = contextL, ...})) = (cond, ir1, ir2)
val (cond, ir1, ir2) = extract ir1
*)


fun fwd_reason (annotatedIR.BLK blk_ir) unchanged_list =
      #1 (mk_blk_spec (annotatedIR.BLK blk_ir) unchanged_list)

 |  fwd_reason (annotatedIR.SC (ir1, ir2, info)) unchanged_list =
      let 
			 val spec1 = fwd_reason ir1 unchanged_list;
          val spec2 = fwd_reason ir2 unchanged_list;
      in
          mk_sc_spec spec1 spec2 unchanged_list
      end

 |  fwd_reason (annotatedIR.TR (cond, body, {fspec = fspec1, ins = ins1, outs = outs1, context = contextL, ...})) unchanged_list = 
      let val body_spec = fwd_reason body unchanged_list
      in
          mk_tr_spec cond body_spec
      end
 |  fwd_reason (annotatedIR.CJ (cond, ir1, ir2, {fspec = fspec1, ins = ins1, outs = outs1, context = contextL, ...})) unchanged_list =
		let
			val spec1 = fwd_reason ir1 unchanged_list;
         val spec2 = fwd_reason ir2 unchanged_list;
		in
			mk_cj_spec cond spec1 spec2 unchanged_list
		end

 |  fwd_reason (annotatedIR.CALL (fname, pre_ir, body_ir, post_ir,info)) unchanged_list =
      let 
			 val emptyset = Binaryset.empty Int.compare;
			 val f_unchanged_list = mk_unchanged_set fname;
          val (pre_spec, pre_th) = mk_blk_spec pre_ir emptyset;
          val body_spec = fwd_reason body_ir f_unchanged_list;
          val (post_spec, post_th) = mk_blk_spec post_ir emptyset;
      in
          mk_fc_spec (pre_spec, body_spec, post_spec, pre_th, post_th, unchanged_list)
      end

 |  fwd_reason _ _ = 
      raise Fail "fwd_reason: unsupported IR strcuture"
 ;

(*---------------------------------------------------------------------------------*)
(*      Equivalence between the original function and the spec function            *) 
(*---------------------------------------------------------------------------------*)
fun restore_f_TAC defs =
		SIMP_TAC std_ss [FUN_EQ_THM, FORALL_PROD] THEN
		REPEAT GEN_TAC THEN

		SIMP_TAC std_ss defs THEN
		REPEAT (CHANGED_TAC (FIRST [CHANGED_TAC (SIMP_TAC std_ss ([LET_THM, WORD_ADD_ASSOC] @ defs)), WORDS_TAC])) THEN
		REPEAT (CHANGED_TAC (FIRST [CHANGED_TAC (SIMP_TAC std_ss ([LET_THM, GSYM WORD_ADD_ASSOC] @ defs)), WORDS_TAC])) THEN
		METIS_TAC[WORD_ADD_COMM, WORD_AND_COMM, WORD_OR_COMM, WORD_XOR_COMM];



fun restore_f spec defs prove_equiv =
  let
      val th0 = CONJUNCT1 (SIMP_RULE std_ss [LET_THM] spec);
      val [in_f,spec_f,out_f] = strip_pair (List.nth (#2 (strip_comb (concl th0)),3));
      val sfl_f_const = #1 (strip_comb (lhs ((concl o SPEC_ALL) (hd defs))));
      val eq_stat = mk_eq (spec_f, sfl_f_const);		
      val eq_th = if (prove_equiv) then 
			(print "Proving equivalence with input function\n";
			 prove(eq_stat, restore_f_TAC defs) handle _ =>
			  let
				  val _ = print "! Equivalence proof between original function and\n";
				  val _ = print "! derived program semantics failed!\n\n";
			  in
				  ASSUME eq_stat
			  end)
			else ASSUME eq_stat;
  in
      eq_th
  end;


(*---------------------------------------------------------------------------------*)
(*      Display the theorem at the level of ARM flat code                          *) 
(*---------------------------------------------------------------------------------*)

fun f_correct spec =
  let
      val th0 = CONJUNCT1 (SIMP_RULE std_ss [LET_THM] spec);
      val th1 = SIMP_RULE std_ss [PSPEC_def, HSPEC_def, run_ir_def] th0;
      val f = let val t0 = concl (SPEC_ALL th1)
                  val (assm,f_spec) = 
                       let val (assm, t1) = dest_imp t0 
                       in (assm,#2 (dest_conj t1))
                       end handle e => (Term`T`,t0)
              in
                    mk_imp (assm, f_spec)
              end
      val th2 = GEN_ALL (prove (f, SIMP_TAC std_ss [th1]));
      val th3 = SIMP_RULE std_ss [translate_def, translate_assignment_def, toEXP_def, toREG_def, toMEM_def, index_of_reg_def, translate_condition_def] th2;
      val th4 = SIMP_RULE list_ss [ARMCompositionTheory.mk_SC_def, ARMCompositionTheory.mk_CJ_def, ARMCompositionTheory.mk_TR_def] th3
      val th5 =  SIMP_RULE std_ss [GSYM proper_def] th4
      val th6 =  WORDS_RULE th5
  in
      th6
  end;
     

fun f_correct_ir spec =
  let
      val th0 = CONJUNCT1 (SIMP_RULE std_ss [LET_THM] spec);
      val th1 = SIMP_RULE std_ss [PSPEC_def, HSPEC_def] th0;
      val f = let val t0 = concl (SPEC_ALL th1)
                  val (assm,f_spec) = 
                       let val (assm, t1) = dest_imp t0 
                       in (assm,#2 (dest_conj t1))
                       end handle e => (Term`T`,t0)
              in
                    mk_imp (assm, f_spec)
              end
      val th2 = GEN_ALL (prove (f, SIMP_TAC std_ss [th1]));
      val th3 = SIMP_RULE std_ss [toEXP_def, toREG_def, toMEM_def, index_of_reg_def] th2;
      val th4 = SIMP_RULE list_ss [] th3
      val th5 =  SIMP_RULE std_ss [GSYM proper_def] th4
      val th6 =  WORDS_RULE th5
  in
      th6
  end;


(*---------------------------------------------------------------------------------*)
(*      Print out                                                                  *) 
(*---------------------------------------------------------------------------------*)

(* Extract the IR tree from the specification and print it out *)

fun extract_ir spec =
    let
       val (f_name, _, (f_args,f_ir,f_outs), _, _, _) = spec;
    in
      (print ("  Name              : " ^ f_name ^ "\n");
       print ("  Arguments         : " ^ (IRSyntax.format_exp f_args) ^ "\n");
       print ("  Returns           : " ^ (IRSyntax.format_exp f_outs) ^ "\n");
       print  "  Body: \n";
       annotatedIR.printIR (annotatedIR.merge_ir f_ir)
      )
    end

(* Extract the ARM instruction list from the specification and print it out *)

fun extract_arm spec =
    let 
       val (f_name, _, (f_args,_,f_outs), _, stat0, _, _, _, _) = spec;
       val stat1 = let val t0 = concl (SPEC_ALL stat0)
                   in if is_imp t0 then #2 (dest_imp t0) else t0
		   end
       val stms = find_term (fn t => type_of t = Type `:INST list`) stat1;
       val stms1 = preARMSyntax.dest_arm stms
    in          
      (print ("  Name              : " ^ f_name ^ "\n");
       print ("  Arguments         : " ^ (IRSyntax.format_exp f_args) ^ "\n");
       print ("  Returns           : " ^ (IRSyntax.format_exp f_outs) ^ "\n");
       print  "  Body: \n";
       Assem.printInsts stms1
      )
    end

(*---------------------------------------------------------------------------------*)
(*      Interface                                                                  *) 
(*---------------------------------------------------------------------------------*)

(* To make the initial value of fp or sp unspecified, assign it a negative integer *)
(* For example, init_fp = ~1 will lead to st<MR R11> = ARB                         *)

(*val init_fp = ref (100);*)
val init_sp = ref (~1);

fun mk_pre_p sp_v = 
    if (!init_sp < 0) then mk_pabs (mk_var ("st", Type `:DSTATE`), Term`T`)
    else
      let val st = mk_pair (mk_var ("regs", Type `:num |-> DATA`), mk_var ("mem", Type `:num |-> DATA`));
          val (fp',sp') = (read_one_var st (IRSyntax.REG 11), read_one_var st (IRSyntax.REG 13));
          fun convert_pt v = if v < 0 then inst [alpha |-> Type `:DATA`] (Term `ARB`) else mk_comb (Term `n2w:num->word32`, term_of_int v)
      in  mk_pabs (st, mk_conj ( mk_eq(fp', convert_pt (!init_sp)), mk_eq(sp', convert_pt (!init_sp)))) (* Initially fp = sp *)
      end;

(*---------------------------------------------------------------------------------*)
(*Preprocess definition to eliminate ugly constants                                *)
(*---------------------------------------------------------------------------------*)
      
fun wordsplit t =
  let
    fun term2Arbnum t =
      let
        val t = mk_comb (Term `w2n:word32->num`, t)
        val t = rhs (concl (EVAL t));
        val n = numLib.dest_numeral t;
      in
        n
      end;

    fun arbnum2term n =
      let
        val t = numLib.mk_numeral n;
        val t = mk_comb (Term `n2w:num->word32`, t)
        val t = rhs (concl (EVAL t));
      in
        t
      end;


    fun remove_zero n c =
      let
        val (n1, n2) = (Arbnum.divmod (n, Arbnum.fromInt 4))
      in
        if (n2 = Arbnum.zero) then
          remove_zero n1 (Arbnum.plus1 c)
        else
          (n, c)
      end;
    

    fun wordsplit_internal (n:num) l =
      if (n = Arbnum.zero) then 
        if (l = []) then [n] else l
      else  
      let
        val (n_div, n_mod) = remove_zero n Arbnum.zero;
        val n' = Arbnum.mod (n_div, Arbnum.fromInt 256);
        val n' = Arbnum.* (n', Arbnum.pow (Arbnum.fromInt 4, n_mod));
        val m = Arbnum.- (n, n');
      in
        wordsplit_internal m (n'::l)
      end;

    val l = wordsplit_internal (term2Arbnum t) [];
    val l = map arbnum2term l;
  in
    l
  end;

fun needs_split t = not (length(wordsplit t) = 1)

fun WORD_EVAL_CONV t =
  if ((wordsSyntax.is_word_type(type_of t)) andalso (free_vars t = [])) then
    (CHANGED_CONV EVAL t) else raise ERR "WORD_EVAL_CONV" ""


fun DATA_RESTRICT_CONV t =
  if (wordsSyntax.is_n2w t andalso needs_split t) then
    let
      val l = wordsplit t;
      val (h, l) = (hd l, tl l);
      val new_t = foldl (fn (x, y) => mk_comb (mk_comb (Term `($!!):word32->word32->word32`, x), y)) h l;
    in
      GSYM (WORDS_CONV new_t)
    end
  else raise ERR "DATA_RESTRICT_CONV" ""



val extra_defs = ref [DECIDE (Term `T`)];

fun preprocess_def def =
  CONV_RULE ((DEPTH_CONV WORD_EVAL_CONV) THENC (DEPTH_CONV DATA_RESTRICT_CONV)) def


(*val prog = fact_def;
  val prog = def6
  val prove_equiv = false*)

fun pp_compile prog prove_equiv = 
  let  
      val def = preprocess_def prog;
      val (f_name, f_type, (f_args,f_ir,f_outs), defs) = funCall.link_ir def;
		val unchanged_list = mk_unchanged_set f_name;
      val f_spec0 = fwd_reason f_ir unchanged_list;
      val f_spec1 = (SIMP_RULE std_ss [restore_f f_spec0 defs prove_equiv] f_spec0)
      val thm_list = CONJ_LIST 3 (SIMP_RULE std_ss [LET_THM] f_spec1);
      val stat = f_correct f_spec1
      val stat_ir = f_correct_ir f_spec1
  in
      (f_name, f_type, (f_args,f_ir,f_outs), defs, stat, stat_ir, el 1 thm_list, el 2 thm_list, el 3 thm_list)
  end

end
end  
