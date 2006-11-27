structure annotatedIR = struct
  local
  open HolKernel Parse boolLib preARMTheory pairLib simpLib bossLib
       numSyntax optionSyntax listSyntax ILTheory IRSyntax
  in

 (*---------------------------------------------------------------------------------*)
 (*      Annotated IR tree                                                          *)
 (*---------------------------------------------------------------------------------*)

   (* annotation at each node of the IR tree *)
   type annt = {fspec : thm, ins : exp, outs : exp, context : exp list};

   (* conditions of CJ and TR *)
   type cond = exp * rop * exp;

   datatype anntIR =  TR of cond * anntIR * annt
                   |  SC of anntIR * anntIR * annt
                   |  CJ of cond * anntIR * anntIR * annt
                   |  BLK of instr list * annt
                   |  STM of instr list
                   |  CALL of string * anntIR * anntIR * anntIR * annt


 (*---------------------------------------------------------------------------------*)
 (*      Print an annotated IR tree                                                 *)
 (*---------------------------------------------------------------------------------*)

  val show_call_detail = ref true;

  fun print_ir (outstream, s0) =
    let 

      fun say s = TextIO.output(outstream,s)
      fun sayln s= (say s; say "\n") 

      fun indent 0 = ()
        | indent i = (say " "; indent(i-1))

      fun printtree(SC(s1,s2,info),d) =
            (indent d; sayln "SC("; printtree(s1,d+2); sayln ","; printtree(s2,d+2); say ")")
        | printtree(CJ((exp1,rop,exp2),s1,s2,info),d) = 
            (indent d; say "CJ("; say (format_exp exp1 ^ " " ^ print_rop rop ^ " " ^ format_exp exp2); sayln ",";
		       printtree(s1,d+2); sayln ","; printtree(s2,d+2); say ")")
        | printtree(TR((exp1,rop,exp2),s,info),d) = 
            (indent d; say "TR("; say (format_exp exp1 ^ " " ^ print_rop rop ^ format_exp exp2); sayln ",";
		       printtree(s,d+2); say ")")
        | printtree(CALL(fname,pre,body,post,info),d) =
            if not (!show_call_detail) then 
                (indent d; say ("CALL(" ^ fname ^ ")"))
            else
                let val ir' = SC (pre, SC (body, post, info), info)
                    (* val ir'' = (merge_stm o rm_dummy_inst) ir' *)
                in 
                    printtree (ir', d)
                end

        | printtree(STM stmL,d) = 
            (indent d; if null stmL then say ("[]") 
                       else say ("[" ^ formatInst (hd stmL) ^
                                 (itlist (curry (fn (stm,str) => "; " ^ formatInst stm ^ str)) (tl stmL) "") ^ "]"))
        | printtree(BLK(stmL, info),d) =
            printtree(STM stmL,d)

    in  
      printtree(s0,0); sayln ""; TextIO.flushOut outstream
    end

  fun printIR ir = print_ir (TextIO.stdOut, ir)

  fun printIR2 (f_name, f_type, (ins,ir,outs), defs) = 
      ( print ("Module: " ^ f_name ^ "\n");
        print ("Inputs: " ^ format_exp ins ^ "\n" ^ "Outputs: " ^ format_exp outs ^ "\n");
        printIR ir
      )

 (*---------------------------------------------------------------------------------*)
 (*      Assistant Graph Functions                                                  *)
 (*---------------------------------------------------------------------------------*)

   structure G = Graph;

   fun mk_edge (n0,n1,lab) gr =
    if n0 = n1 then gr
    else if (List.find (fn m => #2 m = n0) (#1(G.context(n1,gr)))) <> NONE then gr              (* raise Edge *)
    else
       let val ((p1,m1,l1,s1), del_n1) = G.match(n1,gr)
       in G.embed(((lab,n0)::p1,m1,l1,s1),del_n1)
    end;

   (* retreive the subgraph starting from the start node and ends when "f node" holds *) 
   fun sub_graph gr start_node f = 
       let 
           fun one_node (nodeNo,gr') =
               if f nodeNo then
		   gr'
               else           
                   List.foldl (fn ((a,b),gr'') =>
                                   one_node (b, G.embed (([(a,nodeNo)],b,#3 (G.context(b,gr)),[]), gr''))
                              handle e => mk_edge (nodeNo,b,0) gr'')
                            gr' (#4 (G.context(nodeNo,gr)))
       in 
           one_node (start_node, G.embed(([],start_node, #3 (G.context(start_node,gr)),[]),G.empty))
       end;

    (* locate a node, whenever the final node is reached, search terminats *)
    fun locate gr start_node f = 
       let 
           val maxNodeNo = G.noNodes gr - 1;
           fun one_node nodeNo =
               if f nodeNo then
		   (SOME nodeNo,true)
               else if nodeNo = maxNodeNo then
                   (NONE,false)
               else
                   List.foldl (fn ((a,b),(n,found)) => if found then (n,found) else one_node b)
                            (SOME start_node,false) (#4 (G.context(nodeNo,gr)))
       in 
           #1 (one_node start_node)
       end;

 (*---------------------------------------------------------------------------------*)
 (*      Conversion from CFG to IR tree                                             *)
 (*---------------------------------------------------------------------------------*)

   fun get_label (Assem.LABEL {lab = lab'}) = lab'
    |  get_label _ = raise ERR "IL" ("Expecting a label instruction")

   (* find the node including the function label, if there are more than one incoming edges, then a rec is found *)

   fun is_rec gr n = 
       let 
           val context = G.context(n,gr)
           fun is_label (Assem.LABEL _) = true
            |  is_label _ = false
       in 
           if is_label (#instr ((#3 context):CFG.node)) then
                (length (#1 context) > 1, n)
           else is_rec gr (#2 (hd (#4 context)))
       end 
       handle e => (false,0);        (* no label node in the graph *)


   (* Given a TR cfg and the node including the function name label, break this cfg into three parts: the pre-condition part, 
      the basic case part and the recursive case part. The condition is also derived.                                          *)    


   fun break_rec gr lab_node = 
     let 
        fun get_sucL n = #4 (G.context(n,gr));
        fun get_preL n = #1 (G.context(n,gr));

        val last_node = valOf (locate gr 0 (fn n => null (get_sucL n)));
        fun find_join_node n = 
            if length (get_preL n) > 1 then n
            else find_join_node (#2 (hd (get_preL n))); 
        val join_node = find_join_node last_node;  (* the node that the basic and recursive parts join *)

        (* the nodes jumping to the join node *)
        val BAL_node = #2 (valOf (List.find (fn (flag,n) => flag = 1) (get_preL join_node))); 
        val b_end_node = #2 (valOf (List.find (fn (flag,n) => flag = 0) (get_preL join_node))); 
        val b_start_node = #2 (valOf (List.find (fn (flag,n) => flag = 2) (get_sucL BAL_node))); 
        val b_cfg = sub_graph gr b_start_node (fn n => n = b_end_node);

        val cj_node = #2 (valOf (List.find (fn (flag,n) => flag = 1) (get_preL b_start_node)));
        val cmp_node = #2 (hd (get_preL cj_node));
        val cond = to_cond (#instr ((#3 (G.context(cmp_node,gr))):CFG.node), 
                            #instr ((#3 (G.context(cj_node,gr))):CFG.node));
              
        val r_start_node = #2 (valOf (List.find (fn (flag,n) => flag = 0) (get_sucL cj_node)));
        val BL_node = #2 (valOf (List.find (fn (flag,n) => flag = 1) (get_preL lab_node))); 
        val r_end_node = #2 (hd (get_preL BL_node));
        val r_cfg = sub_graph gr r_start_node (fn n => n = r_end_node);
               
        val p_start_node = if #2 (hd (get_sucL lab_node)) = cmp_node then NONE
                           else SOME (#2 (hd (get_sucL lab_node)));
        val p_cfg = case p_start_node of 
                          NONE => NONE  (* the pre-condition part may be empty *)
                      |   SOME k => SOME (sub_graph gr k (fn n => n = #2 (hd (get_preL cj_node))))
    in
        (cond, ((p_cfg,p_start_node), (b_cfg,b_start_node), (r_cfg,r_start_node)), join_node)
    end

   (* Given a CJ cfg and the node including the cmp instruction, break this cfg into the true case part and 
      the false case part.                                                        *) 

   fun break_cj gr cmp_node = 
     let 
        fun get_sucL n = #4 (G.context(n,gr));
        fun get_preL n = #1 (G.context(n,gr));

        val cj_node = #2 (hd (get_sucL cmp_node));
        val sucL = #4 (G.context(cj_node,gr));
        val (t_start_node, f_start_node) =  (#2 (valOf (List.find (fn (flag,n) => flag = 1) sucL)),
                                             #2 (valOf (List.find (fn (flag,n) => flag = 0) sucL)));
        val bal_node = #2 (valOf (List.find (fn (flag,n) => flag = 2) (get_preL t_start_node)));
        val f_end_node = #2 (hd (get_preL bal_node));

        val join_node = #2 (valOf (List.find (fn (flag,n) => flag = 1) (get_sucL bal_node)));
        val t_end_node =  #2 (valOf (List.find (fn (flag,n) => flag = 0) (get_preL join_node))); 
  
        val cond = to_cond (#instr ((#3 (G.context(cmp_node,gr))):CFG.node), 
                            #instr ((#3 (G.context(cj_node,gr))):CFG.node));
              
        val (t_cfg,f_cfg) = (sub_graph gr t_start_node (fn n => n = t_end_node), 
                             sub_graph gr f_start_node (fn n => n = f_end_node))
    in
        (cond, ((t_cfg,t_start_node), (f_cfg,f_start_node)), join_node)
    end

   
   fun convert_cond (exp1, rop, exp2) = 
       (to_exp exp1, to_rop rop, to_exp exp2);

 (*---------------------------------------------------------------------------------*)
 (*  Convert cfg consisting of SC, CJ and CALL structures to ir tree                *)
 (*---------------------------------------------------------------------------------*)

   val thm_t = DECIDE (Term `T`);
   val init_info = {fspec = thm_t, ins = NA, outs = NA, context = []};

   fun convert cfg n =
        let 
           val (preL,_,{instr = inst', def = def', use = sue'},sucL) = G.context(n,cfg);
        in
           case inst' of 
               Assem.OPER {oper = (Assem.NOP, _, _), ...} => 
                     if not (null sucL) then convert cfg (#2 (hd sucL)) else STM [] 

           |   Assem.OPER {oper = (Assem.BL,_,_), dst = dList, src = sList, jump = jp} =>
                     let val stm = CALL(Symbol.name(hd (valOf jp)), STM [], STM [], STM [], 
                                      {fspec = thm_t, ins = list2pair (List.map to_exp sList), 
                                        outs = list2pair (List.map to_exp dList), context = []})
                     in  if null sucL then stm   
                         else SC (stm, convert cfg (#2 (hd sucL)), init_info)
                     end
           |   Assem.LABEL {...} =>
                     if not (null sucL) then convert cfg (#2 (hd sucL)) else STM [] 

           |   Assem.OPER {oper = (Assem.CMP, _, _), ...} =>
                     let val (cond, ((t_cfg,t_start_node),(f_cfg,f_start_node)), join_node) = break_cj cfg n;
                              (* val rest_cfg = sub_graph gr join_node (fn k => k = end_node); *)
                     in 
                         SC (CJ (convert_cond cond, convert t_cfg t_start_node, convert f_cfg f_start_node, init_info),
                             convert cfg join_node, init_info)
                     end

           |   x => 
                     if not (null sucL) then 
                         SC (STM [to_inst x], convert cfg (#2 (hd sucL)), init_info)
                     else STM [to_inst x]
        end

(*---------------------------------------------------------------------------------*)
(*  Convert a cfg corresonding to a function to ir                                 *)
(*---------------------------------------------------------------------------------*)
   fun convert_module (ins,cfg,outs) = 
      let 
         val (flag, lab_node) = is_rec cfg 0
         val (inL,outL) = (pair2list ins, pair2list outs)
      in 
         if not flag then convert cfg lab_node
         else 
            let val (cond, ((p_cfg,p_start_node), (b_cfg,b_start_node), (r_cfg,r_start_node)), join_node) = break_rec cfg lab_node
                val (b_ir,r_ir) = (convert b_cfg b_start_node, convert r_cfg r_start_node);

                val bal_node = #2 (valOf (List.find (fn (flag,n) => flag = 1) (#1 (G.context(lab_node,cfg)))));
                val (Assem.OPER {src = rec_argL,...}) = #instr ((#3(G.context(bal_node,cfg))):CFG.node);
                val rec_args_pass_ir = STM (List.map (fn (dexp,sexp) => {oper = mmov, src = [sexp], dst = [dexp]}) 
                             (zip inL (pair2list (to_exp (hd rec_argL)))))    (* dst_exp  = BL (src_exp) *)

                val info = {fspec = DECIDE(Term`T`), ins = ins, outs = ins, context = []}
                val r_ir_1 = SC(r_ir,rec_args_pass_ir, info)

                val cond' = convert_cond cond
                val tr_ir = case p_cfg of 
                                 NONE => 
                                    SC (TR (cond', r_ir_1, {fspec = thm_t, ins = ins, outs = ins, context = []}),
                                        b_ir, info)
                               |  SOME p_gr =>
                                    let val p_ir = convert p_gr (valOf p_start_node);
                                        val ir0 = SC (r_ir_1, p_ir, init_info)
                                        val ir1 = TR (cond', ir0, {fspec = thm_t, ins = ins, outs = outs, context = []})            
                                        val ir2 = SC (ir1, b_ir, {fspec = thm_t, ins = ins, outs = ins, context = []})
                                    in
                                         SC (p_ir, ir2, {fspec = thm_t, ins = ins, outs = outs, context = []})
                                    end
             in
                tr_ir
             end
       end;              

 (*---------------------------------------------------------------------------------*)
 (*      Simplify the IR tree                                                       *)
 (*---------------------------------------------------------------------------------*)

   fun is_dummy_inst ({oper = mmov, src = sList, dst = dList}) =
         hd sList = hd dList
    |  is_dummy_inst (stm as {oper = op', src = sList, dst = dList}) =
         if length sList < 2 then false
         else if hd dList = hd sList then
            (hd (tl sList) = WCONST Arbint.zero andalso (op' = madd orelse op' = msub orelse op' = mlsl orelse
                     op' = mlsr orelse op' = masr orelse op' = mror))
         else if hd dList = hd (tl (sList)) then
            hd sList = WCONST Arbint.zero andalso (op' = madd orelse op' = mrsb)
         else
            false;

   fun rm_dummy_inst (SC(ir1,ir2,info)) =
         SC (rm_dummy_inst ir1, rm_dummy_inst ir2, info)
    |  rm_dummy_inst (TR(cond,ir2,info)) = 
         TR(cond, rm_dummy_inst ir2, info)
    |  rm_dummy_inst (CJ(cond,ir1,ir2,info)) = 
         CJ(cond, rm_dummy_inst ir1, rm_dummy_inst ir2, info)
    |  rm_dummy_inst (STM stmL) =
         STM (List.filter (not o is_dummy_inst) stmL)
    | rm_dummy_inst (CALL (fname,pre,body,post,info)) =
         CALL (fname, rm_dummy_inst pre, rm_dummy_inst body, rm_dummy_inst post,info)
    | rm_dummy_inst (BLK (instL, info)) =
         BLK (List.filter (not o is_dummy_inst) instL,info)


   fun merge_ir ir =
     let

       (* Determine whether two irs are equal or not *) 

       fun is_ir_equal (SC(s1,s2,_)) (SC(s3,s4,_)) = 
	     is_ir_equal s1 s3 andalso is_ir_equal s2 s4
        |  is_ir_equal (TR(cond1,body1,_)) (TR(cond2,body2,_)) = 
	     cond1 = cond2 andalso is_ir_equal body1 body2
        |  is_ir_equal (CJ(cond1,s1,s2,_)) (CJ(cond2,s3,s4,_)) = 
	     cond1 = cond2 andalso is_ir_equal s1 s3 andalso is_ir_equal s2 s4
        |  is_ir_equal (BLK(s1,_)) (BLK(s2,_)) = 
	     List.all (op =) (zip s1 s2)
        |  is_ir_equal (STM s1) (STM s2) = 
	     List.all (op =) (zip s1 s2)
        |  is_ir_equal (CALL(name1,_,_,_,_)) (CALL(name2,_,_,_,_)) = 
	     name1 = name2
        |  is_ir_equal _ _ = false;

       fun merge_stm (SC(STM s1, STM s2, info)) = 
             BLK (s1 @ s2, info)
        |  merge_stm (SC(STM s1, BLK(s2,_), info)) = 
	     BLK (s1 @ s2, info)
	|  merge_stm (SC(BLK(s1,_), STM s2, info)) = 
	     BLK (s1 @ s2, info)
	|  merge_stm (SC(BLK(s1,_), BLK(s2,_), info)) = 
	     BLK (s1 @ s2, info)
	|  merge_stm (SC(STM [], s2, info)) = 
	     merge_stm s2
	|  merge_stm (SC(s1, STM [], info)) = 
	     merge_stm s1
	|  merge_stm (SC(BLK([],_), s2, info)) = 
	     merge_stm s2
	|  merge_stm (SC(s1, BLK([],_), info)) = 
	     merge_stm s1	
	|  merge_stm (SC(s1,s2,info)) =
	     SC (merge_stm s1, merge_stm s2, info)
	|  merge_stm (TR(cond, body, info)) = 
	     TR(cond, merge_stm body, info)
	|  merge_stm (CJ(cond, s1, s2, info)) = 
	     CJ(cond, merge_stm s1, merge_stm s2, info)
        |  merge_stm (STM s) =
             BLK(s, init_info)
	|  merge_stm stm = 
	     stm

        fun merge ir = let val ir' = merge_stm ir;
                           val ir'' = merge_stm ir' in
                         if is_ir_equal ir' ir'' then ir'' else merge ir''
                       end
     in
	merge ir
     end


 (*---------------------------------------------------------------------------------*)
 (*      Assistant functions                                                        *)
 (*---------------------------------------------------------------------------------*)

   fun get_annt (BLK (stmL,info)) = info
    |  get_annt (SC(s1,s2,info)) = info
    |  get_annt (CJ(cond,s1,s2,info)) = info
    |  get_annt (TR(cond,s,info)) = info
    |  get_annt (CALL(fname,pre,body,post,info)) = info
    |  get_annt (STM stmL) = {ins = NA, outs = NA, fspec = thm_t, context = []};

   fun replace_ins {ins = ins', outs = outs', context = context', fspec = fspec'} ins'' = 
           {ins = ins'', outs = outs', context = context', fspec = fspec'};

   fun replace_outs {ins = ins', outs = outs', context = context', fspec = fspec'} outs'' = 
           {ins = ins', outs = outs'', context = context', fspec = fspec'};

   fun replace_context {ins = ins', outs = outs', context = context', fspec = fspec'} context'' = 
           {ins = ins', outs = outs', context = context'', fspec = fspec'};

   fun replace_fspec {ins = ins', outs = outs', context = context', fspec = fspec'} fspec'' = 
           {ins = ins', outs = outs', context = context', fspec = fspec''};


   fun apply_to_info (BLK (stmL,info)) f =  BLK (stmL, f info)
    |  apply_to_info (SC(s1,s2,info)) f = SC(s1, s2, f info)
    |  apply_to_info (CJ(cond,s1,s2,info)) f = CJ(cond, s1, s2, f info)
    |  apply_to_info (TR(cond,s,info)) f = TR(cond, s, f info)
    |  apply_to_info (CALL(fname,pre,body,post,info)) f = CALL(fname, pre, body, post, f info)
    |  apply_to_info (STM stmL) f = STM stmL;


 (*---------------------------------------------------------------------------------*)
 (*      Calculate Modified Registers                                               *)
 (*---------------------------------------------------------------------------------*)

   fun one_stm_modified_regs ({oper = op1, dst = dlist, src = slist}) =
       List.map (fn (REG r) => r | _ => ~1) (List.filter (fn (REG r) => true | _ => false) dlist);


   fun get_modified_regs (SC(ir1,ir2,info)) =
         (get_modified_regs ir1) @ (get_modified_regs ir2)
    |  get_modified_regs (TR(cond,ir,info)) = 
         get_modified_regs ir
    |  get_modified_regs (CJ(cond,ir1,ir2,info)) = 
         (get_modified_regs ir1) @ (get_modified_regs ir2)
    |  get_modified_regs (CALL(fname,pre,body,post,info)) = 
			let
				val preL = get_modified_regs pre
				val bodyL = get_modified_regs body
				val outsL = (List.map (fn (REG r) => r | _ => ~1) (pair2list (#outs info)))
				val restoredL = [13, ~1]
				val modL = filter (fn e => not (mem e restoredL)) (preL @ bodyL @ outsL)
			in
				modL
			end
    |  get_modified_regs (STM l) =
         itlist (curry (fn (a,b) => one_stm_modified_regs a @ b)) l [] 
    |  get_modified_regs (BLK (l,info)) = 
         itlist (curry (fn (a,b) => one_stm_modified_regs a @ b)) l [];
  
 (*---------------------------------------------------------------------------------*)
 (*      Set input, output and context information                                  *)
 (*      Alignment functions                                                        *)
 (*---------------------------------------------------------------------------------*)

   (* Adjust the inputs to be consistent with the outputs of the previous ir  *)

   fun adjust_ins ir (outer_info as ({ins = outer_ins, outs = outer_outs, context = outer_context, ...}:annt)) =
        let val inner_info as {ins = inner_ins, context = inner_context, outs = inner_outs, fspec = inner_spec, ...} = get_annt ir;
            val (inner_inS,outer_inS) = ((list2set o pair2list) inner_ins, (list2set o pair2list) outer_ins);
        in  if outer_ins = inner_ins then
               ir
            else
               case ir of
                   (BLK (stmL, info)) => 
                       BLK (stmL, replace_ins info outer_ins)
                |  (SC (s1,s2,info)) =>
                       SC (adjust_ins s1 outer_info, s2, replace_ins info outer_ins)
                |  (CJ (cond,s1,s2,info)) =>
                       CJ (cond, adjust_ins s1 outer_info, adjust_ins s2 outer_info, replace_ins info outer_ins)
                |  (TR (cond,s,info)) =>
                       TR(cond, adjust_ins s info, replace_ins info outer_ins)
                |  (CALL (fname,pre,body,post,info)) =>
                       CALL(fname, pre, body, post, replace_ins info outer_ins)
                |  _ => 
                       raise Fail "adjust_ins: invalid IR tree"
        end


   fun args_diff (ins1, outs0) = 
        set2pair (S.difference (pair2set ins1, pair2set outs0));

   (* Given the outputs and the context of an ir, calculate its inputs *)


(*
val ir0 = (back_trace ir1 info)

fun extract (SC(s1,s2,inner_info)) (outer_info as {outs = outer_outs, context = contextL, ...}:annt) =
	(s1, s2, inner_info, outer_outs, contextL, outer_info) 

val (s1, s2, inner_info, outer_outs, contextL, outer_info)  = extract ir1 info

              val s1' = back_trace 

val s2' = back_trace s2 outer_info

fun extract (CJ(cond, s1, s2, inner_info)) (outer_info as {outs = outer_outs, context = contextL, ...}:annt) =
(cond, s1, s2, inner_info, outer_info, outer_outs, contextL)

val (cond, s1, s2, inner_info, outer_info, outer_outs, contextL) = extract s1 outer_info

fun extract (CALL (fname, pre, body, post, info)) (outer_info as {outs = outer_outs, context = contextL, fspec = fout_spec, ...}:annt) =
(fname, pre, body, post, info, outer_info, outer_outs, contextL, fout_spec);

val (fname, pre, body, post, info, outer_info, outer_outs, contextL, fout_spec) = extract s1 {ins = #ins outer_info, outs = #ins s2_info, context = #context s2_info, fspec = #fspec s1_info};

*)

   fun back_trace (BLK (stmL,inner_info)) (outer_info as {outs = outer_outs, context = contextL, ...}:annt) = 
          let 
              val (inner_inL, inner_tempL, inner_outL) =  getIO stmL
              val gapL = set2list (S.difference (pair2set outer_outs, list2set inner_outL));
              val read_inS = list2set (gapL @ inner_inL);
             (* val contextS = S.difference (list2set contextL, real_outS) *)
          in 
              BLK (stmL, {outs = outer_outs, ins = set2pair read_inS, context = contextL, fspec = #fspec inner_info}) 
          end

    |  back_trace (STM stmL) info =
          back_trace (BLK (stmL,init_info)) info

    |  back_trace (SC(s1,s2,inner_info)) (outer_info as {outs = outer_outs, context = contextL, ...}) =
           let 
              val s2' = back_trace s2 outer_info
              val (s1_info, s2_info) = (get_annt s1, get_annt s2');
              val s2'' = if S.isSubset (pair2set (#ins s2_info), pair2set (#outs s1_info))
                         then adjust_ins s2' (replace_ins s2_info (#outs s1_info))
			 else s2';
              val s2_info = get_annt s2'';
              val s1' = back_trace s1 {ins = #ins outer_info, outs = #ins s2_info, context = #context s2_info, fspec = #fspec s1_info};
              val s1_info = get_annt s1'
           in
              SC(s1',s2'', {ins = #ins s1_info, outs = #outs s2_info, fspec = thm_t, context = contextL})
           end

    |  back_trace (CJ(cond, s1, s2, inner_info)) (outer_info as {outs = outer_outs, context = contextL, ...}) =
          let 
              fun filter_exp (REG e) = [REG e]
               |  filter_exp (MEM e) = [MEM e]
               |  filter_exp _ = []

              val cond_expL = filter_exp (#1 cond) @ filter_exp (#3 cond);
              val s1' = back_trace s1 outer_info
              val s2' = back_trace s2 outer_info
              val ({ins = ins1, outs = outs1, ...}, {ins = ins2, outs = outs2, ...}) = (get_annt s1', get_annt s2');
              val inS_0 = set2pair (list2set
					(cond_expL @ (pair2list ins1) @ (pair2list ins2))); 
                      (* union of the variables in the condition and the inputs of the s1' and s2' *)
              val info_0 = replace_ins outer_info inS_0
          in
              CJ(cond, adjust_ins s1' info_0, adjust_ins s2' info_0, info_0)
          end

    |  back_trace (TR (cond, body, info)) (outer_info as {outs = outer_outs, context = contextL, ...}) =
           let 
              val extra_outs = args_diff (PAIR (outer_outs, list2pair contextL), #outs info)
              val info' = replace_context info (pair2list extra_outs);
              val body' = adjust_ins body info'
          in
              TR(cond, body', info')
          end

          (* the adjustment will be performed later in the funCall.sml *)
    |  back_trace (CALL (fname, pre, body, post, info)) (outer_info as {outs = outer_outs, context = contextL, fspec = fout_spec, ...}) =
          let 
				  val outer_outs_set = pair2set outer_outs
				  val inner_outs_set = pair2set (#outs info);
				  val extra_outs_set = S.difference (outer_outs_set, inner_outs_set);

				  val inner_ins_set = pair2set (#ins info)
				  val new_ins_set = S.union(extra_outs_set, inner_ins_set);

				  val new_ins = set2pair new_ins_set;
				  val info' = replace_ins outer_info new_ins
          in
              CALL (fname, pre, BLK ([], info), post, info')
          end;


   fun set_info (ins,ir,outs) = 
       let 
          fun extract_outputs ir0 = 
              let val info0 = get_annt ir0;
                  val (inner_outS, outer_outS) = (IRSyntax.pair2set (#outs info0), IRSyntax.pair2set outs)
                  val ir1 = if Binaryset.equal(inner_outS, outer_outS) then ir0
                            else SC (ir0, BLK ([], {context = #context info0, ins = #outs info0, outs = outs, fspec = thm_t}),
				     replace_outs info0 outs)
                  val info1 = get_annt ir1
              in
                  if #ins info0 = ins then ir1
                  else SC (BLK ([], {context = #context info1, ins = ins, outs = #ins info0, fspec = thm_t}),
			   ir1, replace_ins info1 ins)
              end
          val info =  {ins = ins, outs = outs, context = [], fspec = thm_t}
       in
          extract_outputs (back_trace ir info)
       end;
(* ---------------------------------------------------------------------------------------------------------------------*)
(* Adjust the IR tree to make inputs and outputs consistent                                                             *)
(* ---------------------------------------------------------------------------------------------------------------------*)

  fun match_ins_outs (SC(s1,s2,info)) =
      let 
          val (ir1,ir2) = (match_ins_outs s1, match_ins_outs s2);
          val (info1,info2) = (get_annt ir1, get_annt ir2);
          val (outs1, ins2) = (#outs info1, #ins info2);
      in
          if outs1 = ins2 then 
              SC(ir1,ir2,info)
          else 
              SC(ir1, 
                 SC (BLK ([], {ins = outs1, outs = ins2, context = #context info2, fspec = thm_t}), ir2, 
                          replace_ins info2 outs1),
                 info)
      end

   |  match_ins_outs (ir as (CALL (fname, pre, body, post, info))) =
      let
          val ((pre_ins,post_outs),(outer_ins,outer_outs)) = ((#ins (get_annt pre), #outs (get_annt post)), (#ins info, #outs info))
          val ir' = if post_outs = outer_outs then ir
                    else
			SC (ir,
			    BLK ([], {ins = post_outs, outs = outer_outs, context = #context info, fspec = thm_t}),
			    replace_ins info pre_ins)
      in
          if pre_ins = outer_ins then ir'
          else
              SC (BLK([], {ins = outer_ins, outs = pre_ins, context = #context info, fspec = thm_t}),
                  ir',
                  info)
      end
    
   |  match_ins_outs ir = 
      ir;


 (*---------------------------------------------------------------------------------*)
 (*      Interface                                                                  *)
 (*---------------------------------------------------------------------------------*)

   fun build_ir (f_name, f_type, f_args, f_gr, f_outs, f_rs) = 
      let
         val (ins, outs) = (IRSyntax.to_exp f_args, IRSyntax.to_exp f_outs)
         val ir0 = convert_module (ins, f_gr, outs)
         val ir1 = (merge_ir o rm_dummy_inst) ir0
         val ir2 = set_info (ins,ir1,outs)
      in
         (ins,ir2,outs)
      end  

   fun sfl2ir prog =
     let
        val env = ANF.toANF [] prog;
        val defs = List.map (fn (name, (flag,src,anf,cps)) => src) env;
        val (f_const,(_, f_defs, f_anf, f_ast)) = hd env
        val setting as (f_name, f_type, f_args, f_gr, f_outs, f_rs) = regAllocation.convert_to_ARM (f_anf); 
        val f_ir = build_ir setting
     in
        (f_name, f_type, f_ir, defs)
     end

end
end
