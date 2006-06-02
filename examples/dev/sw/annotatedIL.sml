structure annotatedIL = struct
  local
  open HolKernel Parse boolLib preARMTheory pairLib simpLib bossLib
       numSyntax optionSyntax listSyntax ILTheory
  in


 (*---------------------------------------------------------------------------------*)
 (*      Definition of Data                                                         *) 
 (*---------------------------------------------------------------------------------*)

  exception invalidILExp;

  datatype operator =  madd | msub | mrsb | mmul | mmla | mmov |
                       mand | morr | meor |
                       mlsl | mlsr | masr | mror |
                       mldr | mstr | mpop | mpush |
                       mmrs | mmsr

  datatype alias = fp | ip | sp | lr | pc

  datatype exp = NCONST of Arbint.int
               | WCONST of Arbint.int
               | PAIR of exp * exp
               | CALL of exp * exp list
               | MEM of int * int               (* base * offset *)
               | REG of int
               | ALIAS of alias
               | SHIFT of operator * int
               | NA                             (* N/A, for undecided fields *)

   datatype rop = eq | ne | ge | le | gt | lt | al | nv

   type instr = {oper: operator, dst: exp list, src: exp list}

 (*---------------------------------------------------------------------------------*)
 (*      Definition of Basic Operations                                                   *)
 (*---------------------------------------------------------------------------------*)

  fun pair2list (PAIR(v1, v2)) =
        (pair2list v1) @ (pair2list v2)
   |  pair2list v = [v]

  fun fromAlias fp = 11
   |  fromAlias ip = 12
   |  fromAlias sp = 13
   |  fromAlias lr = 14
   |  fromAlias pc = 15

  fun toAlias 11 = fp
   |  toAlias 12 = ip
   |  toAlias 13 = sp
   |  toAlias 14 = lr
   |  toAlias 15 = pc
   |  toAlias _ = raise invalidILExp

  fun print_op mmov = "mmov"
   |  print_op madd = "madd"
   |  print_op msub = "msub"
   |  print_op mrsb = "msrb"
   |  print_op mmul = "mmul"
   |  print_op mmla = "mmla"
   |  print_op mand = "mand"
   |  print_op morr = "morr"
   |  print_op meor = "meor"
   |  print_op mlsl = "mlsl"
   |  print_op mlsr = "mlsr"
   |  print_op masr = "masr"
   |  print_op mror = "mror"
   |  print_op mldr = "mldr"
   |  print_op mstr = "mstr"
   |  print_op mpop = "mpop"
   |  print_op mpush = "mpush"
   |  print_op mmrs = "mmrs"
   |  print_op mmsr = "mmsr"

  fun convert_op mmov = Term(`MMOV`)
   |  convert_op madd = Term(`MADD`)
   |  convert_op msub = Term(`MSUB`)
   |  convert_op mrsb = Term(`MRSB`)
   |  convert_op mmul = Term(`MMUL`)
   |  convert_op mmla = Term(`MMLA`)
   |  convert_op mand = Term(`MAND`)
   |  convert_op morr = Term(`MORR`)
   |  convert_op meor = Term(`MEOR`)
   |  convert_op mlsl = Term(`MLSL`)
   |  convert_op mlsr = Term(`MLSR`)
   |  convert_op masr = Term(`MASR`)
   |  convert_op mror = Term(`MROR`)
   |  convert_op mldr = Term(`MLDR`)
   |  convert_op mpush = Term(`MPUSH`)
   |  convert_op mstr = Term(`MSTR`)
   |  convert_op mpop = Term(`MPOP`)
   |  convert_op mmrs = Term(`MMRS`)
   |  convert_op mmsr = Term(`MMSR`)

  fun print_rop (eq) = "eq"
   |  print_rop (ne) = "ne"
   |  print_rop (ge) = "ge"
   |  print_rop (lt) = "lt"
   |  print_rop (gt) = "gt"
   |  print_rop (le) = "le"
   |  print_rop (al) = "al"
   |  print_rop (nv) = "nv"

  fun convert_rop (eq) = Term(`EQ`)
   |  convert_rop (ne) = Term(`NE`)
   |  convert_rop (ge) = Term(`GE`)
   |  convert_rop (lt) = Term(`LT`)
   |  convert_rop (gt) = Term(`GT`)
   |  convert_rop (le) = Term(`LE`)
   |  convert_rop (al) = Term(`AL`)
   |  convert_rop (nv) = Term(`NV`)



 (*---------------------------------------------------------------------------------*)
 (*      Definition of Operations for Term-conversion                               *)
 (*---------------------------------------------------------------------------------*)

fun convert_reg (REG e) =
     rhs (concl (SIMP_CONV std_ss [from_reg_index_def] (mk_comb(Term`from_reg_index:num->MREG`, term_of_int e))))
 |  convert_reg _ = 
     raise ERR "IL" ("invalid expression");

fun convert_exp (MEM (regNo, offset)) =
      mk_comb(Term`MM`,
                 mk_pair(term_of_int regNo,
                    mk_comb(if offset >= 0 then Term`POS` else Term`NEG`,
                          term_of_int (abs offset))))
 |  convert_exp (NCONST e) =
      mk_comb(Term`MC`, mk_comb (Term`word32$n2w`, mk_numeral (Arbint.toNat e)))
 |  convert_exp (WCONST e) =
      mk_comb(Term`MC`, mk_comb (Term`word32$n2w`, mk_numeral (Arbint.toNat e)))
 |  convert_exp (REG e) =
      mk_comb (Term`MR`, convert_reg (REG e))
 |  convert_exp (PAIR(e1,e2)) =
      mk_pair(convert_exp e1, convert_exp e2)
 |  convert_exp _ =
      raise ERR "IL" ("invalid expression");


 fun convert_stm ({oper = op1, dst = dlist, src = slist}) =
    let
        val ops = convert_op op1;
        val (slist,dlist) = if op1 = mpop orelse op1 = mstr then (dlist,slist)
                            else (slist,dlist)
        val (dL,sL) = (List.map convert_reg dlist, List.map convert_exp slist)
    in
        list_mk_comb (ops, dL @ sL)
    end
    handle e =>  raise ERR "IL" ("invalid statement!")


 (*---------------------------------------------------------------------------------*)
 (*     Interface between ARM and IR                                                *)
 (*---------------------------------------------------------------------------------*)

   fun to_rop Assem.EQ = eq
    |  to_rop Assem.NE = ne
    |  to_rop Assem.GE = ge
    |  to_rop Assem.LE = le
    |  to_rop Assem.GT = ge
    |  to_rop Assem.LT = lt
    |  to_rop Assem.AL = al
    |  to_rop Assem.NV = nv

   fun to_op Assem.ADD = madd
    |  to_op Assem.SUB = msub
    |  to_op Assem.RSB = mrsb
    |  to_op Assem.MUL = mmul
    |  to_op Assem.MLA = mmla
    |  to_op Assem.AND = mand
    |  to_op Assem.ORR = morr
    |  to_op Assem.EOR = meor
    |  to_op Assem.LSL = mlsl
    |  to_op Assem.LSR = mlsr
    |  to_op Assem.ASR = masr
    |  to_op Assem.ROR = mror
    |  to_op Assem.LDR = mldr
    |  to_op Assem.STR = mstr
    |  to_op Assem.LDMFD = mpop
    |  to_op Assem.STMFD = mpush
    |  to_op Assem.MRS = mmrs
    |  to_op Assem.MSR = mmsr
    |  to_op _ = raise ERR "IL" "No corresponding operator in IL"

   fun to_exp (Assem.MEM {reg = regNo, offset = offset, ...}) =
           MEM(regNo,offset)
    |  to_exp (Assem.NCONST e) =
           NCONST e
    |  to_exp (Assem.WCONST e) =
           WCONST e
    |  to_exp (Assem.REG e) =
           REG e
    |  to_exp (Assem.PAIR(e1,e2)) =
           PAIR (to_exp e1, to_exp e2)
    |  to_exp _ =
           raise ERR "IL" ("No corresponding expression in IL") 

   fun to_inst (Assem.OPER {oper = (oper', cond', flag'), dst = dlist, src = slist, jump = jumps}) =
           {oper = to_op oper', dst = List.map to_exp dlist, src = List.map to_exp slist}
    |  to_inst (Assem.MOVE {dst = dst', src = src'}) =
           {oper = mmov, dst = [to_exp dst'], src = [to_exp src']}
    |  to_inst _ = 
           raise ERR "IL" ("Can convert only data operation instructions") 

   fun to_cond (Assem.OPER {oper = (Assem.CMP, cond1, flag1), dst = dlist1, src = slist1, jump = jumps1},
                Assem.OPER {oper = (Assem.B, cond2, flag2), dst = dlist2, src = slist2, jump = jumps2}) =
        (hd slist1, valOf cond2, hd (tl slist1))
    |  to_cond _ =  raise ERR "IL" ("Fail to obtain the condition from two instructions")

 (*---------------------------------------------------------------------------------*)
 (*      Annotated IR tree                                                          *)
 (*---------------------------------------------------------------------------------*)

   (* annotation at each node of the IR tree *)
   type annt = {spec : term, ins : exp, outs : exp, context : exp list};

   (* conditions of CJ and TR *)
   type cond = exp * rop * exp;

   datatype anntIR =  TR of cond * anntIR * annt
                   |  SC of anntIR * anntIR * annt
                   |  CJ of cond * anntIR * anntIR * annt
                   |  BLK of instr list * annt
                   |  STM of instr list

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
            else find_join_node (#2 (hd (get_preL last_node))); 
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

   (* convert cfg consisting of SC and CJ structures to ir tree *)
   fun convert cfg n =
        let 
           val (preL,_,{instr = inst', def = def', use = sue'},sucL) = G.context(n,cfg);
        in
           case inst' of 
               Assem.OPER {oper = (Assem.NOP, _, _), ...} => 
                     if not (null sucL) then convert cfg (#2 (hd sucL)) else STM [] 

           |   Assem.LABEL {...} =>
                     if not (null sucL) then convert cfg (#2 (hd sucL)) else STM [] 

           |   Assem.OPER {oper = (Assem.CMP, _, _), ...} =>
                     let val (cond, ((t_cfg,t_start_node),(f_cfg,f_start_node)), join_node) = break_cj cfg n;
                              (* val rest_cfg = sub_graph gr join_node (fn k => k = end_node); *)
                     in 
                         SC (CJ (convert_cond cond, convert t_cfg t_start_node, convert f_cfg f_start_node,  
                                     {spec = Term`T`, ins = NA, outs = NA, context = []}),
                             convert cfg join_node,
                                     {spec = Term`T`, ins = NA, outs = NA, context = []}
                             )
                     end

           |   x => 
                     if not (null sucL) then 
                         SC (STM [to_inst x], convert cfg (#2 (hd sucL)),
                             {spec = Term`T`, ins = NA, outs = NA, context = []})
                     else STM [to_inst x]
        end

   (* convert a cfg corresonding to a function to ir *)
   fun convert_module (ins,cfg,outs) = 
      let 
         val (flag, lab_node) = is_rec cfg 0
         val (inL,outL) = (pair2list ins, pair2list outs);
      in 
         if not flag then convert cfg lab_node
         else 
            let val (cond, ((p_cfg,p_start_node), (b_cfg,b_start_node), (r_cfg,r_start_node)), join_node) = break_rec cfg lab_node
                val (b_ir,r_ir) = (convert b_cfg b_start_node, convert r_cfg r_start_node);

                val bal_node = #2 (valOf (List.find (fn (flag,n) => flag = 1) (#1 (G.context(lab_node,cfg)))));
                val (Assem.OPER {src = rec_argL,...}) = #instr ((#3(G.context(bal_node,cfg))):CFG.node);
                val rec_args_pass_ir = STM (List.map (fn (dexp,sexp) => {oper = mmov, src = [sexp], dst = [dexp]}) 
                             (zip inL (List.map to_exp rec_argL)))

                   (* [{oper = mpush, src = List.map to_exp rec_argL, dst = []}, 
                                            {oper = mpop, src = [], dst = inL}];  *)

                val r_ir_1 = SC(r_ir,rec_args_pass_ir,{spec = Term`T`, ins = NA, outs = NA, context = []})

                val cond' = convert_cond cond
                val tr_ir = case p_cfg of 
                                 NONE => 
                                    SC (TR (cond', r_ir_1, {spec = Term`T`, ins = ins, outs = ins, context = []}),
                                        b_ir,
                                        {spec = Term`T`, ins = NA, outs = NA, context = []})
                               |  SOME p_gr =>
                                    let val p_ir = convert p_gr (valOf p_start_node);
                                        val ir0 = SC (r_ir_1, p_ir, {spec = Term`T`, ins = NA, outs = NA, context = []})
                                        val ir1 = TR (cond', ir0, {spec = Term`T`, ins = NA, outs = NA, context = []})                  
                                        val ir2 = SC (ir1, b_ir, {spec = Term`T`, ins = ins, outs = ins, context = []})
                                    in
                                         SC (p_ir, ir2, {spec = Term`T`, ins = NA, outs = NA, context = []})
                                    end
             in
                tr_ir
             end
       end;              

 (*---------------------------------------------------------------------------------*)
 (*      Simplify the IR tree                                                       *)
 (*---------------------------------------------------------------------------------*)

   fun rm_dummy_inst (SC(ir1,ir2,info)) =
         SC (rm_dummy_inst ir1, rm_dummy_inst ir2, info)
    |  rm_dummy_inst (TR(cond,ir2,info)) = 
         TR(cond, rm_dummy_inst ir2, info)
    |  rm_dummy_inst (CJ(cond,ir1,ir2,info)) = 
         CJ(cond, rm_dummy_inst ir1, rm_dummy_inst ir2, info)
    |  rm_dummy_inst (STM[]) =
         STM[]
    |  rm_dummy_inst (STM[{oper = mmov, src = sList, dst = dList}]) =
         if hd sList = hd dList then STM[]
         else STM[{oper = mmov, src = sList, dst = dList}]
    |  rm_dummy_inst (STM[stm as {oper = op', src = sList, dst = dList}]) =
         if hd dList = hd sList then 
            if hd (tl sList) = WCONST Arbint.zero andalso (op' = madd orelse op' = msub orelse op' = mlsl orelse
                     op' = mlsr orelse op' = masr orelse op' = mror) then
               STM[]
            else STM[stm]
         else if hd dList = hd (tl (sList)) then
            if hd sList = WCONST Arbint.zero andalso (op' = madd orelse op' = mrsb) then
               STM[]
            else STM[stm]
         else 
            STM[stm]
    | rm_dummy_inst inst = 
         inst

   fun merge_stm (SC(STM s1, STM s2, info)) = 
         STM (s1 @ s2)
    |  merge_stm (SC(STM [], s2, info)) = 
         merge_stm s2
    |  merge_stm (SC(s1, STM [], info)) = 
         merge_stm s1
    |  merge_stm (SC(s1, SC s,info)) = 
         merge_stm (SC(merge_stm s1, merge_stm (SC s), info))
    |  merge_stm (SC(SC s, s2,info)) = 
         merge_stm (SC(merge_stm (SC s), merge_stm s2, info))
    |  merge_stm (SC(s1,s2,info)) =
         SC (merge_stm s1, merge_stm s2, info)
    |  merge_stm (TR(cond, body, info)) = 
         TR(cond, merge_stm body, info)
    |  merge_stm (CJ(cond, s1, s2, info)) = 
         CJ(cond, merge_stm s1, merge_stm s2, info)
    |  merge_stm stm = 
         stm;

 (*---------------------------------------------------------------------------------*)
 (* Find the inputs, outputs and temporaries for a basic block                      *)
 (*---------------------------------------------------------------------------------*)
  
  structure T = IntMapTable(type key = int fun getInt n = n);

  datatype ACCESS = READ | WRITE | PUSH | POP 
  datatype ROLE = UNKNOWN | INPUT | OUTPUT | INSTACK;

  fun getIO stmL =
   let
     val (regT:((ROLE * ROLE) T.table) ref, memCT:((ROLE * ROLE) T.table) ref, memRT:((ROLE * ROLE) T.table) ref) 
	  = (ref (T.empty), ref (T.empty), ref (T.empty)); 

     fun peekT(t,index) = 
	case T.peek(t,index) of 
	     NONE => (UNKNOWN,UNKNOWN)
	 |   SOME v => v;

     fun ch_mode (UNKNOWN,UNKNOWN) READ = (INPUT,UNKNOWN)
      |  ch_mode (m,UNKNOWN) READ = (INPUT, UNKNOWN)
      |  ch_mode (m,UNKNOWN) WRITE = (m, OUTPUT)
      |  ch_mode (m,OUTPUT) WRITE = (m,OUTPUT)
      |  ch_mode (m,OUTPUT) READ = (m,INSTACK)
      |  ch_mode (m,INSTACK) READ = (m,INSTACK)
      |  ch_mode (m,INSTACK) WRITE = (m,OUTPUT)
      |  ch_mode _ _ = raise Fail "ch_mode: invalidMode";

     fun update_mode (REG r) action = 
	  regT := T.enter (!regT, r, ch_mode (peekT(!regT, r)) action)
      |  update_mode (MEM (base,offset)) action =
          memCT := T.enter (!memCT, offset, ch_mode (peekT(!memCT, offset)) action)
      |  update_mode _ _ = 
	  ();

     fun one_stm ({oper = op1, dst = dst1, src = src1}) =
	  ( List.map (fn exp => update_mode exp READ) src1;
	    List.map (fn exp => update_mode exp WRITE) dst1
	  );

     fun mk_regL indexL = 
	List.map (fn n => REG n) indexL;

     fun mk_memL indexL =
	List.map (fn n => MEM (fromAlias fp,n)) indexL;

     fun filter_inputs mode = 
	 mk_regL (List.filter (fn n => #1 (T.look (!regT,n)) = mode) (T.listKeys (!regT))) @ 
	 mk_memL (List.filter (fn n => #1 (T.look (!memCT,n)) = mode) (T.listKeys (!memCT)));

     fun filter_out_stack mode =
         mk_regL (List.filter (fn n => #2 (T.look (!regT,n)) = mode) (T.listKeys (!regT))) @
         mk_memL (List.filter (fn n => #2 (T.look (!memCT,n)) = mode) (T.listKeys (!memCT)));

     val _ = List.map one_stm stmL;
     val (ins, temps, outs) = (filter_inputs INPUT, filter_out_stack INSTACK, filter_out_stack OUTPUT);

     in
	(ins, temps, outs)
     end

 (*---------------------------------------------------------------------------------*)
 (*      Set input, output and context information                                  *)
 (*---------------------------------------------------------------------------------*)

   structure S = Binaryset;

   fun list2pair [] = NA
    |  list2pair (h::ts) = PAIR (h, list2pair ts);

   fun index_of_exp (MEM (base,offset)) =
         10000 + offset
    |  index_of_exp (REG e) =
         e
    |  index_of_exp NA =
         ~1
    |  index_of_exp _ =
          raise ERR "annotatedIR.eval_exp" ("invalid expression")

   fun expOrder (s1,s2) =
      let val (i1,i2) = (index_of_exp s1, index_of_exp s2)
      in
          if i1 > i2 then GREATER
          else if i1 = i2 then EQUAL
          else LESS
      end;
 
   fun get_annt (BLK (stmL,info)) = info
    |  get_annt (SC(s1,s2,info)) = info
    |  get_annt (CJ(cond,s1,s2,info)) = info
    |  get_annt (TR(cond,s,info)) = info
    |  get_annt _ =  raise ERR "annotatedIR.get_annt" ("invalid IR tree")

   fun bottom_up (STM stmL) =
          let 
              val (ins', temps', outs') =  getIO stmL
          in 
              BLK(stmL, {spec = Term `T`, ins = list2pair ins', outs = list2pair outs', context = []})
          end
    |  bottom_up (SC(s1,s2,info)) =
          let val {ins = ins1, outs = outs1, context = context1, ...} = get_annt (bottom_up s1);
              val {ins = ins2, outs = outs2, context = context2, ...} = get_annt (bottom_up s2);
              val context_0 = S.listItems(S.intersection(S.addList(S.empty expOrder,context1), S.addList(S.empty expOrder,context2)))
          in
              SC(s1,s2,{spec = Term `T`, ins = ins1, outs = outs2, context = context_0})
          end
    |  bottom_up (TR(cond,s,info)) =
          TR(cond,bottom_up s,info)
    |  bottom_up (CJ(cond, s1, s2, info)) =
          let val {ins = ins1, outs = outs1, context = context1, ...} = get_annt (bottom_up s1);
              val {ins = ins2, outs = outs2, context = context2, ...} = get_annt (bottom_up s2);
              val ins_0 = S.listItems(S.union (S.addList(S.empty expOrder,(pair2list ins1)), 
                                               S.addList(S.empty expOrder,(pair2list ins2))));
              val outs_0 = S.listItems(S.union (S.addList(S.empty expOrder,(pair2list outs1)), 
                                                S.addList(S.empty expOrder,(pair2list outs2))));
              val context_0 = S.listItems(S.intersection(S.addList(S.empty expOrder,context1), S.addList(S.empty expOrder,context2)))
          in
              CJ(cond,s1,s2,{spec = Term `T`, ins = list2pair ins_0, outs = list2pair outs_0, context = context_0})
          end
    |  bottom_up _ =  raise ERR "annotatedIR.bottom_up" ("invalid IR tree");


   fun list2set l = S.addList(S.empty expOrder,l);
   fun set2list s = List.filter (fn n => not (n = NA)) (S.listItems s);


   fun top_down (BLK (s,x)) info = BLK (s,info)
    |  top_down (STM s) info = BLK (s,info)
    |  top_down (SC(s1,s2,x)) info = SC (top_down s1 info, top_down s2 info, info)

    |  top_down (CJ(cond,s1,s2,x)) info = CJ (cond, top_down s1 info, top_down s2 info, info)

    |  top_down (TR(cond,body, tr_info as {ins = tr_ins, outs = tr_outs, context = tr_context, ...})) 
                 {ins = ins', outs = outs', context = context', ...} = 
          let val context_0 = set2list (S.union(list2set context',S.difference((list2set o pair2list) outs', (list2set o pair2list) tr_outs)))
          in 
              TR(cond, top_down body {ins = tr_ins, outs = tr_outs, context = context_0, spec = Term `T`}, tr_info)
          end
  
    |  top_down _ _ = raise Fail "top_down: unsupported IR structure";


   fun set_info (ins,ir,outs) = 
       top_down (bottom_up ir) {spec = Term`T`, ins = ins, outs = outs, context = []};

 (*---------------------------------------------------------------------------------*)
 (*      Interface                                                                  *)
 (*---------------------------------------------------------------------------------*)

   fun build_ir (fname, ftype, args, gr, outs, rs) = 
      let
         val (ins,outs) = (to_exp args, to_exp outs)
         val ir0 = convert_module (ins,gr,outs)
         val ir1 = (merge_stm o rm_dummy_inst) ir0
         val ir2 = set_info (ins,ir1,outs)
      in
         (ins,ir2,outs)
      end  

   fun sfl2ir prog =
     let
       val foids as [(f_const,(_,_, f_anf, f_ast))] = ANF.toANF [] prog;
       val setting as (f_name, f_type, f_args, f_gr, f_outs, f_rs) = regAllocation.convert_to_ARM (f_anf);
     in
       build_ir setting
     end

end
end
