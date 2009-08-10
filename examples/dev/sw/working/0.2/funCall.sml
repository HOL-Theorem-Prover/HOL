structure funCall =
struct

local
open HolKernel Parse boolLib IRSyntax annotatedIR
structure T = IntMapTable(type key = int  fun getInt n = n);
structure S = Binaryset
structure IR = IRSyntax
in

exception invalidArgs;
val numAvaiRegs = ref 10;

fun strOrder (s1:string,s2:string) =
    if s1 > s2 then GREATER
    else if s1 = s2 then EQUAL
    else LESS;

(* ---------------------------------------------------------------------------------------------------------------------*)
(* The configuaration for passing parameters, returning results and allocating stack space                              *)
(* The stack goes upward. 												*)
(* ---------------------------------------------------------------------------------------------------------------------*)
(*
                Address goes upward (i.e. from low address to high address)!!!

                                          Content                 Address
    caller's ip                 |  saved pc                     |   0
    caller's fp                 |  saved lr                     |   1
                                |  save sp                      |   2
                                |  save fp                      |   3
                                |  modified reg k               |
                                |  modified reg k-1             |
                                |  ...                          |
                                |  local variable 0             |   4
                                |  local variable 1             |   5
                                |       ...                     |   .
                                |  local variable n             |   .
                                |  output k from callee         |   .
                                |       ...                     |
                                |  output 1 from callee         |
                                |  output 0 from callee         |
                                |  argument m'                  |
                                |       ...                     |
                                |  argument 1                   |
                                |  argument 0                   |
    caller's sp callee's ip     |  saved pc                     |
    callee's fp                 |  saved lr                     |
                                |  save sp                      |
                                |  save fp                      |
                                |  modified reg k               |
                                |  modified reg k-1             |
                                |  ...                          |
                                |  local variable 0             |
                                |  local variable 1             |
                                |       ...                     |
    callee's sp                 |  local variable n'            |
*)


(* Distinguish inputs and local variables                                               *)
(* Calculate the offset based on fp of the temporaries bebing read in a callee		*)
(* If a temporary is an input, then read it from the stack where the caller sets 	*)
(* If it is a local variable, then read it from the current frame			*)

fun calculate_relative_address (args,ir,outs,numSavedRegs) =
  let
    (* Identify those TMEMs that are actually arguments *)
    val argT = #1 (List.foldl (fn (IR.TMEM n, (t,i)) =>
			          (T.enter(t, n, i), i+1)
                               |  (arg, (t,i)) => (t, i+1)
                              )
                        (T.empty, 0)
                        (IR.pair2list args)
                  );

    val i = ref 0
    val localT = ref (T.empty);   (* Table for the local variables *)

    (* For those TMEMs that are local variables, assign them in the stack according to the order of their apprearance *)

    fun filter_mems (IR.TMEM n) =
        ( case T.peek (argT, n) of
                SOME k => IR.MEM (IR.fromAlias IR.fp, ~2 - k)		(* inputs *)
           |     NONE =>
		( case T.peek(!localT, n) of
		      SOME j => IR.MEM (IR.fromAlias IR.fp, 3 + j + numSavedRegs) (* existing local variable *)
		   |  NONE =>
			  ( localT := T.enter(!localT, n, !i);
			    i := !i + 1;
			    IR.MEM (IR.fromAlias IR.fp, 3 + (!i - 1) + numSavedRegs) (* local variables *)
			  )
		 )
        )
     |  filter_mems v = v

    fun one_stm ({oper = op1, dst = dst1, src = src1}) =
            {oper = op1, dst = List.map filter_mems dst1, src = List.map filter_mems src1}

    fun adjust_exp (IR.PAIR (e1,e2)) =
	    IR.PAIR(adjust_exp e1, adjust_exp e2)
     |  adjust_exp e =
	    filter_mems e

    fun adjust_info {ins = ins', outs = outs', context = context', fspec = fspec'} =
        {ins = adjust_exp ins', outs = adjust_exp outs', context = List.map adjust_exp context', fspec = fspec'}

    fun visit (SC(ir1,ir2,info)) =
         SC (visit ir1, visit ir2, adjust_info info)
    |  visit (TR((e1,rop,e2),ir,info)) =
         TR ((adjust_exp e1,rop,adjust_exp e2), visit ir, adjust_info info)
    |  visit (CJ((e1,rop,e2),ir1,ir2,info)) =
         CJ ((adjust_exp e1,rop,adjust_exp e2), visit ir1, visit ir2, adjust_info info)
    |  visit (CALL(fname,pre,body,post,info)) =
         CALL(fname, pre, body, post, adjust_info info)
    |  visit (STM l) =
         STM (List.map one_stm l)
    |  visit (BLK (l,info)) =
         BLK (List.map one_stm l, adjust_info info);

  in
        (adjust_exp args, visit ir, adjust_exp outs, T.numItems (!localT))
  end

(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Decrease and increase the value of a register by n                                                                  *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun dec_p pt n = {oper = IR.msub, dst = [IR.REG pt], src = [IR.REG pt, IR.WCONST (Arbint.fromInt n)]}

fun inc_p pt n = {oper = IR.madd, dst = [IR.REG pt], src = [IR.REG pt, IR.WCONST (Arbint.fromInt n)]};


(* ---------------------------------------------------------------------------------------------------------------------*)
(* Pre-call and post-call processing in compilance with the ARM Procedure Call standard                                 *)
(* ---------------------------------------------------------------------------------------------------------------------*)

(* 	MOV     ip, sp
	STMFA   sp!, {..., fp,ip,lr,pc}
	SUB     fp, ip, #1
        SUB     sp, sp, #var (* skip local variables *)
*)

fun entry_blk rs n =
    [ {oper = IR.mmov, dst = [IR.REG (IR.fromAlias IR.ip)], src = [IR.REG (IR.fromAlias IR.sp)]},
      {oper = IR.mpush, dst = [IR.REG (IR.fromAlias IR.sp)],
       src = rs @ [IR.REG (IR.fromAlias IR.fp), IR.REG (IR.fromAlias IR.ip),
		   IR.REG (IR.fromAlias IR.lr), IR.REG (IR.fromAlias IR.pc)]
      },
      {oper = IR.msub, dst = [IR.REG (IR.fromAlias IR.fp)], src = [IR.REG (IR.fromAlias IR.ip), IR.WCONST Arbint.one]},
      dec_p (IR.fromAlias IR.sp) n (* skip local variables *)
    ]

(*
    ADD         sp, fp, 3 + #modified registers      (* Skip saved lr, sp, fp and modified registers *)
    LDMFD 	sp, {..., fp,sp,pc}
*)

fun exit_blk rs =
    [
      {oper = IR.msub, dst = [IR.REG (IR.fromAlias IR.sp)], src = [IR.REG (IR.fromAlias IR.fp), IR.WCONST (Arbint.fromInt (3 + length rs))]},
      {oper = IR.mpop, dst = rs @ [IR.REG (IR.fromAlias IR.fp), IR.REG (IR.fromAlias IR.sp), IR.REG (IR.fromAlias IR.pc)],
       src = [IR.REG (IR.fromAlias IR.sp)]}
    ];


(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Given a list of registers and memory slots, group consecutive registers together to be used by mpush and mpop       *)
(*  For example, [r1,r2,m1,m3,r3,4w,r4,r5] is segmented to                                                              *)
(*  ([r1,r2],true, 0),(m1,false,2),(m3,false,3),([r3],true,4),(4w,false,5),([r4,r5],true,6)                             *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun mk_reg_segments argL =
  let val isBroken = ref false;

      (* proceeds in reverse order of the list *)
      fun one_arg (IR.REG r, (invRegLs, i)) =
	let val flag = !isBroken
	    val _ = isBroken := false
	in
	    if null invRegLs orelse flag then
	        (([IR.REG r], true, i) :: invRegLs, i-1)
	    else
	        let val (cur_segL, a, j) = hd invRegLs
	        in
	  	    if null cur_segL then (([IR.REG r], true, i) :: (tl invRegLs), i-1)
	  	    else ((IR.REG r :: cur_segL, true, i) :: (tl invRegLs), i-1)
	        end
	end
      |	  one_arg (exp, (invRegLs, i)) =
		(isBroken := true; (([exp],false, i) :: invRegLs, i-1))

      val (invRegLs, i) = List.foldr one_arg ([], length argL - 1) argL

  in
      invRegLs
  end

(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Given a list of registers, generate a mpush or mpop statement                                                       *)
(*  The sp is assumed to be in the right position                                                                       *)
(*  If the list contain only one resiter, then use mldr and mstr instead                                                *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun mk_ldm_stm isPop r dataL =
    if isPop then
	if length dataL = 1 then
	       {oper = IR.mldr, dst = dataL, src = [IR.MEM (r,1)]}
	else
               {oper = IR.mpop, dst = dataL, src = [IR.REG r]}
    else
	if length dataL = 1 then
               {oper = IR.mstr, dst = [IR.MEM(r,0)], src = dataL}
	else
	       {oper = IR.mpush, dst = [IR.REG r], src = dataL}

(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Write one argument to the memory slot referred by regNo and offset      			                        *)
(*  Push arguments to the stack. If the argument comes from a register, and store it into the stack directly; 		*)
(*  if it comes from memory, then first load it into R10, and then store it into the stack;				*)
(*  if it is a constant, then assign it to R10 first then store it into the stack.                                      *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun write_one_arg (IR.MEM v) (regNo,offset) =
               [  {oper = IR.mldr, dst = [IR.REG (!numAvaiRegs)], src = [IR.MEM v]},
                  {oper = IR.mstr, dst = [IR.MEM (regNo,offset)], src = [IR.REG (!numAvaiRegs)]} ]
 |  write_one_arg (IR.REG r) (regNo,offset) =
               [  {oper = IR.mstr, dst = [IR.MEM (regNo,offset)], src = [IR.REG r]} ]
 |  write_one_arg v (regNo,offset) =   (* v = NONCST n or WCONST w *)
               [  {oper = IR.mmov, dst = [IR.REG 10], src = [v]},
		  {oper = IR.mstr, dst = [IR.MEM (regNo,offset)], src = [IR.REG 10]} ]

(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Read one argument from the memory slot referred by regNo and offset                                                 *)
(*  If the destination is a register, then load it into the register directly;                                          *)
(*  if it is in the memory, then first load the value into R10, and then store it into that memory location;            *)
(*  The destination couldn't be a constant                                                                              *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun read_one_arg (IR.REG r) (regNo,offset) =
	       [  {oper = IR.mldr, dst = [IR.REG r], src = [IR.MEM(regNo,offset)]} ]
 |  read_one_arg (IR.MEM v) (regNo,offset) =
               [  {oper = IR.mldr, dst = [IR.REG (!numAvaiRegs)], src = [IR.MEM(regNo,offset)]},
                  {oper = IR.mstr, dst = [IR.MEM v], src = [IR.REG (!numAvaiRegs)]} ]
 |  read_one_arg _ _ =
                 raise invalidArgs

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Push a list of values that may be constants or in registers or in memory into the stack                              *)
(* [1,2,3,...]                                                                                                          *)
(* old pointer | 1 |                                                                                                    *)
(*             | 2 |                                                                                                    *)
(*             | 3 |                                                                                                    *)
(*              ...                                                                                                     *)
(* new pointer                                                                                                          *)
(* Note that the elements in the list are stored in the memory from low addresses to high addresses                     *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun pushL regNo argL =
  let
      val offset = ref 0;

      fun one_seg (regL, true, i) =
              if length regL = 1 then
                    write_one_arg (hd regL) (regNo, !offset - i) (* relative offset should be negative *)
              else
                  let val k = !offset in
                    ( offset := i + length regL;
                      [dec_p regNo (i - k),
		       (* reverse the regL in accordance with the order of STM *)
                       mk_ldm_stm false regNo (List.rev regL)])
                  end
       | one_seg ([v], false, i) =
                  write_one_arg v (regNo, !offset - i)
       | one_seg _ = raise invalidArgs
  in
      (List.foldl (fn (x,s) => s @ one_seg x) [] (mk_reg_segments argL)) @
       [dec_p regNo (length argL - !offset)]
  end

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Pop from the stack a list of values that may be in registers or in memory into the stack                             *)
(*           ...                                                                                                        *)
(*           | 3 |                                                                                                      *)
(*           | 2 |                                                                                                      *)
(*           | 1 |                                                                                                      *)
(*  pointer                                                                                                             *)
(*  be read to the list [1,2,3,...]                                                                                     *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun popL regNo argL =
  let
      val offset = ref 0;

      fun one_seg (regL, true, i) =
              if length regL = 1 then
                    read_one_arg (hd regL) (regNo, i - !offset + 1) (* relative address should be positive *)
              else
                  let val k = !offset in
                    ( offset := i;
                      [inc_p regNo (i - k),
                       mk_ldm_stm true regNo regL])
                  end
       | one_seg ([v], false, i) =
                  read_one_arg v (regNo, i - !offset + 1)
       | one_seg _ = raise invalidArgs
  in
      (List.foldl (fn (x,s) => s @ one_seg x) [] (mk_reg_segments argL)) @
       [inc_p regNo (length argL - !offset)]
  end

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Pass by the caller the parameters to the callee                                                                      *)
(* All arguments are passed through the stack                                                                           *)
(* Stack status after passing                                                                                           *)
(*          ...                                                                                                         *)
(*        | arg 3 |                                                                                                     *)
(*        | arg 2 |                                                                                                     *)
(* sp     | arg 1 |                                                                                                     *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun pass_args argL =
  pushL (IR.fromAlias IR.sp) (List.rev argL)

(* ---------------------------------------------------------------------------------------------------------------------*)
(* The callee obtains the arguments passed by the caller though the stack                                               *)
(* By default, the first four arguments are loaded into r0-r4                                                           *)
(* The rest arguments has been in the right positions. That is, we need not to get them explicitly                      *)
(* Note that the register allocation assumes above convention                                                           *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun get_args argL =
   let
       val len = length argL;
       val len1 = if len < (!numAvaiRegs) then len else (!numAvaiRegs)

       fun mk_regL 0 = [IR.REG 0]
	|  mk_regL n = mk_regL (n-1) @ [IR.REG n];

   in
       popL (IR.fromAlias (IR.ip)) argL
       (* Note that callee's IP equals to caller's SP, we use the IP here to load the arguments *)
   end;

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Pass by the callee the results to the caller                                                                         *)
(* All results are passed through the stack                                                                             *)
(* Stack status after passing                                                                                           *)
(*                                                                                                                      *)
(*             ...                                                                                                      *)
(*         | result 3 |                                                                                                 *)
(*         | result 2 |                                                                                                 *)
(*         | result 1 |                                                                                                 *)
(*    sp                                                                                                                *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun send_results outL numArgs =
   let
       (* skip the arguments and the stored pc, then go to the position right before the first output*)
       val sOffset = numArgs + length outL + 1;
       val stms = pushL (IR.fromAlias IR.sp) (List.rev outL)
   in
       { oper = IR.madd,
         dst = [IR.REG (IR.fromAlias IR.sp)],
	 src = [IR.REG (IR.fromAlias IR.fp), IR.WCONST (Arbint.fromInt sOffset)]
       }
       :: stms
   end

(* ---------------------------------------------------------------------------------------------------------------------*)
(* The caller retreives the results passed by the callee though the stack                                               *)
(* Stack status                                                                                                         *)
(*                                                                                                                      *)
(*             ...                                                                                                      *)
(*         | result 3 |                                                                                                 *)
(*         | result 2 |                                                                                                 *)
(*         | result 1 |                                                                                                 *)
(*     sp  |          |                                                                                                 *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun get_results outL =
        popL (IR.fromAlias IR.sp) outL

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Function Call: Pre-processing, Post-processing and Adjusted Body                                                     *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun compute_fcall_info ((outer_ins,outer_outs),(caller_src,caller_dst),(callee_ins,callee_outs),rs,context) =
    let
        fun to_stack expL =
            let val len = length expL
                val i = ref 0;
            in
                List.map (fn exp => ( i := !i + 1; MEM(11, ~(3 + (len - !i))))) expL
            end

        val to_be_stored = S.difference (list2set (List.map REG (S.listItems rs)), pair2set caller_dst);
        val rs' = S.intersection(to_be_stored, S.union (pair2set outer_outs, list2set context));
        val pre_ins = trim_pair (PAIR (caller_src, set2pair rs'));
        val stored = (list2pair o to_stack o set2list) rs';
        val pre_outs = trim_pair (PAIR (callee_ins, stored));
        val body_ins = pre_outs;
        val body_outs = trim_pair(PAIR (callee_outs, stored));
        val post_ins = body_outs;
        val post_outs = trim_pair(PAIR (caller_dst, set2pair rs'));
        val context' = set2list (S.difference (list2set context, rs'))
    in
       ((pre_ins,pre_outs),(body_ins,body_outs),(post_ins,post_outs),set2list rs',context')
    end


val involved_defs = ref ([] : thm list);

fun convert_fcall (CALL(fname, pre, body, post, outer_info)) =
    let
        (* pass the arguments to the callee, and callee will save and restore anything	*)
	(* create the BL statement							*)
	(* then modify the sp to point to the real position of the returning arguments	*)

        val (outer_ins,outer_outs) = (#ins outer_info, #outs outer_info);
        val (caller_dst,caller_src) = let val x = get_annt body in (#outs x, #ins x) end;
        val {ir = (callee_ins, callee_ir, callee_outs), regs = rs, localNum = n, def = f_def, ...} = declFuncs.getFunc fname;
        val _ = involved_defs := (!involved_defs) @ [f_def];
        val ((pre_ins,pre_outs),(body_ins,body_outs),(post_ins,post_outs),rs',context) =
             compute_fcall_info ((outer_ins,outer_outs),(caller_src,caller_dst),(callee_ins,callee_outs),rs,#context outer_info);

	val reserve_space_for_outputs =
	        [dec_p (fromAlias sp) (length (pair2list caller_dst))];

        val pre' = rm_dummy_inst (BLK (
                        reserve_space_for_outputs @
                        pass_args (pair2list caller_src) @
                        entry_blk rs' n @
                        get_args (pair2list callee_ins),
                    {ins = pre_ins, outs = pre_outs, context = context, fspec = thm_t}));

        val body' = apply_to_info callee_ir (fn info' => {ins = body_ins, outs = body_outs, context = context, fspec = thm_t});

        val post' = rm_dummy_inst (BLK (
                        send_results (IR.pair2list callee_outs) (length (IR.pair2list callee_ins)) @
                         get_results (IR.pair2list caller_dst) @
                        exit_blk rs',
                    {ins = post_ins, outs = post_outs, context = context, fspec = thm_t}))

    in
        CALL(fname, pre', body', post', outer_info)
    end

 |  convert_fcall (SC(s1,s2,info)) = SC (convert_fcall s1, convert_fcall s2, info)
 |  convert_fcall (CJ(cond,s1,s2,info)) = CJ (cond, convert_fcall s1, convert_fcall s2, info)
 |  convert_fcall (TR(cond,s,info)) = TR (cond, convert_fcall s, info)
 |  convert_fcall ir = ir;


(* ---------------------------------------------------------------------------------------------------------------------*)
(* Link caller and callees together                                                                                     *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun link_ir prog =
  let
      val (fname, ftype, f_ir as (ins,ir0,outs), defs) = sfl2ir prog;
      val rs = S.addList (S.empty regAllocation.intOrder, get_modified_regs ir0);
      val (ins1,ir1,outs1, localNum) = calculate_relative_address (ins,ir0,outs,S.numItems rs);
      val _ = (involved_defs := [];
               declFuncs.putFunc (fname, ftype, (ins1,ir1,outs1), rs, localNum, (hd defs)));
      val ir2 = convert_fcall ir1
      val ir3 = match_ins_outs ir2
  in
      (fname,ftype,(ins1,ir3,outs1), defs @ (!involved_defs))
  end;


end (* local structure ... *)

end (* structure *)
