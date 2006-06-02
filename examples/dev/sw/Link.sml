structure Link =
struct

local
open HolKernel Parse boolLib
structure T = IntMapTable(type key = int  fun getInt n = n);
structure S = Binaryset
in
exception invalidArgs;
exception linkingError;
val numAvaiRegs = ref 10;

fun strOrder (s1:string,s2:string) =
    if s1 > s2 then GREATER
    else if s1 = s2 then EQUAL
    else LESS;

(* ---------------------------------------------------------------------------------------------------------------------*)
(* The configuaration for passing parameters, returning results and allocating stack space                              *)
(* The stack goes downward. 												*)
(* ---------------------------------------------------------------------------------------------------------------------*)
(*
                Address goes downward!!!

    caller's ip                 |  saved pc                     |
    caller's fp                 |  saved lr                     |
                                |  save sp                      |
                                |  save fp                      |
                                |  local variable 0             |
                                |  local variable 1             |
                                |       ...                     |
                                |  local variable n             |
                                |  output k from callee         |
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
                                |  local variable 0             |
                                |  local variable 1             |
                                |       ...                     |
    callee's sp                 |  local variable n'            |
*)


(* Distinguish inputs and local variables                                               *)
(* Calculate the offset based on fp of the temporaries bebing read in a callee		*)
(* If a temporary is an input, then read it from the stack where the caller sets 	*)
(* If it is a local variable, then read it from the current frame			*)

fun calculate_relative_address (args,stms,outs,numSavedRegs) =
  let
    (* Identify those TMEMs that are actually arguments *)
    val argT = #1 (List.foldl (fn (Assem.TMEM n, (t,i)) =>
                        (T.enter(t, n, i), i+1)
                    |  (arg, (t,i)) => (t, i+1)
                   )
                        (T.empty, 0)
                        (Assem.pair2list args)
                  );

    val i = ref 0
    val localT = ref (T.empty);   (* Table for the local variables *)

    (* For those TMEMs that are local variables, assign them in the stack according to the order of their apprearance *)
 
    fun filter_mems (Assem.TMEM n) =
        ( case T.peek (argT, n) of
                SOME k => (Assem.MEM {reg = Assem.fromAlias (Assem.FP), offset = 2 + k, wback = false})		(* inputs *)
           |     NONE => 
		( case T.peek(!localT, n) of 
		      SOME j => Assem.MEM {reg = Assem.fromAlias (Assem.FP), offset = ~3 - j - numSavedRegs, 
					   wback = false} (* existing local variable *)
		   |  NONE => 
			  ( localT := T.enter(!localT, n, !i);
			    i := !i + 1;
			    Assem.MEM {reg = Assem.fromAlias (Assem.FP), offset = ~3 - (!i - 1) - numSavedRegs, 
				       wback = false} (* local variables *)
			  )
		 )
        )
     |  filter_mems v = v

    fun one_stm (Assem.OPER {oper = op1, dst = dst1, src = src1, jump = jp1}) =
        Assem.OPER {oper = op1,
                    dst = List.map filter_mems dst1,
                    src = List.map filter_mems src1,
                    jump = jp1
                   }
     |  one_stm (Assem.MOVE {dst = dst1, src = src1}) =
         Assem.MOVE {dst = filter_mems dst1,
                     src = filter_mems src1}
     |  one_stm inst = inst

    fun adjust_exp (Assem.PAIR (e1,e2)) = 
		Assem.PAIR(adjust_exp e1, adjust_exp e2)
     |  adjust_exp e =
		filter_mems e 

  in
        (adjust_exp args, List.map one_stm stms, adjust_exp outs, T.numItems (!localT))
  end


(* ---------------------------------------------------------------------------------------------------------------------*)
(*                                                                                           *)
(* ---------------------------------------------------------------------------------------------------------------------*)

(* 	MOV     ip, sp
	STMFD   sp!, {fp,ip,lr,pc}
	SUB     fp, ip, #4
*)

fun entry_stms rs =
    [ Assem.MOVE {dst = Assem.REG (Assem.fromAlias Assem.IP), src = Assem.REG (Assem.fromAlias Assem.SP)}, 
      Assem.OPER {oper = (Assem.STMFD, NONE, false),
                  dst = [Assem.WREG (Assem.fromAlias Assem.SP)],
                  src = rs @ [Assem.REG (Assem.fromAlias Assem.FP), Assem.REG (Assem.fromAlias Assem.IP), 
			 Assem.REG (Assem.fromAlias Assem.LR), Assem.REG (Assem.fromAlias Assem.PC)],
                  jump = NONE},
      Assem.OPER  {oper = (Assem.SUB, NONE, false),
                     dst = [Assem.REG (Assem.fromAlias Assem.FP)],
                     src = [Assem.REG (Assem.fromAlias Assem.IP), Assem.NCONST Arbint.one],
                     jump = NONE}
    ]

(* 	LDMFD 	sp, {fp,sp,pc}									*)
fun exit_stms rs = 
    [ Assem.OPER {oper = (Assem.LDMFD, NONE, false),
                  src = [Assem.REG (Assem.fromAlias Assem.SP)],
                  dst = rs @ [Assem.REG (Assem.fromAlias Assem.FP), Assem.REG (Assem.fromAlias Assem.SP),
                         Assem.REG (Assem.fromAlias Assem.PC)],
                  jump = NONE}];


(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Decrease and increase the value of a register by n                                                                  *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun dec_p pt n = 
	Assem.OPER  {oper = (Assem.SUB, NONE, false),
                     dst = [Assem.REG pt],
                     src = [Assem.REG pt, Assem.NCONST (Arbint.fromInt n)],
                     jump = NONE}

fun inc_p pt n =
        Assem.OPER  {oper = (Assem.ADD, NONE, false),
                     dst = [Assem.REG pt],
                     src = [Assem.REG pt, Assem.NCONST (Arbint.fromInt n)],
                     jump = NONE};

(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Given a list of registers and memory slots, group consecutive registers together to be used by LDM and STM          *)
(*  For example, [r1,r2,m1,m3,r3,4w,r4,r5] is segmented to                                                              *)
(*  ([r1,r2],true, 0),(m1,false,2),(m3,false,3),([r3],true,4),(4w,false,5),([r4,r5],true,6)                             *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun mk_reg_segments argL =
  let val isBroken = ref false;      

      (* proceeds in reverse order of the list *)
      fun one_arg (Assem.REG r, (invRegLs, i)) =
	let val flag = !isBroken
	    val _ = isBroken := false
	in
	    if null invRegLs orelse flag then
	        (([Assem.REG r], true, i) :: invRegLs, i-1)
	    else
	        let val (cur_segL, a, j) = hd invRegLs
	        in 
	  	    if null cur_segL then (([Assem.REG r], true, i) :: (tl invRegLs), i-1)  
	  	    else ((Assem.REG r :: cur_segL, true, i) :: (tl invRegLs), i-1)
	        end
	end
      |	  one_arg (exp, (invRegLs, i)) = 
		(isBroken := true; (([exp],false, i) :: invRegLs, i-1)) 

      val (invRegLs, i) = List.foldr one_arg ([], length argL - 1) argL 

  in
      invRegLs
  end

(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Given a list of registers, generate a LDM or STM statement                                                          *)
(*  The sp is assumed to be in the right position                                                                       *)
(*  If the list contain only one resiter, then use LDR and STR instead                                                  *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun mk_ldm_stm isLoad r dataL =
    if isLoad then
	if length dataL = 1 then
	        Assem.OPER {oper = (Assem.LDR, NONE, false),
                  src = [Assem.MEM {reg = r, offset = 1, wback = false}],
                  dst = dataL,
                  jump = NONE}
	else	    
        	Assem.OPER {oper = (Assem.LDMFD, NONE, false),
                  src = [Assem.REG r],
                  dst = dataL,
                  jump = NONE}
    else 
	if length dataL = 1 then
                Assem.OPER {oper = (Assem.STR, NONE, false),
                  dst = [Assem.MEM {reg = r, offset = 0, wback = false}],
                  src = dataL,
                  jump = NONE}
	else
		Assem.OPER {oper = (Assem.STMFD, NONE, false),
                  dst = [Assem.WREG r],
                  src = dataL,
                  jump = NONE}

(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Write one argument to the memory slot referred by regNo and offset      			                        *)
(*  Push arguments to the stack. If the argument comes from a register, and store it into the stack directly; 		*)
(*  if it comes from memory, then first load it into R10, and then store it into the stack;				*) 
(*  if it is a constant, then assign it to r10 first then store it into the stack.                                      *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun write_one_arg (Assem.MEM v) (regNo,offset) = [
                 Assem.OPER {oper = (Assem.LDR, NONE, false),
                             dst = [Assem.REG (!numAvaiRegs)],
                             src = [Assem.MEM v],
                             jump = NONE},
                 Assem.OPER {oper = (Assem.STR, NONE, false),
                             dst = [Assem.MEM {reg = regNo,
                                               offset = offset, wback = false}],
                             src = [Assem.REG (!numAvaiRegs)],
                             jump = NONE}]
 |  write_one_arg (Assem.REG r) (regNo,offset) =   
                 [Assem.OPER  {oper = (Assem.STR, NONE, false),
                               dst = [Assem.MEM {reg = regNo,
                                                 offset = offset,
                                                 wback = false}],
                               src = [Assem.REG r],
                               jump = NONE}]
 |  write_one_arg v (regNo,offset) =   (* v = NONCST n or WCONST w *)
                 [Assem.MOVE {dst = Assem.REG 10, src = v},
		  Assem.OPER  {oper = (Assem.STR, NONE, false),
                               dst = [Assem.MEM {reg = regNo,
                                                 offset = offset,
                                                 wback = false}],
                               src = [Assem.REG 10],
                               jump = NONE}]


(* ---------------------------------------------------------------------------------------------------------------------*)
(*  Read one argument from the memory slot referred by regNo and offset                                                 *)
(*  If the destination is a register, then load it into the register directly;                                          *)
(*  if it is in the memory, then first load the value into R10, and then store it into that memory location;            *)
(*  The destination couldn't be a constant                                                                              *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun read_one_arg (Assem.REG r) (regNo,offset) = 
		[Assem.OPER  {oper = (Assem.LDR, NONE, false),
                              dst = [Assem.REG r],
                              src = [Assem.MEM {reg = regNo,
                                                offset = offset,
                                                wback = false}],
                              jump = NONE}]
 |  read_one_arg (Assem.MEM v) (regNo,offset) = [
                 Assem.OPER {oper = (Assem.LDR, NONE, false),
                             dst = [Assem.REG (!numAvaiRegs)],
                             src = [Assem.MEM {reg = regNo,
                                               offset = offset, wback = false}],
                             jump = NONE},
                 Assem.OPER {oper = (Assem.STR, NONE, false),
                             dst = [Assem.MEM v],
                             src = [Assem.REG (!numAvaiRegs)],
                             jump = NONE}]
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
(* Note that the elements in the list are stored in the memory from high addresses to low addressed                     *) 
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
  pushL (Assem.fromAlias Assem.SP) (List.rev argL)

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

       fun mk_regL 0 = [Assem.REG 0]
	|  mk_regL n = mk_regL (n-1) @ [Assem.REG n];

   in 
       popL (Assem.fromAlias (Assem.IP)) argL
       (* Note that callee's IP equals to caller's sp, we use the IP here to load the arguments *) 
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
       val stms = pushL (Assem.fromAlias Assem.SP) (List.rev outL)
   in
	Assem.OPER { oper = (Assem.ADD,NONE,false),
		     dst = [Assem.REG (Assem.fromAlias Assem.SP)],
		     src = [Assem.REG (Assem.fromAlias Assem.FP), Assem.NCONST (Arbint.fromInt sOffset)],
		     jump = NONE
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

fun get_results outL numArgs =
   let
       val sOffset = numArgs;  (* skip the arguments and the saved pc *)
   in
	inc_p (Assem.fromAlias Assem.SP) sOffset :: 
        popL (Assem.fromAlias (Assem.SP)) outL
   end;


(* ---------------------------------------------------------------------------------------------------------------------*)
(* Tail recursive procedure gets back the resutls returned by previous round                                               *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun get_results_by_recursive_procedure outL =
    popL (Assem.fromAlias (Assem.SP)) outL;


(* ---------------------------------------------------------------------------------------------------------------------*)
(* Remove redundant instructions											*)
(* There are a couple of cases to be considered:                                                                        *)
(*   1. When the destination register and source register of an MOVE instruction is the same, remove this instruction   *)
(*   2. All instructions following an BAL instruction are dead codes provided that there are not the targets of some    *)
(*         jumps (that is, these instructions will be kept only if the control flow would go back to them)              *)
(*   3. For some arithmetic instructions and logical instructions, if one of the operands is 0, then the operations     *)
(*         need not to be performed                                                                                     *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun rm_redundancy stms =
  let
     val enterDeadCode = ref false;

     fun isValid (Assem.MOVE{dst = d, src = r}) =
                not (d = r) andalso not (!enterDeadCode)
      |  isValid (Assem.OPER {oper = (Assem.B, SOME (Assem.AL), flag), ...}) =
                let val flag = !enterDeadCode
                in
                    (enterDeadCode := true; not flag)
                end
      |  isValid (Assem.LABEL {...}) = 
		  (enterDeadCode := false; true)
      |  isValid (Assem.OPER{oper = (op1,cond1,flag), dst = dst1, src = src1, jump = jp1}) =
              not (!enterDeadCode) andalso
              not ( length src1 = 2 andalso (hd dst1 = hd src1) andalso (hd (tl src1) = Assem.NCONST Arbint.zero) andalso
                    (op1 = Assem.ADD orelse op1 = Assem.SUB orelse op1 = Assem.LSL orelse
                     op1 = Assem.LSR orelse op1 = Assem.ASR orelse op1 = Assem.ROR))
  in
     List.filter isValid stms
  end;

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Link caller and callees together                                                                                     *)
(* ---------------------------------------------------------------------------------------------------------------------*)

val called = ref(Binaryset.empty strOrder);
val processed = ref(Binaryset.empty strOrder);

fun caller_procedure (caller_name,args,stms,outs) =
  let

    fun one_stm (fun_name,args) (Assem.OPER {oper = (Assem.BL,c1,flag), dst = caller_dst, src = caller_src, jump = SOME labs}) =
	let
	    val callee_name = Symbol.name (hd labs) 
        in

	    if callee_name = fun_name then 	(* tail recursion	*)
		 (pass_args caller_src) @ (get_results_by_recursive_procedure (Assem.pair2list args)) @
		 [Assem.OPER {oper = (Assem.B,SOME (Assem.AL),false), dst = [], src = [],
		  	      jump = SOME [Temp.namedlabel (callee_name ^ "_0")]}]

            else
	   	let
		    val _ = called := Binaryset.add(!called, callee_name);
	
		    (* pass the arguments to the callee, and callee will save and restore anything	*)
		    (* create the BL statement							*)
		    (* then modify the sp to point to the real position of the returning arguments	*)

		    val reserve_space_for_outputs = 
			dec_p (Assem.fromAlias Assem.SP) (length caller_dst)
		in
			reserve_space_for_outputs :: 
			pass_args caller_src @ 
			[Assem.OPER {oper = (Assem.BL,NONE,false), dst = [], src = [],
			             jump = SOME labs}] @
			get_results caller_dst (length caller_src) 
                end
     	end
     |  one_stm (fun_name,args) others = [others]

  in
  	List.foldl (fn (inst,body) => body @ one_stm (caller_name, args) inst) [] stms
  end

	
fun callee_procedure name =
    let
        val {name = fun_name, ftype = fun_type, args = callee_args, stms = callee_stms, outs = callee_outs, regs = rs} 
		= declFuncs.getFunc name;

	val (p_lab, q_lab) = ( Assem.LABEL {lab = Temp.namedlabel fun_name},
                               Assem.LABEL {lab = Temp.namedlabel (fun_name ^ "_0")})

	val (args1, stms1, outs1, numLocal) = calculate_relative_address
				(callee_args,callee_stms,callee_outs, S.numItems rs) 

        val stms_to_get_args = get_args (Assem.pair2list args1)

        val modifiedRegs = Binaryset.listItems (S.difference(S.union (rs, regAllocation.getModifiedRegs stms_to_get_args),
				     S.add(S.empty regAllocation.regOrder, Assem.REG (Assem.fromAlias Assem.IP))));

	val reverse_space_for_locals = [dec_p (Assem.fromAlias Assem.SP) numLocal];

	val move_sp = 
		Assem.OPER  {oper = (Assem.SUB, NONE, false),
                     dst = [Assem.REG (Assem.fromAlias Assem.SP)],
                     src = [Assem.REG (Assem.fromAlias Assem.FP), Assem.NCONST (Arbint.fromInt (length modifiedRegs + 3))],
                     jump = NONE}
	val stms1 =  p_lab ::
          	     entry_stms modifiedRegs @
		     reverse_space_for_locals @
		     stms_to_get_args @
          	     [q_lab] @
          	     tl (caller_procedure (fun_name,args1,stms1,outs1)) @
          	     send_results (Assem.pair2list outs1) (length (Assem.pair2list args1)) @
          	     [move_sp] @   (* skip save_lr,save_sp,save_fp and saved registers *)
          	     exit_stms modifiedRegs

    in
	( fun_name, fun_type, callee_args, rm_redundancy stms1, callee_outs, rs)
    end


fun expand (fun_name,fun_type,args,stms,outs,rs) = 
  let val _ = (called := Binaryset.add(Binaryset.empty strOrder, fun_name); processed := !called);

      val return_stm = [Assem.MOVE {dst = Assem.REG (Assem.fromAlias Assem.PC),
				    src = Assem.REG (Assem.fromAlias Assem.LR)}]

      val (args1, stms1, outs1, numLocal) = calculate_relative_address(args,stms,outs,0)

      val (p_lab, q_lab) = ( Assem.LABEL {lab = Temp.namedlabel fun_name},
			     Assem.LABEL {lab = Temp.namedlabel (fun_name ^ "_0")})	

      val reverse_space_for_locals = [dec_p (Assem.fromAlias Assem.SP) numLocal];

      val move_sp =
                Assem.OPER  {oper = (Assem.SUB, NONE, false),
                     dst = [Assem.REG (Assem.fromAlias Assem.SP)],
                     src = [Assem.REG (Assem.fromAlias Assem.FP), Assem.NCONST (Arbint.fromInt 3)],
                     jump = NONE}

      fun callees () = 
	if Binaryset.equal(!called, !processed) then [] else
	let val p = hd (Binaryset.listItems (Binaryset.difference(!called, !processed))); 
	    val _ = processed := Binaryset.add(!processed, p)
        in (callee_procedure p) :: callees () end

      val stms1 =  p_lab ::
          	   entry_stms [] @
		   reverse_space_for_locals @
          	   [q_lab] @
          	   tl (caller_procedure (fun_name,args1,stms1,outs1)) @
          	   [move_sp] @                   (* skip save_lr,save_sp,save_fp *)
          	   exit_stms []

  in
	(fun_name, fun_type, args1, rm_redundancy stms1, outs1, rs)
	:: callees()
  end

fun link prog = 
  let
    val (fname, ftype, args, gr, outs, rs) = regAllocation.convert_to_ARM prog;
    val _ = (called := Binaryset.add (Binaryset.empty strOrder, fname))
  in
    expand (fname, ftype, args, CFG.linearizeCFG gr, outs, rs)
  end;

fun rm_labels arm = 
  let
    exception label_not_found
    val hashtable : ((string,int) Polyhash.hash_table) =
                Polyhash.mkTable(Polyhash.hash, op = ) (128, label_not_found)

    val index = ref 0;
    
    val stms = List.foldl (fn ((fname,ftype,args,insts,outs,rs),insts1) => 
				insts1 @ insts) [] arm;

    val new_stms = List.filter (fn (Assem.LABEL {lab = l}) => (
					Polyhash.insert (hashtable) (Symbol.name l,!index);
					false)
				|  _ => (index := !index + 1; true)) stms;

    fun one_stm (Assem.OPER {oper = op1, dst = d1, src = s1, jump = SOME labs}) =
	let val k:int = Polyhash.find hashtable (Symbol.name (hd labs));
	    val new_stm =  
	      if (!index < k) then
		(Assem.OPER {oper = op1, dst = d1, src = s1, jump = SOME [Symbol.mkSymbol "+" (k - (!index))]})
	      else (Assem.OPER {oper = op1, dst = d1, src = s1, jump = SOME [Symbol.mkSymbol "-" (!index - k)]});
	    val _ = index := !index + 1
	in
	    [new_stm]
	end
    | one_stm (Assem.LABEL {...}) = []
    | one_stm inst = (index := !index + 1;[inst])

    fun one_fun (fname,ftype,args,insts,outs,rs) = 
	(fname, ftype, args, List.foldl (fn (inst,L) => L @ one_stm inst) [] insts, outs, rs)

  in
    (index := 0; List.map one_fun arm)
  end

fun link2 prog =
  rm_labels (link prog);

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Print ARM programs													*)
(* ---------------------------------------------------------------------------------------------------------------------*)

val lineNo = ref ~1;

fun printInsts stms = 
  let 
      fun formatNextLineNo () =
          ( lineNo := !lineNo + 1;
            "  " ^
            ( if !lineNo < 10 then "  " ^ Int.toString (!lineNo)
              else if !lineNo < 100 then " " ^ Int.toString (!lineNo)
              else Int.toString (!lineNo)
            ) ^
            ":"
          )
  in
      List.map (fn stm => print ((formatNextLineNo() ^  "  " ^ Assem.formatInst stm) ^ "\n")) stms
  end

val print_structure = ref true;

fun printarm (progL,anfL) =
   let 
       val _ = lineNo := ~1;
       fun one_fun flag(fname,ftype,args,stms,outs,rs) = 
   	 ( 
	  (if flag then 
	      ( print "*****************************************************************\n";
	    	print ("  Name              : " ^ fname ^ "\n");
     	        print "  Arguments         : ";
     	        List.map (fn arg => print (Assem.one_exp arg ^ " ")) (Assem.pair2list args);
	        print "\n  Modified Registers: ";
                List.map (fn arg => print (Assem.one_exp arg ^ " ")) (Binaryset.listItems rs);
	        print "\n  Returns           : ";
                List.map (fn arg => print (Assem.one_exp arg ^ " ")) (Assem.pair2list outs);
     	        print "\n  Body: \n"
	      )
	   else print "");
     	  printInsts stms
   	 )
   in
      ( one_fun true (hd progL); 
        List.map (one_fun (!print_structure)) (tl progL)
      )
   end

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Compile the environment given by the CPS/ANF compiler                                                                *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun compileEnv (env:(term * (bool * thm * thm * thm)) list) =
     let val defs = List.foldr (fn ((name, (flag,src,anf,cps)), state) =>
		(if declFuncs.is_decl (#1 (dest_const name)) then (src::state) else (link anf;src::state))) [] (tl env);
         val (name, (flag,src,anf,cps)) = hd env
     in 
	(link2 anf, src::defs)
     end

end (* local structure ... *)

end (* structure *)
