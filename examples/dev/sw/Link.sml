structure Link = 
struct

local 
open HolKernel Parse boolLib
structure S = Binaryset;
structure G = Graph;
structure T = IntMapTable(type key = int  fun getInt n = n);
in
exception invalidArgs;
exception linkingError;
val numAvaiRegs = ref 10;

fun strOrder (s1:string,s2:string) =
    if s1 > s2 then GREATER
    else if s1 = s2 then EQUAL
    else LESS;

(* ---------------------------------------------------------------------------------------------------------------------*)
(*                                                                                           *)
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
    val argT = #1 (List.foldl (fn (Assem.TMEM n, (t,i)) =>
                        (T.enter(t, n, i), i+1)
                    |  (arg, (t,i)) => (t, i+1)
                   )
                        (T.empty, 0)
                        (Assem.pair2list args)
                  );

    val i = ref 0

    fun filter_mems (Assem.TMEM n) =
        ( case T.peek (argT, n) of
                SOME k => (Assem.MEM {reg = Assem.fromAlias (Assem.FP), offset = 2 + k, wback = false})		(* inputs *)
           |     NONE => ( i := !i + 1; 
			   Assem.MEM {reg = Assem.fromAlias (Assem.FP), offset = ~3 - (!i - 1) - numSavedRegs, wback = false}) (* local variables *)
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
        (adjust_exp args, List.map one_stm stms, adjust_exp outs, !i + 1)
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
                     src = [Assem.REG (Assem.fromAlias Assem.IP), Assem.NCONST 1],
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
(*                                                                                           *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun dec_p pt n = 
	Assem.OPER  {oper = (Assem.SUB, NONE, false),
                     dst = [Assem.REG (Assem.fromAlias pt)],
                     src = [Assem.REG (Assem.fromAlias pt), Assem.NCONST n],
                     jump = NONE}

fun inc_p pt n =
        Assem.OPER  {oper = (Assem.ADD, NONE, false),
                     dst = [Assem.REG (Assem.fromAlias pt)],
                     src = [Assem.REG (Assem.fromAlias pt), Assem.NCONST n],
                     jump = NONE};


fun mk_reg_segments argL =
  let val isBroken = ref false;      

      fun one_arg (Assem.REG r, (invRegLs, memL, i)) =
	let val flag = !isBroken
	    val _ = isBroken := false
	in
	    if null invRegLs orelse flag then
	        (([Assem.REG r], i) :: invRegLs, memL, i+1)
	    else
	        let val (cur_segL, j) = hd invRegLs
	        in 
	  	    if null cur_segL then (([Assem.REG r], i) :: (tl invRegLs), memL, i+1)  
	  	    else ((cur_segL @ [Assem.REG r], j) :: (tl invRegLs), memL, i+1)
	        end
	end
      |	  one_arg (Assem.MEM v, (invRegLs, memL, i)) = 
		(isBroken := true; (invRegLs, memL @ [(Assem.MEM v,i)], i+1)) 
      |   one_arg _ = 
		raise invalidArgs

      val (invRegLs, memL, i) = List.foldl one_arg ([],[],0) argL 

  in
      (invRegLs, memL)
  end

fun mk_ldm_stm isLoad dataL =
    if isLoad then
	if length dataL = 1 then
	        Assem.OPER {oper = (Assem.LDR, NONE, false),
                  src = [Assem.MEM {reg = Assem.fromAlias Assem.SP, offset = 1, wback = false}],
                  dst = dataL,
                  jump = NONE}
	else	    
        	Assem.OPER {oper = (Assem.LDMFD, NONE, false),
                  src = [Assem.REG (Assem.fromAlias Assem.SP)],
                  dst = dataL,
                  jump = NONE}
    else 
	if length dataL = 1 then
                Assem.OPER {oper = (Assem.STR, NONE, false),
                  dst = [Assem.MEM {reg = Assem.fromAlias Assem.SP, offset = 0, wback = false}],
                  src = dataL,
                  jump = NONE}
	else
		Assem.OPER {oper = (Assem.STMFD, NONE, false),
                  dst = [Assem.WREG (Assem.fromAlias Assem.SP)],
                  src = dataL,
                  jump = NONE}


(* write one argument to the memory slot referred by regNo and offset						*)

fun write_one_arg (Assem.REG r) (regNo,offset) = 
		[Assem.OPER  {oper = (Assem.STR, NONE, false),
                                      dst = [Assem.MEM {reg = regNo,
                                                        offset = offset,
                                                        wback = false}],
                                      src = [Assem.REG r],
                                      jump = NONE}]
 |  write_one_arg (Assem.MEM v) (regNo,offset) = [
                 Assem.OPER {oper = (Assem.LDR, NONE, false),
                             dst = [Assem.REG 10],
                             src = [Assem.MEM v],
                             jump = NONE},
                 Assem.OPER {oper = (Assem.STR, NONE, false),
                             dst = [Assem.MEM {reg = regNo,
                                               offset = offset, wback = false}],
                             src = [Assem.REG 10],
                             jump = NONE}]
 |  write_one_arg _ _  =
                 raise invalidArgs


fun read_one_arg (Assem.REG r) (regNo,offset) = 
		[Assem.OPER  {oper = (Assem.LDR, NONE, false),
                              dst = [Assem.REG r],
                              src = [Assem.MEM {reg = regNo,
                                                offset = offset,
                                                wback = false}],
                              jump = NONE}]
 |  read_one_arg (Assem.MEM v) (regNo,offset) = [
                 Assem.OPER {oper = (Assem.LDR, NONE, false),
                             dst = [Assem.REG 10],
                             src = [Assem.MEM {reg = regNo,
                                               offset = offset, wback = false}],
                             jump = NONE},
                 Assem.OPER {oper = (Assem.STR, NONE, false),
                             dst = [Assem.MEM v],
                             src = [Assem.REG 10],
                             jump = NONE}]
 |  read_one_arg _ _ =
                 raise invalidArgs


(* push arguments to the stack. If the argument comes from a register, and store it into the stack directly; 		*)
(* if it comes from memory, then first load it into R0, and then store it into the stack				*) 

val argL1 = [Assem.MEM {reg = 10, offset = 1, wback = false}, Assem.REG 0, Assem.REG 1, Assem.MEM {reg = 10, offset = 0, wback = false},
          Assem.REG 4, Assem.REG 8]

fun pass_args argL =
   let 
       val regs0_4 = [Assem.REG 0, Assem.REG 1, Assem.REG 2, Assem.REG 3] 	
       val (inRegs, res0_4) = if length argL < 4 then (argL, List.take(regs0_4,length argL))
		      else (List.take(argL,4), regs0_4) 

       val first4Args =  
		[ Assem.OPER {oper = (Assem.LDMFD,NONE,false),
		   	      src = [Assem.REG (Assem.fromAlias (Assem.SP))],
			      dst = res0_4,
			      jump = NONE}
		]

       val (regLs, memL) = mk_reg_segments argL

       val (store_regs, final_upper) = List.foldl (fn ((argL,offset), (instL,upper)) => 
				(instL @ [dec_p Assem.SP (upper - offset - length argL)] @ 
				 [mk_ldm_stm false argL], offset))    
			([],length argL) regLs
       val store_mems = List.foldl (fn ((arg,offset),instL) => instL @ write_one_arg arg (13,~1 * offset)) 
				[] memL
   in
	(* save in-memory arguments first, then STMFD the register segments		*)  
	store_mems @ store_regs @ [dec_p Assem.SP final_upper] @ first4Args 
   end


fun send_results outL numArgs =
   let
       val sOffset = length outL + numArgs + 1;  (* skip the arguments *)

       val (regLs, memL) = mk_reg_segments outL

       val (store_regs, final_upper) = List.foldl (fn ((outL,offset), (instL,upper)) =>
                                (instL @ [dec_p Assem.SP (upper - offset - length outL)] @
                                 [mk_ldm_stm false outL], offset))
                        ([],length outL) regLs
       val store_mems = List.foldl (fn ((out,offset),instL) => instL @ write_one_arg out (13,~1 * offset))
                                [] memL

   in
	Assem.OPER { oper = (Assem.ADD,NONE,false),
		     dst = [Assem.REG (Assem.fromAlias Assem.SP)],
		     src = [Assem.REG (Assem.fromAlias Assem.FP), Assem.NCONST sOffset],
		     jump = NONE
		   }
 	:: store_mems @ store_regs
   end


fun get_results outL numArgs =
   let
       val sOffset = numArgs + 1;  (* skip the arguments and the saved pc *)

       val (regLs, memL) = mk_reg_segments outL

       val (load_regs, final_upper) = List.foldl (fn ((outL,offset), (instL,upper)) =>
                                (instL @ [inc_p Assem.SP (offset - upper)] @
                                 [mk_ldm_stm true outL], offset))
                        ([],0) (rev regLs)
       val load_mems = List.foldl (fn ((out,offset),instL) => instL @ read_one_arg out (13, offset))
                                [] memL

   in
	inc_p Assem.SP sOffset :: 
	load_mems @ load_regs @ [inc_p Assem.SP (length outL - final_upper)] 
   end;


(* ---------------------------------------------------------------------------------------------------------------------*)
(*                                                                                           *)
(* ---------------------------------------------------------------------------------------------------------------------*)

val called = ref(Binaryset.empty strOrder);
val processed = ref(Binaryset.empty strOrder);

fun one_program (caller_name,args,stms,outs) =
  let

    fun one_stm (fun_name,args) (Assem.OPER {oper = (Assem.BL,c1,flag), dst = caller_dst, src = caller_src, jump = SOME labs}) =
	let
	    val callee_name = Symbol.name (hd labs) 
        in

	    if callee_name = fun_name then 	(* tail recursion	*)
		 (pass_args caller_src) @ 
		 [inc_p Assem.SP (length caller_src)] @	(* drop from the stack the arguments/results of this round	*)
		 [Assem.OPER {oper = (Assem.B,SOME (Assem.AL),false), dst = [], src = [],
		  	      jump = SOME [Temp.namedlabel (callee_name ^ "_0")]}]
		(* We don't need to get the results here due to tail recursion wouldn't use it		*)    		
            else
	   	let
		    val _ = called := Binaryset.add(!called, callee_name);
	
		    (* pass the arguments to the callee, and callee will save and restore anything	*)
		    (* create the BL statement							*)
		    (* then modify the sp to point to the real position of the returning arguments	*)

		    val reserve_space_for_outputs = 
			dec_p Assem.SP (length caller_dst)
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
        val {name = fun_name, args = callee_args, stms = callee_stms, outs = callee_outs, regs = rs} 
		= declFuncs.getFunc name;

	val (p_lab, q_lab) = ( Assem.LABEL {lab = Temp.namedlabel fun_name},
                               Assem.LABEL {lab = Temp.namedlabel (fun_name ^ "_0")})

        val modifiedRegs = Binaryset.listItems rs;
	val (args1, stms1, outs1, numLocal) = calculate_relative_address(callee_args,callee_stms,callee_outs,length modifiedRegs) 

	val move_sp = 
		Assem.OPER  {oper = (Assem.SUB, NONE, false),
                     dst = [Assem.REG (Assem.fromAlias Assem.SP)],
                     src = [Assem.REG (Assem.fromAlias Assem.FP), Assem.NCONST (numLocal + length modifiedRegs + 2)],
                     jump = NONE}
	

    in
        p_lab :: 
	entry_stms modifiedRegs @
	[q_lab] @
	tl (one_program (fun_name,args1,stms1,outs1)) @
	send_results (Assem.pair2list outs1) (length (Assem.pair2list args1)) @
	[move_sp] @	(* skip save_lr,save_sp,save_fp and local variables *)
	exit_stms modifiedRegs
    end


fun expand (fun_name,args,stms,outs,rs) = 
  let val _ = (called := Binaryset.add(Binaryset.empty strOrder, fun_name); processed := !called);

      val return_stm = [Assem.MOVE {dst = Assem.REG (Assem.fromAlias Assem.PC),
				    src = Assem.REG (Assem.fromAlias Assem.LR)}]

      val rs = S.listItems rs;
      val (args1, stms1, outs1, numLocal) = calculate_relative_address(args,stms,outs,length rs)

      val (p_lab, q_lab) = ( Assem.LABEL {lab = Temp.namedlabel fun_name},
			     Assem.LABEL {lab = Temp.namedlabel (fun_name ^ "_0")})	
      
      val move_sp =
                Assem.OPER  {oper = (Assem.SUB, NONE, false),
                     dst = [Assem.REG (Assem.fromAlias Assem.SP)],
                     src = [Assem.REG (Assem.fromAlias Assem.FP), Assem.NCONST (numLocal + length rs + 1)],
                     jump = NONE}

      fun callees () = 
	if Binaryset.equal(!called, !processed) then [] else
	let val p = hd (Binaryset.listItems (Binaryset.difference(!called, !processed))); 
	    val _ = processed := Binaryset.add(!processed, p)
        in (callee_procedure p) @ callees () end
  in
	( args1,
	  p_lab ::
          entry_stms rs @
	  [q_lab] @
	  tl (one_program(fun_name,args1,stms1,outs1)) @ 
	  [move_sp] @ 			(* skip save_lr,save_sp,save_fp and local variables *)
	  exit_stms rs @ callees (), 
	  outs1)
  end      


fun rm_redundancy stms = 
  let 
     val isPrevBAL = ref false;

     fun isValid (Assem.MOVE{dst = d, src = r}) =
		not (d = r)
      |  isValid (Assem.OPER {oper = (Assem.B, SOME (Assem.AL), flag), ...}) =
		let val flag = !isPrevBAL
		in (isPrevBAL := true; not flag)
		end
      |  isValid (Assem.OPER{oper = (op1,cond1,flag), dst = dst1, src = src1, jump = jp1}) =
	      not ( length src1 = 2 andalso (hd dst1 = hd src1) andalso (hd (tl src1) = Assem.NCONST 0) andalso
		    (op1 = Assem.ADD orelse op1 = Assem.SUB orelse op1 = Assem.LSL orelse
		     op1 = Assem.LSR orelse op1 = Assem.ASR orelse op1 = Assem.ROR))
      |  isValid _ = true	       
  in
     List.filter isValid stms
  end;


fun link prog = 

  let 
    val (fname, ftype, args, stms, outs, rs) = 
         regAllocation.convert_to_ARM (prog, !numAvaiRegs);
    val _ = (called := Binaryset.add (Binaryset.empty strOrder, fname))
    val (args1, stms1, outs1) = expand (fname, args, stms, outs, rs)
  in
    (fname, ftype, args1, rm_redundancy stms1, outs1)
  end;

fun rm_labels stms = 
  let
    exception label_not_found
    val hashtable : ((string,int) Polyhash.hash_table) =
                Polyhash.mkTable(Polyhash.hash, op = ) (128, label_not_found)

    val index = ref 0;
    
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
	    new_stm
	end
    | one_stm inst = (index := !index + 1;inst)
  in
    (index := 0; List.map one_stm new_stms)
  end

fun link2 prog =
 let
     val (fname, ftype, args, stms, outs) = link prog
     val stms1 = rm_labels stms;
     val stms2 = stms1 
  in
     (fname, ftype, args, stms2, outs)
  end


fun printInsts stms = 
  let val lineNo = ref ~1;

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

fun printarm (fname,ftype,args,stms,outs) =
   ( print ("Name: " ^ fname ^ "\n");
     print "Arguments: \n    ";
     List.map (fn arg => print (Assem.one_exp arg ^ " ")) (Assem.pair2list args);
     print "\nBody: \n";
     printInsts stms;
     print "Return: \n    ";
     List.map (fn arg => print (Assem.one_exp arg ^ " ")) (Assem.pair2list outs)
   )


fun compileEnv (env:(term * (bool * thm * thm * thm)) list) =
     let val _ = List.foldr (fn ((name, (flag,src,anf,cps)), state) =>
		(link anf; ())) () (tl env);
         val (name, (flag,src,anf,cps)) = hd env
     in 
	link2 anf
     end

end (* local structure ... *)

end (* structure *)
