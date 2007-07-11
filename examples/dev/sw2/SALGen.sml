structure SALGen :> SALGen =
struct

(* Interactive
quietdec := true;
app load ["pairLib","basic", "SALTheory"];
open pairLib pairSyntax PairRules numSyntax basic SALTheory;
quietdec := false;
*)

open HolKernel Parse boolLib pairLib pairSyntax bossLib ;
open PairRules numSyntax basic SALTheory;

val ERR = mk_HOL_ERR "SALGen";

(* --------------------------------------------------------------------*)
(* Generate SAL code for a FIL program                                 *)
(* --------------------------------------------------------------------*)

structure M = Binarymap
structure S = Binaryset
val VarType = ref (Type `:word32`) (* numSyntax.num *)

(* --------------------------------------------------------------------*)
(* Datatypes, Commonly-used variables and functions                    *)
(* --------------------------------------------------------------------*)

val nop = prim_mk_const{Name="NOP",Thy="SAL"};
val reduce_tm = prim_mk_const{Name="Reduce",Thy="SAL"};
val union_tm = prim_mk_const{Name="UNION",Thy="SAL"};
val asg_tm = prim_mk_const{Name="ASG",Thy="SAL"};
val ifgoto_tm = prim_mk_const{Name="IFGOTO",Thy="SAL"};
val goto_tm = prim_mk_const{Name="GOTO",Thy="SAL"};

fun dest_composite ty = 
 case total dest_thy_type ty
  of SOME {Tyop="COMPOSITE",Thy="SAL",Args=[x]} => x
   | other => raise ERR "dest_composite" "";
   
(* --------------------------------------------------------------------*)
(* Auxiliary functions manipulating labels                             *)
(* --------------------------------------------------------------------*)

val label_tm = prim_mk_const{Name="L",Thy="SAL"};

fun mk_label i = mk_comb(label_tm, term_of_int i);

val label_index = ref 0;

fun reset_label () = label_index := 0
fun cur_label() = mk_label (!label_index)

fun next_label () = 
  let val _ = label_index := !label_index + 1;
  in  
      mk_label (!label_index)
  end;

(* ---------------------------------------------------------------------*)
(* Mechanism for mechanical reasoning                                   *)
(* A specification stores all information about a FIL program including *)
(* a theorem stating that the SAL code "implements" the FIL program.    *)
(* The composition of specifications is directed by the syntax of the   *)
(* program and goes in a bottom-up manner.                              *) 
(* ---------------------------------------------------------------------*)

type spec_type = {body : term, dst : term, entry : term, exit : term, exp : term, thm : thm}

(* Make a basic specification for single assignment instruction *)

fun mk_instr_spec (entry_l,exit_l) (dest,src) =
  let
    val ty = type_of dest
    val value = mk_pair (src, dest)
    val instr = list_mk_comb (inst [alpha |-> ty] asg_tm, [entry_l, dest, src, exit_l])
    val s = list_mk_pair [entry_l, instr, exit_l]
    val spec = list_mk_comb(inst [alpha |-> ty] reduce_tm, [s, value])
    val spec_thm = prove(spec, SIMP_TAC std_ss [inst_rule])
  in
    {entry = entry_l, exit = exit_l, body = instr, thm = spec_thm, exp = src, dst = dest}
  end

(* Union of two structures (i.e. sequential composition *)

fun mk_union_spec (spec1:spec_type) (spec2:spec_type) =
  let (*  s1 |+| s2 *)
      val union_body = list_mk_comb(inst [alpha |-> !VarType] union_tm, [#body spec1, #body spec2])
      val exp = mk_plet (#dst spec1, #exp spec1, 
			 mk_comb(mk_pabs (#dst spec1, #exp spec2), #dst spec1))
      val value = mk_pair(exp, #dst spec2)
      val s = list_mk_pair [#entry spec1, union_body, #exit spec2]
      val spec = list_mk_comb(inst [alpha |-> !VarType] reduce_tm, [s, value])

      val spec_lem =  prove (spec,   (* set_goal ([], spec) *)
                       MATCH_MP_TAC seq_rule THEN
                       EXISTS_TAC (#exit spec1) THEN EXISTS_TAC (#dst spec1) THEN
                       PBETA_TAC THEN 
		       REWRITE_TAC [#thm spec1, #thm spec2]
                      )
     val spec_thm = PBETA_RULE spec_lem   
  in
     {entry = #entry spec1, exit = #exit spec2, body = union_body, thm = spec_thm, exp = exp, dst = #dst spec2}
  end

(* --------------------------------------------------------------------*)
(* Eliminate the deepest "let" expression. It is for optiomization.    *)
(* --------------------------------------------------------------------*)

val ELIM_DEEP_LET_CONV =
   let
     val elim_deep_let_conv = (fn t => (DEPTH_CONV (SIMP_CONV bool_ss [Once LET_THM])) t)
   in
     RATOR_CONV elim_deep_let_conv THENC
     RAND_CONV elim_deep_let_conv 
   end;

(* --------------------------------------------------------------------*)
(* Compose the specifications in a bottom-up manner.                   *)
(* --------------------------------------------------------------------*)

(* Generate specification for conditional structures.                  *)

fun mk_cond_spec (entry_l,exit_l) (dest,src) args = 
   let
       val (J,M1,M2) = dest_cond src

       val args = hd(free_vars J)
       val c = mk_pabs(args,J)
       val (l1,l2,l3,l4) = (entry_l,next_label(),next_label(),exit_l)
       val ifgoto = list_mk_comb(inst [alpha |-> !VarType] ifgoto_tm, [l1, c, l2, l3])
       val spec1 = gen_code (l2,M1,l4) (args,dest)
       val spec2 = gen_code (l3,M2,l4) (args,dest)

       val b1 = list_mk_comb(inst [alpha |-> !VarType] union_tm, [ifgoto, #body spec1])
       val b2 = list_mk_comb(inst [alpha |-> !VarType] union_tm, [b1, #body spec2])
       val s = list_mk_pair [l1, b2, l4]

       val exp = mk_cond (mk_comb(c,args), 
			  mk_comb(mk_pabs(args, #exp spec1), args), 
			  mk_comb(mk_pabs(args, #exp spec2), args))
       val value = mk_pair(exp, dest)
       val spec = list_mk_comb(inst [alpha |-> !VarType] reduce_tm, [s, value])

       val spec_lem =  prove (spec,   (* set_goal ([], spec) *)
			      MATCH_MP_TAC CONDITIONAL_RULE THEN
			      PBETA_TAC THEN
                              REWRITE_TAC [#thm spec1, #thm spec2]
			      )
       val spec_thm = PBETA_RULE spec_lem
       val exp' = mk_cond (J, #exp spec1, #exp spec2)

(*     val t = #1 (dest_pair (List.last (#2 (strip_comb (concl spec_lem1)))))
       val lem = ELIM_DEEP_LET_CONV t handle _ => REFL t
       val spec_thm = ONCE_REWRITE_RULE [lem] spec_lem1
*)
    in
       {entry = entry_l, exit = exit_l, body = b2, thm = spec_thm, exp = exp', dst = dest}
    end

and 

(* The composition is syntax directed.             *) 

mk_spec (entry_l,exit_l) (dest,src) args = 
    if is_atomic src orelse is_pair src then 
	mk_instr_spec (entry_l,exit_l) (dest,src)

    else if is_cond src then                 (*  t = if P then M else N *)
	mk_cond_spec (entry_l,exit_l) (dest,src) args

    else if is_comb src then
      let val (operator, operands) = strip_comb src
      in
        if basic.is_binop operator then (* Arith. and Logical Operations *)
           mk_instr_spec (entry_l,exit_l) (dest,src)
        else (* Application *)
	   raise Fail "unimplemented SAL code generation for function applications"
      end
    else
       raise Fail "unimplemented for this structure!"

and 

(*  Code generation (by producing specifications)       *)

gen_code (entry_l, t, exit_l) (input,output) =
   if is_atomic t orelse is_pair t then
       if t = output then    (* no copying is required *)
	    {entry = entry_l, exit = exit_l, body = inst [alpha |-> !VarType] nop, exp = t, dst = t,
	     thm = dummy_rule}
       else mk_instr_spec (entry_l,exit_l) (output, t)

   else if is_let t then                     (*  exp = LET (\v. N) M  *)
     let 
         val (v,M,N) = dest_plet t
         val new_l = next_label()
         val spec1 = mk_spec (entry_l,new_l) (v,M) input
         val spec2 = gen_code (new_l, N, exit_l) (#dst spec1, output)
         val spec3 = if #body spec2 = (inst [alpha |-> !VarType] nop) then 
	                 mk_spec (entry_l,exit_l) (v,M) input       (* make sure the exit label is correct *)
                     else mk_union_spec spec1 spec2
     in
         spec3
     end

   else
     {entry = entry_l, exit = exit_l, body = t, thm = mk_thm ([],``T``), exp = t, dst = t}
  ;

(* --------------------------------------------------------------------*)
(* Fromat SAL programs for printing.                                   *)
(* --------------------------------------------------------------------*)

val seperator = ref ("\n")   (* " \n " *)
val indent = "      "

fun format_label l = 
  "l" ^ (term_to_string (#2 (dest_comb l))) handle _ => term_to_string l

fun indent_label l = 
  let val label = format_label(l) 
  in case (size (label)) of
      2 => label ^ ":   " |
      3 => label ^ ":  "  |
      4 => label ^ ": "   |
      _ => label ^ ":"
  end

(* Turn a piece of SAL code into a string *) 

fun formatSAL code =
  if is_const code andalso #1 (dest_const code) = "NOP" then ""
  else if is_atomic code orelse is_pair code then term_to_string code
  else if is_comb code then
    let val (operator, xs) = strip_comb code
        val op_s = #1 (dest_const operator)
    in 
       if op_s = "UNION" then
         formatSAL (hd xs) ^ formatSAL (hd (tl xs))
       else if op_s = "ASG" then
         let val [entry_l, dest, src, exit_l] = xs
         in indent_label entry_l ^ term_to_string dest ^ " := " ^ term_to_string src ^ 
            "  (goto " ^ format_label exit_l ^ ")" ^ !seperator
         end
       else if op_s = "IFGOTO" then
         let val [entry_l, cond, true_l, false_l] = xs
         in indent_label entry_l ^ "ifgoto " ^ 
	     term_to_string (#2 (dest_pabs cond)) ^ " " ^ format_label true_l ^
	      " " ^ format_label false_l ^ !seperator
         end
       else if op_s = "GOTO" then
         let val [entry_l, exit_l] = xs
         in indent ^ "goto " ^ format_label exit_l ^ !seperator
         end
       else
         term_to_string code
     end
  else
    term_to_string code

(* --------------------------------------------------------------------*)
(* Pre-processing before code generation                               *)
(* --------------------------------------------------------------------*)

(* Find the output of an expression      *)

fun find_output t =
    if is_let t then
	let val (v,M,N) = dest_plet t
        in if is_atomic N orelse is_pair N then SOME N
           else find_output N
        end
    else if is_cond t then NONE
    else if is_pabs t then
        find_output (#2 (dest_pabs t))
    else NONE

(* Identify the argument, body and the output of a function *)

fun pre_process def = 
  let
    val (fname, fbody) = dest_eq (concl (SPEC_ALL def))
    val fname = if is_comb fname then #1 (dest_comb fname) else fname
    val (args,body) = dest_pabs fbody handle _ => (#2 (dest_comb fname), fbody)
    
    val (body, output) = 
      case find_output(body) of 
        SOME x => (body, x) |
        NONE => (mk_plet(args, body, args), args)
  in
    {body = body, input = args, output = output}
  end

(* --------------------------------------------------------------------*)
(* Certifing Code Generation                                           *)
(* --------------------------------------------------------------------*)

val printSAL = print o formatSAL;

fun certified_gen def =
  let
    val rs = pre_process def
    val (sane,var_type) = pre_check(#input rs, #body rs)
  in
    if sane then
      let val _ = (reset_label(); VarType := var_type)
	  val s = gen_code (next_label(), #body rs, next_label()) (#input rs, #output rs)
      in
	  {code = #body s, thm = #thm s}
      end
      handle _ =>  
       ( print("STOP: The source program (FIL) includes structures whose conversion hasn't been implemented!\n");
         {code = nop, thm = mk_thm ([], Term`T`)}
       )
    else 
      ( print("STOP: The source program (FIL) is invalid! (e.g. all variables are not of the same type)\n");
        {code = nop, thm = mk_thm ([], Term`T`)}
      )
  end

(* --------------------------------------------------------------------*)

end (* struct *)
