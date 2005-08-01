
(********************************************************************************************************)
(* Function makeALU generates HOL term for transition system and init states of sync. pipelined ALU     *)
(* where the number of registers and datapath width can be varied. Used for testing RuleCheck.          *)
(* The ALU is taken from [1] Clarke et al: Model Checking, 1999 (MIT Press).                            *)
(*                                                                                                      *)
(* state vars are:                                                                                      *)
(*     res = alu op result register                                                                     *)
(*     op0 = alu operand reg                                                                            *)
(*     op1 = alu operand reg                                                                            *)
(*     reg0 = gp reg                                                                                    *)
(*     reg 1 = gp reg                                                                                   *)
(*    state vars that are inputs to the system:                                                         *)
(*     stall = whether stalling or not                                                                  *)
(*     dest = dest address of res                                                                       *)
(*     src0 = src add for op0                                                                           *)
(*     src1 = src add for op1                                                                           *)
(*     ctrl = op selection                                                                              *)
(********************************************************************************************************)

(* Usage example (start hol including the HolCheck/examples directory, using the -I command line option)
   Warning: this gives huge unreadable properties for aw>2 and d>4 or so

app load ["holCheckLib","alu"];
val aw = 1; (* address space width in bits *)
val d = 1; (* datapath width in bits *)
val alu1 = alu.makeALU d aw;
val alu2 = holCheckLib.holCheck alu1 handle ex => Raise ex;
val alu3 = holCheckLib.prove_model alu2;
val res = holCheckLib.get_results alu3;

*)

structure alu = 

struct

local 

open Globals HolKernel Parse
open boolSyntax bossLib pairSyntax 
open commonTools ctlSyntax holCheckLib

in


(********************************************************************************************************)
(* generates expression for retrieving bit b of register pointed to by the register called addreg,      *)
(* where the address space is wsize bits wide                                                           *)
(********************************************************************************************************)

fun getreg addreg wsize bit =
        let fun getreg_aux l n b = if (l=[]) then `` ^(mk_bool_var ("reg"^(int_to_string n)^"_"^b))``
                             else ``if ^(hd l) then ^(getreg_aux (tl l) (2*n+1) b) else ^(getreg_aux (tl l) (2*n) b)``;
        in getreg_aux (List.rev(map (fn v => mk_bool_var (addreg^"_"^v)) (List.tabulate(wsize,(fn n => (int_to_string n)))))) 0 bit end;

(********************************************************************************************************)
(* generates bitwise conjunction of equality tests for registers r1 and r2, each w bits wide            *)
(********************************************************************************************************)

fun regeq r1 r2 w =
  let val regsz = List.tabulate (w, (fn n => (int_to_string n)));
  in boolSyntax.list_mk_conj (map (fn a => mk_eq(mk_bool_var (r1^"_"^a),mk_bool_var (r2^"_"^a))) regsz) end;

(********************************************************************************************************)
(* return HOL/CTL truth value corresponding to bit bb of the integer rr.                                *)
(* useful in generating the addresses of data registers                                                 *)
(********************************************************************************************************)

(* return binary rep. of integer r1, as a list of 0's and 1's *)
fun i2b r1 = if (Int.div(r1,2)=0) then [Int.mod(r1,2)] else (Int.mod(r1,2))::(i2b(Int.div(r1,2)));

fun getbit rr bb l =
  let val r = Option.valOf(Int.fromString rr);
      val b = Option.valOf(Int.fromString bb);
      val ll = (i2b r);
      val ll = ll@List.tabulate(l - (List.length ll),(fn x => 0));
  in if (List.nth(ll,b)=0) then F else T handle Subscript => F end;

fun getctlbit ap_ty rr bb l =
  let val r = Option.valOf(Int.fromString rr);
      val b = Option.valOf(Int.fromString bb);
      val ll = (i2b r);
      val ll = ll@List.tabulate(l - (List.length ll),(fn x => 0));
  in if (List.nth(ll,b)=0) then inst [alpha|->ap_ty] C_F else inst [alpha|->ap_ty] C_T 
      handle Subscript => inst [alpha|->ap_ty] C_F end;

(********************************************************************************************************)
(* Returns (thm*thm)*(ctl_wff*ctl_wff)*(string list)                                                    *)
(*   where the thms are HOL defns for the transition system and initial states of the ALU with datapath *)
(*   width d, and with an address space of aw bits. The ctl_wff's are CTL formulae expressing the       *)
(*   properties that the correct destination register is updated properly (see [1] for details). The    *)
(*   string list is the variable ordering with which to initialise BuDDy                                *)
(********************************************************************************************************)

fun makeALU d aw =
  let
    val datapath = List.tabulate (d, (fn n => (int_to_string n)));
    val addpath = List.tabulate (aw, (fn n => (int_to_string n)));
    val regnums = List.tabulate ((round(Math.pow(2.0,(Real.fromInt(aw))))), (fn n => (int_to_string n)));
    val regfile = map (fn n => "reg"^n) regnums;
    val dataregs = ["op0","op1","res"]@regfile;
    val addregs = ["dest","dest_ex","dest_wb","src0","src1"];
    val ctrlvars = ["stall","stall_ex","stall_wb","ctrl","ctrl_ex"];
    val dataregvars = map mk_bool_var (List.concat (List.map (fn x => (List.map (fn y => x^"_"^y) datapath)) dataregs));
    val addregvars = map mk_bool_var (List.concat (List.map (fn x => (List.map (fn y => x^"_"^y) addpath)) addregs));
    val allvars = (dataregvars @ addregvars @ (map mk_bool_var ctrlvars));
    (*val state = pairSyntax.list_mk_pair allvars;*)
    val I1 = T;
    val bw_alu_op = map (fn n => 
			 mk_disj((mk_conj(``ctrl_ex:bool``,(mk_disj((mk_bool_var ("op0_"^n)),(mk_bool_var ("op1_"^n)))))),
				 (mk_conj(``~(ctrl_ex:bool)``,(mk_neg(mk_disj((mk_bool_var ("op0_"^n)),(mk_bool_var ("op1_"^n)))))))))
                         datapath;
    val bw_res_trans = map (fn a => mk_eq((mk_bool_var ("res_"^a^"'")),mk_cond(``~stall_ex:bool``,
                                                                   (List.nth(bw_alu_op, (string_to_int a))),
                                                                    (mk_bool_var ("res_"^a))))) datapath;
    val bw_op0_trans = map (fn a => ``^(mk_bool_var ("op0_"^a^"'")) = if (~stall_ex /\ (^(regeq "dest_ex" "src0" aw)))
                                          then ^(List.nth(bw_alu_op, (string_to_int a)))
							else (if stall_wb
                                                      then (^(getreg "src0" aw a))
						                  else (if (^(regeq "dest_wb" "src0" aw))
                                                            then (^(mk_bool_var ("res_"^a)))
                                                            else (^(getreg "src0" aw a))))``) datapath;
    val bw_op1_trans = map (fn a => ``^(mk_bool_var ("op1_"^a^"'")) = if (~stall_ex /\ (^(regeq "dest_ex" "src1" aw)))
                                          then ^(List.nth(bw_alu_op, (string_to_int a)))
							else (if stall_wb
                                                      then (^(getreg "src1" aw a))
						                  else (if (^(regeq "dest_wb" "src1" aw))
                                                            then (^(mk_bool_var ("res_"^a)))
                                                            else (^(getreg "src1" aw a))))``) datapath;
   val bw_reg_trans = map (fn n => 
			   (map (fn a => mk_eq(mk_bool_var ("reg"^n^"_"^a^"'"),
					       mk_cond(``stall_wb:bool``,mk_bool_var ("reg"^n^"_"^a),
					       mk_cond((boolSyntax.list_mk_conj(List.map 
										(fn b => mk_eq(mk_bool_var("dest_wb_"^b),
											       (getbit n b aw))) addpath)),
						       mk_bool_var("res_"^a),
						       mk_bool_var("reg"^n^"_"^a) )))) datapath)) regnums;
   val bw_reg_trans = map list_mk_conj bw_reg_trans;
   val bw_dest_trans = map (fn n => list_mk_conj(map (fn (x,y) => mk_eq(mk_bool_var(x^"_"^n^"'"),
									mk_bool_var(y^"_"^n))) [("dest_wb","dest_ex"),
												("dest_ex","dest")])) addpath;
    val R1 = list_mk_conj (bw_res_trans @ bw_op0_trans @ bw_op1_trans @ bw_reg_trans @  bw_dest_trans
			 @ [(``stall_ex':bool = stall:bool``),(``stall_wb':bool=stall_ex:bool``), (``ctrl_ex':bool=ctrl:bool``)])
    val T1 = [(".",R1)];

   (* define properties *)
   infixr 5 C_AND infixr 5 C_OR infixr 2 C_IMP infix C_IFF;
   val state = ksTools.mk_state I1 T1

   fun alu_AP s = C_AP state (mk_bool_var s) 
   val ap_ty = (type_of state) --> bool
   val bw_op0_defs = List.map  (fn b => list_C_OR
	(List.map (fn x =>  (C_AX(C_AX(alu_AP ("reg"^x^"_"^b)))) C_AND
		   (list_C_AND (List.map (fn y => (alu_AP ("src0"^"_"^y)) C_IFF  (getctlbit ap_ty x y aw))
				addpath))) regnums)) datapath;
   val bw_op1_defs = List.map (fn b => list_C_OR
	(List.map (fn x => (C_AX(C_AX(alu_AP ("reg"^x^"_"^b)))) C_AND
		   (list_C_AND (List.map (fn y=>((alu_AP ("src1"^"_"^y)) C_IFF (getctlbit ap_ty x y aw)))
				addpath))) regnums)) datapath;
   val bw_res_defs = List.map (fn b => list_C_OR(map (fn x => (C_AX(C_AX(C_AX(alu_AP ("reg"^x^"_"^b))))) C_AND
						 (list_C_AND(List.map (fn y => ((alu_AP ("dest"^"_"^y)) C_IFF (getctlbit ap_ty x y aw)))
							     addpath))) regnums)) datapath;
   val bw_ctl_alu_op_defs = map (fn (x,y) => ((alu_AP ("ctrl")) C_AND (x C_OR y)) C_OR ((C_NOT(alu_AP ("ctrl"))) C_AND 
											(C_NOT( x C_OR y))))
						(ListPair.zip(bw_op0_defs,bw_op1_defs));

   val bw_prop1 = map (fn (x,y) => (C_AG((C_NOT(alu_AP ("stall"))) C_IMP (((x C_IFF y)))))) 
		      (ListPair.zip(bw_ctl_alu_op_defs,bw_res_defs))
   val bw_prop1 = List.map (fn (p,n) => ("p1_"^(int_to_string n),p)) (ListPair.zip(bw_prop1,List.tabulate(List.length bw_prop1,I)))

   val bw_prop2 = map (fn b => list_C_AND(map 
					  (fn rg => 
					   (C_AG( (alu_AP ("stall")) C_IMP
						 (list_C_AND(map 
								(fn a =>C_NOT((alu_AP ("dest"^"_"^a)) C_IFF (getctlbit ap_ty rg a aw)))
								addpath)) C_OR
						 (((C_AX(C_AX(alu_AP ("reg"^rg^"_"^b)))) C_IFF 
						   (C_AX(C_AX(C_AX(alu_AP ("reg"^rg^"_"^b))))))))))
					  regnums)) datapath;
   val bw_prop2 = List.map (fn (p,n) => ("p2_"^(int_to_string n),p)) (ListPair.zip(bw_prop2,List.tabulate(List.length bw_prop2,I)))

   fun makeBddMap d aw =
    let
     val resv = map (fn v => ("res_"^v,"res_"^v^"'")) datapath;
     val op0v = map (fn v => ("op0_"^v,"op0_"^v^"'")) datapath;
     val op1v = map (fn v => ("op1_"^v,"op1_"^v^"'")) datapath;
     val destv =List.concat(List.concat (map (fn v => map (fn a => [v^a,v^a^"'"]) addpath) ["dest_","dest_ex_","dest_wb_"]));
     val src0v = map (fn v => ("src0_"^v,"src0_"^v^"'")) addpath;
     val src1v = map (fn v => ("src1_"^v,"src1_"^v^"'")) addpath;
     val stallv = ["stall","stall'","stall_ex","stall_ex'","stall_wb","stall_wb'"];
     val ctrlv = ["ctrl","ctrl'","ctrl_ex","ctrl_ex'"];
     val regv = (map (fn rg => rev(map (fn d => ("reg"^rg^"_"^d,"reg"^rg^"_"^d^"'")) datapath)) regnums);
     fun interleave l1 l2 = List.concat(map (fn ((x,x'),(y,y')) => [x,x',y,y']) (ListPair.zip(l1,l2)));
     fun stdest l1 l2 = if (l1=[]) then [] else List.take(l1,2)@List.take(l2,aw*2)@(stdest (List.drop(l1,2)) (List.drop(l2,aw*2)))  ;
     fun geninter L = (if (hd(L)=[]) then [] 
		       else (List.concat(map (fn l => [fst(hd(l)),snd(hd(l))] ) L))::(geninter(map (fn l => tl(l)) L)));
     in (interleave src0v src1v) @ (stdest stallv  destv) @ ctrlv @
        (List.concat(geninter ([(rev op0v)]@[(rev op1v)]@(regv)@[(rev resv)]))) end
    val bvm = makeBddMap d aw;
  in ((set_init I1) o (set_trans T1) o (set_flag_ric true) o (set_name "alu") o (set_vord bvm)o (set_state state) o 
    (set_props(bw_prop1@bw_prop2))) empty_model end;




end
end

