
(*
val _ = load "stringLib";
val _ = load "listTheory";
val _ = load "pairTheory";
val _ = load "arithmeticTheory";
*)
local
open bossLib;
open boolTheory;
open stringLib;
open Conv;
open Parse;
open listTheory;
open pairTheory;
open arithmeticTheory;
open STETheory;
open Lib;
open Drule;
in


val base_defn_list = [DefTraj_def, DefSeq_def, leq_def,
		      lub_def, Zero_def,
		      One_def, X_def, FST,
		      SND, Depth_def,
		      Nodes_def, APPEND, MAX_def,
		      MEM];

val CONV = SIMP_CONV arith_ss [DISJ_IMP_THM, FORALL_AND_THM,
			       UNWIND_FORALL_THM1];



fun STE_CONV_RULE theorem thm_list =

    let
	val TrajConv = computeLib.CBV_CONV (computeLib.new_compset thm_list)
	val NC = computeLib.CBV_CONV (reduceLib.num_compset())
	val BC = computeLib.CBV_CONV (computeLib.bool_compset())
    in
	CONV_RULE(EVERY_CONV [TrajConv, NC, TrajConv, BC]) theorem
    end;


(* Some user-interface functions *)
fun add_next start term =
    if start = 0 then term
    else
	let val newstart = start - 1
	in
	    add_next newstart (``NEXT ^term``)
	end;

fun add_next_upto_depth start depth term =
	if (start  = (depth-1)) then
	    add_next start term
	else
	    ``^(add_next start term) AND
	    ^(add_next_upto_depth (start+1) depth term)``;

fun TrajForm (guard:term, n:string, value:term, START, END) =
     let val node = stringLib.fromMLstring n
	 val atom =
	     ``((Is_1 ^node) WHEN (^value/\ ^guard))
	     AND
	     ((Is_0 ^node) WHEN ~(^value /\ ^guard))``;
     in
	 add_next_upto_depth START END atom
     end;

fun TF [x] = TrajForm x
| TF (x::xs) = ``^(TrajForm x) AND ^(TF xs)``;

fun extract_constr theorem = fst(boolSyntax.dest_imp(Thm.concl theorem));


(* STE Simulator over lattice models *)
(* verbose switches the print options *)
fun STE A C Y comp_list verbose =
if verbose then
let
val clock = start_time();
val thm_list = comp_list @ base_defn_list;
val _ = print ("\nSpecialising the STE Implementation definition...");
val iter0 = SPECL [A, C, Y] STE_Impl_def;
val _ = print ("done\n");
val _ = print ("Calculating the depth of the formula...");
val iter1 =  RIGHT_CONV_RULE(SIMP_CONV arith_ss [Depth_def, MAX_def]) iter0;
val _ = print ("done\n");
val _ = print("Rewriting for less than or equal...");
val iter2 = RIGHT_CONV_RULE(SIMP_CONV std_ss [LESS_OR_EQ]) iter1;
val _ = print("done\n");
val _ = print("Rewriting for less than...");
val iter3 = RIGHT_CONV_RULE(SIMP_CONV arith_ss [LESS_EQ]) iter2;
val _ = print("done\n");
val _ = print("Calculating the nodes in the antecedent and consequent...");
val iter4 = RIGHT_CONV_RULE(STRIP_QUANT_CONV(RAND_CONV(EVAL))) iter3;
val _ = print("done\n");
val _ = print ("Rewriting with DISJ_IMP_THM...");
val iter5a = RIGHT_CONV_RULE(SIMP_CONV std_ss [DISJ_IMP_THM]) iter4;
val _ = print("done\n");
val _ = print ("Rewriting with FORALL_AND_THM...");
val iter5b = RIGHT_CONV_RULE(SIMP_CONV std_ss [FORALL_AND_THM]) iter5a;
val _ = print("done\n");
val _ = print ("Rewriting with UNWINDFORALL_THM1...");
val iter5 = RIGHT_CONV_RULE(SIMP_CONV std_ss [UNWIND_FORALL_THM1]) iter5b;
val _ = print ("done\n");
val _ = print("Running STE...");
val iter6 = STE_CONV_RULE iter5 thm_list;
val iter7 = RIGHT_CONV_RULE(TOP_DEPTH_CONV(stringLib.string_EQ_CONV)
		THENC (TOP_DEPTH_CONV(COND_CONV))) iter6;
val _ = print("done\n");
val _ = print ("Canonicalising booleans...");
val iter8 = RIGHT_CONV_RULE(EVAL) iter7;
val _ = print ("done\n");
val _ = end_time clock
in
iter8
end
else
let
val clock = start_time();
val thm_list = comp_list @ base_defn_list;
val iter0 = SPECL [A, C, Y] STE_Impl_def;
val iter1 =  RIGHT_CONV_RULE(SIMP_CONV arith_ss [Depth_def, MAX_def]) iter0;
val iter2 = RIGHT_CONV_RULE(SIMP_CONV std_ss [LESS_OR_EQ]) iter1;
val iter3 = RIGHT_CONV_RULE(SIMP_CONV arith_ss [LESS_EQ]) iter2;
val iter4 = RIGHT_CONV_RULE(STRIP_QUANT_CONV(RAND_CONV(EVAL))) iter3;
val iter5a = RIGHT_CONV_RULE(SIMP_CONV std_ss [DISJ_IMP_THM]) iter4;
val iter5b = RIGHT_CONV_RULE(SIMP_CONV std_ss [FORALL_AND_THM]) iter5a;
val iter5 = RIGHT_CONV_RULE(SIMP_CONV std_ss [UNWIND_FORALL_THM1]) iter5b;
val iter6 = STE_CONV_RULE iter5 thm_list;
val iter7 = RIGHT_CONV_RULE(TOP_DEPTH_CONV(stringLib.string_EQ_CONV)
		THENC (TOP_DEPTH_CONV(COND_CONV))) iter6;
val iter8 = RIGHT_CONV_RULE(EVAL) iter7;
val _ = end_time clock
in
iter8
end;



(* From STE World to the Boolean World *)
fun STE_TO_BOOL A C Y Yb ok_thm monotonic_thm ste_impl_result =
    let val iter1 = SPECL [A, C, Y, Yb] BRIDGETHEOREM2;
	val iter2 = CONV_RULE(SIMP_CONV arith_ss [ok_thm]) iter1;
	val iter3 = CONV_RULE(SIMP_CONV arith_ss [monotonic_thm]) iter2;
	val iter4 =
	    CONV_RULE(SIMP_CONV bool_ss [DE_MORGAN_THM]) ste_impl_result;
    	val iter5 = CONV_RULE(SIMP_CONV std_ss [iter4]) iter3
in
    iter5
    end;

end;
