 
structure minisatResolve = struct

local 

open Globals Parse HolKernel  
open Array boolSyntax boolTheory Drule Conv Rewrite
open satCommonTools dimacsTools satTheory

 
in

fun l2hh (h0::h1::t) = (h0,h1,t)
  | l2hh _ = raise Match

(*+1 because minisat var numbers start at 0,SatLib at 1*)
fun mk_sat_var lfn sva n = 
    let val rv = Array.sub(sva,n+1) 
	handle Subscript => failwith("mk_sat_var"^(int_to_string (n+1))^"\n")
    in rbapply lfn rv handle NotFound => rv end

local 

val A = mk_var("A",bool)
val B = mk_var("B",bool)
val AND_INV_IMP2 = SPEC_ALL AND_INV_IMP
fun INSTANTIATE_UNDERLYING lfn th =
    let val fvs = HOLset.listItems (hyp_frees th)
	val tms = map (fn v => tryrbapplyd lfn v v) fvs 
    in INST (map2 (fn t => fn fv => fv |-> t) tms fvs) th end
in 

(* let xi denote cnf definition variables such that pi is the rhs of the definition    *)
(* clauseth[i] gives i'th clause of CNF, as a pair (t,[tm] |- t')                      *)
(* where t = (x0 \/ ... \/ xn) and t' = (p0 \/ ... \/ pn), i.e. the "expanded" t       *)  
fun dualise lfn orc clauseth ci =
    let 
 	fun dualise' th = 
	    let val c = rand (land (concl th)) in 
		if is_disj c
		then 
		    let val (d0,d1) = dest_disj c 
			val th1 = 
			    if is_neg d0 
			    then EQ_MP (INST [A |-> dest_neg d0,B |-> d1] OR_DUAL3) th
			    else EQ_MP (INST [A|->d0,B |-> d1] OR_DUAL2) th 
		    in dualise' (UNDISCH th1) end
		else 
		    UNDISCH 
			(if is_neg c 
			 then CONV_RULE (LAND_CONV NOT_NOT_CONV) th 
			 else MP (INST [A |-> c] AND_INV2) th) 
	    end
	val (t1,th1) = Array.sub(clauseth,orc) (* t, [tm] |- t') *)
	    handle Subscript => failwith("dualise"^(int_to_string (ci))^"\n")
	val res = 
	    if RBM.numItems lfn = 0 (* original problem in CNF, so th1 is [tm] |- t *)
	    then let val  th2 = MP (INST [A|->t1] AND_INV_IMP2) th1 (*[tm] |- ~t ==> F*)
		 in dualise' th2 end else (* [~p0,...,~pn,tm] |- F *)
	    let val th2 = MP (INST [A|->t1] AND_INV_IMP2) (ASSUME t1) (*[tm,t] |- ~t ==> F *)
		val dth =  dualise' th2 (* [~x0,...,~xn,tm,t] |- F *)
		in PROVE_HYP th1 (INSTANTIATE_UNDERLYING lfn dth) end (* [~p0,...,~pn,tm] |- F *)
     in res end
end

(* convert clause term to dualised thm form on first use *)
fun prepareRootClause lfn orc clauseth cl ci = 
    let 
 	val th = dualise lfn orc clauseth ci
 	val _ = Dynarray.update(cl,ci,th)
     in th end

(* will return clause thm at index ci *)
fun getClause cl ci = Dynarray.sub(cl,ci)
    handle Subscript => failwith("getClause"^(int_to_string (ci))^"\n")

(* ground resolve clauses c0 and c1 on v, 
   where v is the only var that occurs with opposite signs in c0 and c1 *)
(* if n0 then v negated in c0 (but remember we are working with dualised clauses)*)
fun resolve v n0 rth0 rth1 = 
    let 
 	val th' = if n0 then DISCH v rth0 else DISCH v rth1
 	val th = PROVE_HYP th' (if n0 then rth1 else rth0)
     in th end

val counter = ref 0

(* resolve c0 against c1 wrt v *)
fun resolveClause lfn sva cl piv rth0 c1i = 
    let  
         val rth1 = getClause cl c1i
	(* piv is the pivot lit in c1i. if piv mode 2 = 0, then must be negated in c0i *)
	val n0 = (piv mod 2 = 0)
	val v = mk_sat_var lfn sva (piv div 2)
 	val rth  = resolve v n0 rth0 rth1
	val _ = (counter:=(!counter)+1)
     in rth end

fun resolveChain lfn sva cl (nl,lnl) rci =
    let val ((_,c0i),(vi,c1i),nlt) = l2hh nl
	val r0 = getClause cl c0i
	val r1 = resolveClause lfn sva cl vi r0 c1i
	val res = List.foldl (fn ((vi,ci),th) => 
				 resolveClause lfn sva cl vi th ci) r1 nlt 
	val _ = Dynarray.update(cl,rci,res)
    in () end

end
end

 
