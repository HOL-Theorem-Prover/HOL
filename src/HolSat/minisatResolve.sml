 
structure minisatResolve = struct

local 

open Globals Parse HolKernel  
open Array boolSyntax boolTheory Drule Conv Rewrite
open satCommonTools dimacsTools satTheory

 
in

local 
    val t = mk_var("t",bool)
    val NOT_NOT2 = SPEC_ALL NOT_NOT
in
fun NOT_NOT_CONV tm = INST [t|->rand(rand tm)] NOT_NOT2
end

fun l2hh (h0::h1::t) = (h0,h1,t)
  | l2hh _ = raise Match

fun mk_sat_var sva n = Array.sub(sva,n+1) (*+1 because minisat var numbers start at 0,SatLib at 1*)
    handle Subscript => failwith("mk_sat_var"^(int_to_string (n+1))^"\n")

local 

val A = mk_var("A",bool)
val B = mk_var("B",bool)
val AND_INV_IMP2 = SPEC_ALL AND_INV_IMP

in 

(* mcth maps clause term t to thm of the form 'cnf |- t', *)
(*  where t is a clause of the cnf term                 *)    
fun dualise rt2o mcth ci =
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
	val th1 = Array.sub(mcth,Dynarray.sub(rt2o,ci))
		  handle Subscript => failwith("dualise"^(int_to_string (ci))^"\n")
	val th2 = MP (INST [A |-> (concl th1)] AND_INV_IMP2) th1 
	val res =  dualise' th2  
     in res end

end

(* convert clause term to dualised thm form on first use *)
fun prepareRootClause rt2o mcth cl ci = 
    let 
 	val th = dualise rt2o mcth ci
 	val _ = Dynarray.update(cl,ci,th)
     in th end

(* will return clause thm at index ci *)
fun getClause rt2o mcth cl ci = Dynarray.sub(cl,ci)
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
fun resolveClause sva rt2o mcth cl piv rth0 c1i = 
    let  
         val rth1 = getClause rt2o mcth cl c1i
	(* piv is the pivot lit in c1i. if piv mode 2 = 0, then must be negated in c0i *)
	val n0 = (piv mod 2 = 0)
	val v = mk_sat_var sva (piv div 2)
 	val rth  = resolve v n0 rth0 rth1
	val _ = (counter:=(!counter)+1)
     in rth end

fun resolveChain sva rt2o mcth cl (nl,lnl) rci =
    let val ((_,c0i),(vi,c1i),nlt) = l2hh nl
	val r0 = getClause rt2o mcth cl c0i
	val r1 = resolveClause sva rt2o mcth cl vi r0 c1i
	val res = List.foldl (fn ((vi,ci),th) => resolveClause sva rt2o mcth cl vi th ci) r1 nlt 
	val _ = Dynarray.update(cl,rci,res)
    in () end

end
end

 
