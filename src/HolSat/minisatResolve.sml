 
structure minisatResolve = struct

local 

open Globals Parse HolKernel  
open Array boolSyntax boolTheory Drule Conv Rewrite
open satCommonTools dimacsTools minisatParse satTheory

structure RBM = Redblackmap;

 
in

 (* p is a literal *)
fun toVar p = if is_neg p then rand p else p

fun kill_neg t = if is_neg t then rand t else t

local 
val A = mk_var("A",bool)
val t = mk_var("t",bool)
val AND_INV2 = SPEC_ALL AND_INV
val NOT_NOT2 = SPEC_ALL NOT_NOT
in
fun NOT_NOT_ELIM th = EQ_MP (INST [t|->rand(rand(concl th))] NOT_NOT2) th
fun NOT_NOT_CONV tm = INST [t|->rand(rand tm)] NOT_NOT2
end

fun l2hh (h0::h1::t) = (h0,h1,t)
  | l2hh _ = raise Match

fun mk_sat_var n = lookup_sat_num (n+1) (*+1 because minisat var numbers start at 0, 
					 HolSatLib at 1*)
fun get_var_num v = lookup_sat_var v - 1

fun isUsedRootClauseIdx cl ci = case Array.sub(cl,ci) of ROOT (RTHM _) => true | _ => false
fun isRootClauseThm th = HOLset.isEmpty(hypset th)

local 

val A = mk_var("A",bool)
val B = mk_var("B",bool)
val AND_INV_IMP2 = SPEC_ALL AND_INV_IMP

in 

(* mcth maps clause term t to thm of the form cnf |- t, *)
(*  where t is a clause of the cnf term                 *)    
fun dualise mcth t =
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
	val th1 = Redblackmap.find(mcth,t) 
	val th2 = MP (INST [A |-> t] AND_INV_IMP2) th1 
	val res =  dualise' th2  
     in res end

end

(* convert clause term to dualised thm form on first use *)
fun prepareRootClause mcth cl (t,lns) ci = 
    let 
 	val th = dualise mcth t
 	val _ = update(cl,ci,ROOT (RTHM (th,lns,T,TRUTH)))
     in (th,lns) end

(* will return clause info at index ci *)
fun getRootClause cl ci =
    let 
 	val res = case sub(cl,ci) of 
		      ROOT (LL ll) => raise Domain
		    | ROOT (RTHM x) => x
		    | CHAIN _ => raise Domain
		    | LEARNT x => raise Domain
		    | BLANK => raise Domain
     in res end

(* will return clause thm at index ci *)
fun getClause mcth cl clr ci =
    let 
 	val res = case (if ci>=0 then sub(cl,ci) else sub(clr,~ci)) of 
		      ROOT (LL ll) => prepareRootClause mcth cl ll ci
		    | ROOT (RTHM x) => (#1 x,#2 x)
		    | CHAIN _ => raise Domain
		    | LEARNT x => x
		    | BLANK => raise Domain
     in res end

(* ground resolve clauses c0 and c1 on v, 
   where v is the only var that occurs with opposite signs in c0 and c1 *)
(* if n0 then v negated in c0 (but remember we are working with dualised clauses)*)
fun resolve v n0 rth0 rth1 = 
    let 
 	val th' = if n0 then DISCH v rth0 else DISCH v rth1
 	val th = PROVE_HYP th' (if n0 then rth1 else rth0)
     in th end


(* resolve c0 against c1 wrt v *)
fun resolveClause mcth cl clr piv rci (c0i,c1i) = 
    let  
         val ((rth0,lns0),(rth1,lns1)) = pair_map (getClause mcth cl clr) (c0i,c1i)
	val n0 = HOLset.member(lns0,(true,piv))
	val v = mk_sat_var piv
 	val rth  = resolve v n0 rth0 rth1
	val lns0' = HOLset.delete(lns0,(n0,piv))
        val lns1' = HOLset.delete(lns1,(not n0,piv))
        val rlns = HOLset.union(lns0',lns1')
 	val _ = if rci>=0 
		then update(cl,  rci,LEARNT (rth,rlns)) 
		else update(clr,~rci,LEARNT (rth,rlns))
     in (rth,rlns) end

fun clause_size mcth cl clr ci = HOLset.numItems(hypset(fst(getClause mcth cl clr ci)))

val mxi =  (valOf Int.maxInt) 

fun clear_chain_arrays vcc clr = 
    (modify (K (RBM.mkDict Int.compare,0,NONE)) vcc; modify (K BLANK) clr)

fun update_vcc mcth cl vcc clr pivs ci (isn,vi) = 
    if Intset.member(pivs,vi) (* is vi a pivot? *)
	then let val (cis,cs,_) = Array.sub(vcc,vi)
	     in Array.update(vcc,vi,(RBM.insert(cis,ci,isn),
				     cs+(clause_size mcth cl clr ci),NONE)) 
	     end
    else ()

fun update_chain_arrays mcth cl vcc clr pivs ci = 
    let 
         val (_,lns) = getClause mcth cl clr ci
	val _ = HOLset.app (update_vcc mcth cl vcc clr pivs ci) lns
     in () end

(* vil is list of var indices (pivots), cil is list of clause indices, in the chain*)
(* clear out vcc and then for each vil[i], vcc[i] is list of ci's in cil containing vil[i], 
   and the sum of their sizes*)
(* the latter is called the pivot rank (abbrev to pr): 
 we always choose the lowest ranked pivot for each resolve*)
fun mkVarLists mcth cl vcc clr vil cil  =  
    let 
 	val _ = clear_chain_arrays vcc clr 
 	val pivs = Intset.addList(Intset.empty, vil)
	val _ = List.app (fn ci => update_chain_arrays mcth cl vcc clr pivs ci) cil  
	val (piv,_) = List.foldl 
	    (fn (vi,(piv,pr)) => let val (cis,pr',_) = Array.sub(vcc,vi)
				 in if pr'<pr andalso RBM.numItems cis = 2
				     then (SOME vi,pr') else (piv,pr) end)
	    (NONE,mxi) vil
     in (piv,pivs) end

(* in the SOME case, the vi is a remaining pivot and occured in resolvent, hence needs updating *)
fun res_update_vcc vcc rci c0i c1i sz1 sz2 rsz vi (cis,pr,SOME isn') = 
    let 
 	val (cis1,is1) = (fst(RBM.remove(cis,c0i)),true) handle NotFound => (cis,false)
	val (cis2,is2) = (fst(RBM.remove(cis1,c1i)),true) handle NotFound => (cis1,false)
	val cis3 = if is1 orelse is2 then RBM.insert(cis2,rci,isn') else cis2 
 	val pr' = pr + rsz 
	    - (if is1 then sz1 else 0) - (if is2 then sz2 else 0)
	val _ = Array.update(vcc,vi,(cis3,pr',NONE))
     in (cis3,pr') end
| res_update_vcc vcc rci c0i c1i sz1 sz2 rsz vi (cis,pr,NONE) = (cis,pr) 

fun res_update_vcc_last vcc c0i c1i rci pivs = 
    let val vi = Intset.find (K true) pivs
	val vvi = valOf vi
	val (cis,_,_) = (Array.sub(vcc,vvi))
	val ((cis1,isn1),is1) = (RBM.remove(cis,c0i),true) handle NotFound => ((cis,false),false)
	val ((cis2,isn2),is2) = (RBM.remove(cis1,c1i),true) handle NotFound => ((cis1,false),false)
	val isn = if is1 then isn1 else isn2
	val cis3 = RBM.insert(cis2,rci,isn) 
	val _ = Array.update(vcc,vvi,(cis3,0,NONE))
    in vi end

(* vi is res var, ~rci is idx of res clause in clr, and rsv is it's shadow vec *)
(* this updates vcc i.e if vi' occured in the antecedent clauses of the current resolvent then 
   vi' now occurs in the resolvent as far as this chain is concerned, so update vcc[vi'] *)
fun res_update mcth cl vcc clr rth rlns c0i c1i rci pivs piv (cis_vi,pr_vi) =     
    if Intset.numItems pivs = 0 then NONE
    else if Intset.numItems pivs = 1 then res_update_vcc_last vcc c0i c1i rci pivs
    else
    let  
 	val sz1 = clause_size mcth cl clr c0i
	val sz2 = clause_size mcth cl clr c1i 
	val rsz = clause_size mcth cl clr rci 
 	val _ = HOLset.app 
		    (fn (isn,vi) => 
			if Intset.member(pivs,vi) 
			then let val (cis_vi,pr,_) = Array.sub(vcc,vi)
			     in Array.update(vcc,vi,(cis_vi,pr,SOME isn)) end
			else ())
		    rlns
 	val (piv',_) = Intset.foldl 
			   (fn (vi',(piv',minpr)) =>  
			       let  
 	                           val (cis',pr') = res_update_vcc vcc rci c0i c1i sz1 sz2 
								   rsz vi' (Array.sub(vcc,vi'))
			       in if pr'<minpr andalso RBM.numItems cis' = 2 
				  then (SOME vi',pr') 
				  else (piv',minpr) end) (NONE,mxi) pivs
     in piv' end

fun list2pair [f,s] = (f,s)
  | list2pair _ = raise Match

fun resolveChain' mcth cl vcc clr rci pivs piv = 
    let 
         val res = if isSome piv 
		  then let val piv = valOf piv
			   val pivs' = Intset.delete(pivs,piv)
 			   val (cis_vi,pr_vi,_) =  Array.sub(vcc,piv)
			   val ((c0i,n0),(c1i,n1)) = list2pair (RBM.listItems cis_vi)
			   val (rth,rlns) = resolveClause mcth cl clr piv rci (c0i,c1i)
			   val piv' = res_update mcth cl vcc clr rth rlns c0i c1i rci pivs' piv (cis_vi,pr_vi)
 		       in resolveChain' mcth cl vcc clr (rci-1) pivs' piv' end
		  else Array.sub(clr,~(rci+1))

     in res end

fun resolveChain mcth cl clr vcc rci = 
    let 
 	val (nl,lnl) = case sub(cl,rci) of CHAIN l => l | _ => failwith("resolveChain")
	val (vil,cil) = ListPair.unzip nl
 	val vil = tl vil (* first "var" is actually dummy value ~1 *) 
	(* build containment lists for each chain var and clause *)
        val (piv,pivs)  = mkVarLists mcth cl vcc clr vil cil 
	val res = resolveChain' mcth cl vcc clr ~1 pivs piv
	val _ = update(cl,rci,res) 
     in ()  end

fun resolveChain0 mcth cl clr vcc rci =
    let val (nl,lnl) = case sub(cl,rci) of CHAIN l => l | _ => failwith("resolveChain")
	val (vil,cil) = ListPair.unzip nl
	val vil = tl vil 
	val (c0i,c1i,cilt) = l2hh cil
	val r1 = resolveClause mcth cl clr (hd vil) rci (c0i,c1i)
	val res = List.foldl (fn ((vi,ci),th) => 
				 resolveClause mcth cl clr vi rci (ci,rci)) 
			     r1 (ListPair.zip(tl vil,cilt))
	val _ = update(cl,rci,LEARNT res)
    in () end

(*rth should be A |- F, where A contains all and only the root clauses used in the proof*)
fun unsatProveResolve mcth (cl,sk,scl,lsr,cc) vc rcv reord = 
    let 
 	val vcc = Array.array(vc,(RBM.mkDict Int.compare,0,NONE))
	val clr = Array.array(vc,BLANK) (* reused by resolveChain: holds temp res clauses *)
	val doChain = if reord then resolveChain else resolveChain0 
	val _ = List.app (doChain mcth cl clr vcc) (List.rev sk)
        val rth = case sub(cl,cc-1) of LEARNT th => fst th | _ => failwith("unsatProveTrace")
     in rth end



end
end

 
