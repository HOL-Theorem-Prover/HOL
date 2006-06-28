 
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

fun mk_sat_var n = lookup_sat_num (n+1) (*+1 because minisat var numbers start at 0, HolSatLib at 1*)
fun get_var_num v = lookup_sat_var v - 1

fun isUsedRootClauseIdx cl ci = case Array.sub(cl,ci) of ROOT (RTHM _) => true | _ => false
fun isRootClauseThm th = HOLset.isEmpty(hypset th)

local 

val A = mk_var("A",bool)
val B = mk_var("B",bool)
val AND_INV_IMP2 = SPEC_ALL AND_INV_IMP
val cguid = ref 0

in 

fun dualise' th = 
    let val c = rand (land (concl th))
    in if is_disj c
       then let val (d0,d1) = dest_disj c
		val th1 = EQ_MP (INST [A|->d0,B|->d1] satTheory.OR_DUAL) th
		val th2 = if is_neg d0 then CONV_RULE (LAND_CONV NOT_NOT_CONV) th1 else th1
	    in dualise' (UNDISCH th2) end
       else UNDISCH (if is_neg c then CONV_RULE (LAND_CONV NOT_NOT_CONV) th else th)
    end

fun dualise t = 
    let val cn = ("D"^(int_to_string (!cguid)))
	val vl = all_vars t 
	val ty = list_mk_fun(List.map type_of vl,bool)
	val dc = mk_var(cn,ty)
	val dl = list_mk_comb(dc,vl)
	val cdef = SPEC_ALL (new_definition(cn^"def",mk_eq(dl,t)))
	val _ = (cguid:=(!cguid)+1)
	val th1 = UNDISCH (fst (EQ_IMP_RULE cdef)) 
	val th2 = MP (INST [A|->t] AND_INV_IMP2) th1
    in (dualise' th2,lhs(concl cdef),cdef) end
end

(* convert clause term to dualised thm form on first use *)
fun prepareRootClause cl (t,lns) ci = 
    let 
 	val (th,dl,cdef) = dualise t
 	val _ = update(cl,ci,ROOT (RTHM (th,lns,dl,cdef)))
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
fun getClause cl clr ci =
    let 
 	val res = case (if ci>=0 then sub(cl,ci) else sub(clr,~ci)) of 
		      ROOT (LL ll) => prepareRootClause cl ll ci
		    | ROOT (RTHM x) => (#1 x,#2 x)
		    | CHAIN _ => raise Domain
		    | LEARNT x => x
		    | BLANK => raise Domain
     in res end

(* ground resolve clauses c0 and c1 on v, where v is the only var that occurs with opposite signs in c0 and c1 *)
(* if n0 then v negated in c0 (but remember we are working with dualised clauses)*)
fun resolve v n0 rth0 rth1 = 
    let 
 	val th' = NOT_INTRO(if n0 then DISCH v rth0 else DISCH v rth1)
 	val th = PROVE_HYP th' (if n0 then rth1 else rth0)
     in th end


(* resolve c0 against c1 wrt v *)
fun resolveClause cl clr piv rci ((c0i,n0),(c1i,n1)) = 
    let  
         val ((rth0,lns0),(rth1,lns1)) = pair_map (getClause cl clr) (c0i,c1i)
	val v = mk_sat_var piv
 	val rth  = resolve v n0 rth0 rth1
	val lns0' = HOLset.delete(lns0,(n0,piv))
        val lns1' = HOLset.delete(lns1,(not n0,piv))
        val rlns = HOLset.union(lns0',lns1')
 	val _ = if rci>=0 
		then update(cl,  rci,LEARNT (rth,rlns)) 
		else update(clr,~rci,LEARNT (rth,rlns))
     in (rth,rlns) end

fun clause_size cl clr ci = HOLset.numItems(hypset(fst(getClause cl clr ci)))

val mxi =  (valOf Int.maxInt) 

fun clear_chain_arrays vcc clr = 
    (modify (K (RBM.mkDict Int.compare,0,NONE)) vcc; modify (K BLANK) clr)

fun update_vcc cl vcc clr pivs ci (isn,vi) = 
    if Intset.member(pivs,vi) (* is vi a pivot? *)
	then let val (cis,cs,_) = Array.sub(vcc,vi)
	     in Array.update(vcc,vi,(RBM.insert(cis,ci,isn),cs+(clause_size cl clr ci),NONE)) end
    else ()

fun update_chain_arrays cl vcc clr pivs ci = 
    let 
         val (cth,lns) = getClause cl clr ci
	val _ = HOLset.app (update_vcc cl vcc clr pivs ci) lns
     in () end

(* vil is list of var indices (pivots), cil is list of clause indices, in the chain*)
(* clear out vcc and then for each vil[i], vcc[i] is list of ci's in cil containing vil[i], and the sum of their sizes*)
(* the later is called the pivot rank (abbrev to pr): we always choose the lowest ranked pivot for each resolve*)
fun mkVarLists cl vcc clr vil cil  =  
    let 
 	val _ = clear_chain_arrays vcc clr 
 	val pivs = Intset.addList(Intset.empty, vil)
	val _ = List.app (fn ci => update_chain_arrays cl vcc clr pivs ci) cil  
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
fun res_update cl vcc clr rth rlns c0i c1i rci pivs piv (cis_vi,pr_vi) =     
    if Intset.numItems pivs = 0 then NONE
    else if Intset.numItems pivs = 1 then res_update_vcc_last vcc c0i c1i rci pivs
    else
    let  
 	val sz1 = clause_size cl clr c0i
	val sz2 = clause_size cl clr c1i 
	val rsz = clause_size cl clr rci 
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

fun resolveChain' cl vcc clr rci pivs piv = 
    let 
         val res = if isSome piv 
		  then let val piv = valOf piv
			   val pivs' = Intset.delete(pivs,piv)
 			   val (cis_vi,pr_vi,_) =  Array.sub(vcc,piv)
			   val ((c0i,n0),(c1i,n1)) = list2pair (RBM.listItems cis_vi)
			   val (rth,rlns) = resolveClause cl clr piv rci ((c0i,n0),(c1i,n1))
			   val piv' = res_update cl vcc clr rth rlns c0i c1i rci pivs' piv (cis_vi,pr_vi)
 		       in resolveChain' cl vcc clr (rci-1) pivs' piv' end
		  else Array.sub(clr,~(rci+1))

     in res end

fun resolveChain cl clr vcc rci = 
    let 
 	val (nl,lnl) = case sub(cl,rci) of CHAIN l => l | _ => failwith("resolveChain")
	val (vil,cil) = ListPair.unzip nl
 	val vil = tl vil (* first "var" is actually dummy value ~1 *) 
        val (piv,pivs)  = mkVarLists cl vcc clr vil cil (* build containment lists for each chain var and clause *)
	val res = resolveChain' cl vcc clr ~1 pivs piv
	val _ = update(cl,rci,res) 
      in ()  end

(*rth should be A |- F, where A contains all and only the root clauses used in the proof*)
fun unsatProveResolve (cl,sk,scl,lsr,cc) vc rcv = 
    let 
 	val vcc = Array.array(vc,(RBM.mkDict Int.compare,0,NONE))
	val clr = Array.array(vc,BLANK) (* reused by resolveChain: holds temp res clauses *)
	val _ = List.app (resolveChain cl clr vcc) (List.rev sk)
        val rth = case sub(cl,cc-1) of LEARNT th => fst th | _ => failwith("unsatProveTrace")
     in (scl,cl,rth) end



end
end

 
