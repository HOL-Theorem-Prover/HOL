 
(* Non-logical definitional CNF, due to John Harrison.            *)
(* Ported from HOL Light by Hasan Amjad, with HOL4 specific mods. *)

structure def_cnf = 
struct 

local

open Lib boolLib Globals Parse Term Type Thm Drule Psyntax Conv Feedback boolSyntax

open satCommonTools satTheory

val dpfx = "dcnf_"

in 

val presimp_conv = QCONV (GEN_REWRITE_CONV REDEPTH_CONV empty_rewrites
		[NOT_CLAUSES, AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES, COND_EXPAND,
		 COND_CLAUSES])

(* ------------------------------------------------------------------------- *)
(* Split up a theorem according to conjuncts, in a general sense.            *)
(* ------------------------------------------------------------------------- *)
local
val p_tm = mk_var("p",bool) 
val q_tm = mk_var("q",bool)
fun is_literal tm = is_var tm orelse (is_neg tm andalso is_var(rand tm))
val spine_disj = HolKernel.spine_binop (total dest_disj) (*FIXME: fold is_lit check into this *)
fun is_clausal tm =
  let val djs = spine_disj tm 
  in all is_literal djs end
in
val GCONJUNCTS  = 
    let fun GCONJUNCTS' th acc =
	    let val (opr,args) = strip_comb (concl th)
	    in if not (is_const opr) then th::acc else 
	       case fst (dest_const opr) of
		   "~" => 
		   let val  (opr,args) = strip_comb (hd args)
		   in if not (is_const opr) then th::acc else 
		      (case fst (dest_const opr) of
			  "==>" =>
			  let val (p,q) = (hd args,last args)
			  in GCONJUNCTS' (MP (INST [p_tm|->p,q_tm|->q] pth_ni1) th)
				(GCONJUNCTS' (MP (INST [p_tm|->p,q_tm|->q] pth_ni2) th) acc) end
			| "\\/" => 
			  let val (p,q) = (hd args,last args)
			  in GCONJUNCTS' (MP (INST [p_tm|->p,q_tm|->q] pth_no1) th)
				(GCONJUNCTS' (MP (INST [p_tm|->p,q_tm|->q] pth_no2) th) acc) end
			| "~" => 
			  GCONJUNCTS' (MP (INST [p_tm|->hd args] pth_nn) th) acc
			| _ => th::acc)
		   end
		 | "/\\" => 
		   let val (p,q) = (hd args,last args)
		   in GCONJUNCTS' (CONJUNCT1 th) (GCONJUNCTS' (CONJUNCT2 th) acc) end
		 | _ => th::acc 
	    end
	fun findTF tm = total (HolKernel.find_term (fn t => is_T t orelse is_F t)) tm
	fun GCONJUNCTS'' th = GCONJUNCTS' th []
    in fn tm => fn th => 
	  let val ths0 = if is_neg tm andalso is_neg (rand tm) 
			 then CONJUNCTSR (CONV_RULE NOT_NOT_CONV th) else [th]
	      val ths1 = List.map GCONJUNCTS'' ths0
	      val is_cnf = ref true
	      val ths2 =  List.map (fn th => 
				       if is_clausal (concl th) then (true,th)
				       else (is_cnf:=false;(false,th))) (List.concat ths1)
	      val ths3 = if !is_cnf then ths2 else 
			 List.map (fn (is_c,th) => 
				      if isSome (findTF (concl th))
				      then (is_c,CONV_RULE presimp_conv th) else (is_c,th)) ths2
	  in (!is_cnf,ths3) end
    end
end

(* ------------------------------------------------------------------------- *)
(* Generate fresh variable names (could just use genvars).                   *)
(* ------------------------------------------------------------------------- *)

fun propvar cnfv i = mk_var(cnfv^(int_to_string i),bool)

(* ------------------------------------------------------------------------- *)
(* Set up the basic definitional arrangement.                                *)
(* ------------------------------------------------------------------------- *)

fun localdefs cnfv tm (n,defs,lfn) =
    if is_neg tm then
	let val (n1,v1,defs1,lfn1) = localdefs cnfv  (rand tm) (n,defs,lfn) 
	    val  tm' = mk_neg v1 
	in (n1,rbapply defs1 tm',defs1,lfn1) 
	   handle NotFound => let val n2 = n1 + 1 
				  val v2 = propvar cnfv n2 
		       in  (n2,v2,RBM.insert(defs1,tm',v2),RBM.insert(lfn1,v2,tm)) end
	end
    else if is_conj tm orelse is_disj tm orelse is_imp tm orelse is_eq tm then
	let val (n1,v1,defs1,lfn1) = localdefs cnfv  (land tm) (n,defs,lfn) 
	    val (n2,v2,defs2,lfn2) = localdefs cnfv  (rand tm) (n1,defs1,lfn1) 
	    val tm' = mk_comb(mk_comb(rator(rator tm),v1),v2) 
	in (n2,rbapply defs2 tm',defs2,lfn2) 
	   handle NotFound => let val n3 = n2 + 1 
				  val v3 = propvar cnfv n3 
		       in (n3,v3,RBM.insert(defs2,tm',v3),RBM.insert(lfn2,v3,tm)) end
	end
    else if is_cond tm then
	let val (opr,args) = strip_comb tm
	    val (n1,v1,defs1,lfn1) = localdefs cnfv  (List.nth(args,0)) (n,defs,lfn) 
	    val (n2,v2,defs2,lfn2) = localdefs cnfv  (List.nth(args,1)) (n1,defs1,lfn1) 
	    val (n3,v3,defs3,lfn3) = localdefs cnfv  (List.nth(args,2)) (n2,defs2,lfn2)
	    val tm' =  mk_comb(mk_comb(mk_comb(opr,v1),v2),v3)
	in (n3,rbapply defs3 tm',defs2,lfn3) 
	   handle NotFound => let val n4 = n3 + 1 
				  val v4 = propvar cnfv n4 
		       in (n4,v4,RBM.insert(defs3,tm',v4),RBM.insert(lfn3,v4,tm)) end
	end
  else (n,rbapply defs tm,defs,lfn)
       handle NotFound => let val n1 = n + 1
			      val v1 = propvar cnfv n1 
		   in (n1,v1,RBM.insert(defs,tm,v1),RBM.insert(lfn,v1,tm)) end

(* ------------------------------------------------------------------------- *)
(* Just translate to fresh variables, but otherwise leave unchanged.         *)
(* ------------------------------------------------------------------------- *)

fun transvar_var cnfv (n,tm,vdefs,lfn) = 
    (n,rbapply vdefs tm,vdefs,lfn)
    handle NotFound =>  let val n1 = n + 1 
			    val v1 = propvar cnfv n1 
			in (n1,v1,RBM.insert(vdefs,tm,v1),RBM.insert(lfn,v1,tm)) end

fun transvar_lit cnfv (n,tm,vdefs,lfn) = 
    if is_neg tm then
	let val (n1,tm1,vdefs1,lfn1) = transvar_var cnfv (n,rand tm,vdefs,lfn) 
	in (n1,mk_neg tm1,vdefs1,lfn1) end
    else transvar_var cnfv (n,tm,vdefs,lfn)

fun transvar_clause cnfv (n,tm,vdefs,lfn) = 
    let val lits = List.rev (strip_disj tm)
	val (h,t) = (hd lits,tl lits)
	val (n,tm,vdefs,lfn) = 
	    List.foldl 
		(fn (p,(n,tm,vdefs,lfn)) => 
		    let val (n1,p1,vdefs1,lfn1) = transvar_lit cnfv (n,p,vdefs,lfn)
		    in (n1,mk_disj(p1,tm),vdefs1,lfn1) end)
		(transvar_lit cnfv (n,h,vdefs,lfn)) t
    in (n,tm,vdefs,lfn) end

(* ------------------------------------------------------------------------- *)
(* Check if something is clausal (slightly stupid).                          *)
(* ------------------------------------------------------------------------- *)

(* convert tm to CNF, assuming that it is of the form v =  v' op v'' *)
(* where all the v's are vars, and op is one of [~,\/,/\,==>,=]      *)
(* of course when op is ~, there is only one argument               *)
exception To_cnf_false
local 
val p_tm = mk_var("p",bool)
val q_tm = mk_var("q",bool)
val r_tm = mk_var("r",bool)
val s_tm = mk_var("s",bool)
in
fun to_cnf' tm = 
    let val (l,r) = dest_eq tm
	val (opr,args) = strip_comb r
    in case fst (dest_const opr) of
	   "~" => INST [p_tm |-> l, q_tm |-> (hd args)] dc_neg
	 | "\\/" => INST [p_tm |-> l, q_tm |-> (hd args),r_tm |-> (last args)] dc_disj
	 | "/\\" => INST [p_tm |-> l, q_tm |-> (hd args),r_tm |-> (last args)] dc_conj
	 | "==>" => INST [p_tm |-> l, q_tm |-> (hd args),r_tm |-> (last args)] dc_imp
	 | "=" => INST [p_tm |-> l, q_tm |-> (hd args),r_tm |-> (last args)] dc_eq
	 | "COND" => INST [p_tm |-> l, q_tm |-> (hd args), r_tm |-> (hd (tl args)), 
			   s_tm |-> (last args)] dc_cond	  
	 | _ => failwith("to_cnf': "^(fst (dest_const opr)))
    end
end

val cnfv_ref = ref "SP"

fun clausify tm lfn eq cls =
    let val fvs = free_vars eq 
	val eth = to_cnf' eq 
	val tth = INST (map (fn v => v |-> rbapply lfn v) fvs) eth 
	val xth = ADD_ASSUM tm (EQ_MP tth (REFL(rbapply lfn (land eq)))) 
    in zip (strip_conj(rand(concl eth))) (CONJUNCTS xth) @ cls end

fun to_cnf is_cnf tm =
    if is_cnf then 
	(NONE,HOLset.numItems(FVL[tm](HOLset.empty Term.var_compare)),RBM.mkDict Term.var_compare,
	 Array.fromList (zip (strip_conj(dest_neg tm)) (CONJUNCTSR (ASSUME (dest_neg tm))))) else
    let 
	val th = ASSUME tm 
 	val (is_cnf,ths) = GCONJUNCTS tm th
 	val (cnfv,vc,eqs,tops,lfn) = 
	    if is_cnf then
	    let val tops = List.map (fn (_,th) => (concl th,th)) ths 
	    in (NONE,HOLset.numItems (FVL [tm] (HOLset.empty Term.var_compare)),
		[],tops,RBM.mkDict Term.var_compare) end else
	    let 
 	        val cnfv = (!cnfv_ref)
	        val (n,tops,defs,lfn) =
		    itlist (fn (ic,th) => 
			    fn (m,tops,defs,lfn) =>
			       let val t = concl th 
			       in if is_T t orelse is_F t then (m,tops,defs,lfn) else
				  let val (n,v,defs',lfn') =
					  if ic then transvar_clause cnfv (m,t,defs,lfn)
					  else localdefs cnfv t (m,defs,lfn)
  				  in (n,(v,th)::tops,defs',lfn') end
			       end) ths
			   (~1,[],RBM.mkDict Term.compare,RBM.mkDict Term.var_compare)
 		val defg = RBM.foldl (fn (t,nv,a) => (t,nv)::a) [] defs 
		val mdefs = filter (fn (r,_) => not (is_var r)) defg 
		val eqs = map (fn (r,l) => mk_eq(l,r)) mdefs 
		val vc = (n + 1) 
	    in (SOME cnfv,vc,eqs,tops,lfn) end
 	val all_clauses = itlist (clausify tm lfn) eqs tops 
     in (cnfv,vc,lfn,Array.fromList all_clauses) end

(* verify that each t \in eqs in to_cnf above is of the required form: v = v' op v'' *)
(* this is only used during development, for sanity checking                         *)
fun verq eqs = 
List.app (fn eq =>
	     if is_eq eq then 
		 let val (l,r) = dest_eq eq
		 in if not (is_var l) then print "LHS is not a var\n" else
		    let val (opr,args) = strip_comb r
		    in if List.length args>2 then print "RHS op >2 args\n" else
		       if is_neg r then
			   if is_var (hd args) then () else print "neg RHS not a var\n"
		       else if  is_conj r orelse is_disj r orelse 
				is_imp r orelse is_eq r
		       then if is_var (hd args) andalso is_var (last args)
			    then () else print "RHS binop args not vars\n"
		       else print "RHS not a recognized op\n" 
		    end
		 end
	     else print "Not top-level eq!\n") eqs



end
end

