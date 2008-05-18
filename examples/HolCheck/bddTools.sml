
(* utility functions for working with bdd's and term-bdd's *)

structure bddTools =
struct

local

open Globals HolKernel Parse goalstackLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open Psyntax bossLib pairTheory pred_setTheory pred_setLib stringLib listTheory simpLib pairSyntax pairLib PrimitiveBddRules DerivedBddRules Binarymap PairRules pairTools boolSyntax Drule Tactical Conv Rewrite Tactic boolTheory listSyntax stringTheory boolSimps pureSimps listSimps numLib HolSatLib metisLib

open stringBinTree reachTheory commonTools

val dpfx = "bto_"

in

fun t2tb vm t = DerivedBddRules.GenTermToTermBdd (!DerivedBddRules.termToTermBddFun) vm t

fun mk_tb_res_subst red res vm = ListPair.map (fn (v,c) => (BddVar true vm v,BddCon (c=T) vm)) (red,res)


fun BddListConj vm (h::t) = if (List.null t) then h else PrimitiveBddRules.BddOp (bdd.And, h, (BddListConj vm t))
|   BddListConj vm [] = PrimitiveBddRules.BddCon true vm;

fun BddListDisj vm (h::t) = if (List.null t) then h else PrimitiveBddRules.BddOp (bdd.Or, h, (BddListDisj vm t))
|   BddListDisj vm [] = PrimitiveBddRules.BddCon false vm;


(* return bdd b as a DNF term (this is similar to the output of bdd.printset and in fact mimics the code) *)
(* used when the term part of bdd is higher order but we need the boolean equivalent                      *)
(* and it would be inefficient to unwind the higher order bits                                            *)
(* bddToTerm returns a nested i-t-e term that can get way too big                                         *) 
fun bdd2dnf vm b =
    if (bdd.equal b bdd.TRUE) then T  
    else if (bdd.equal b bdd.FALSE) then F 
    else let val pairs = Binarymap.listItems vm
	     fun get_var n =
		 case assoc2 n pairs of
		     SOME(str,_) => mk_var(str,bool)
		   | NONE        => (failwith("bdd2dnf: Node "^(Int.toString n)^" has no name"))
	     fun b2t_aux b assl =
		 if (bdd.equal b bdd.TRUE)
		 then [assl]
		 else
		     if (bdd.equal b bdd.FALSE)
		     then []
		     else let val v = get_var(bdd.var b)
			  in (b2t_aux (bdd.high b) (v::assl))@(b2t_aux (bdd.low b) ((mk_neg v)::assl)) end
	 in
	     list_mk_disj (List.map list_mk_conj (b2t_aux b []))
	 end;

fun bdd2cnf vm b =
    if (bdd.equal b bdd.TRUE) then T  
    else if (bdd.equal b bdd.FALSE) then F 
    else let val pairs = Binarymap.listItems vm
	     fun get_var n =
		 case assoc2 n pairs of
		     SOME(str,_) => mk_var(str,bool)
		   | NONE        => (failwith("bdd2cnf: Node "^(Int.toString n)^" has no name"))
	     fun b2t_aux b assl =
		 if (bdd.equal b bdd.TRUE)
		 then []
		 else
		     if (bdd.equal b bdd.FALSE)
		     then [assl]
		     else let val v = get_var(bdd.var b)
			  in (b2t_aux (bdd.low b) (v::assl))@(b2t_aux (bdd.high b) ((mk_neg v)::assl)) end
	 in
	     list_mk_conj (List.map list_mk_disj (b2t_aux b []))
	 end;

fun getIntForVar vm (s:string) =  Binarymap.find(vm,s);

fun getVarForInt vm (i:int) = 
    let val l = List.filter (fn (ks,ki) => ki=i) (Binarymap.listItems vm)
in if List.null l then NONE else SOME (fst(List.hd l)) end

fun termToBdd vm t = PrimitiveBddRules.getBdd(DerivedBddRules.GenTermToTermBdd (!DerivedBddRules.termToTermBddFun) vm t) 

(* transform term part of term-bdd using the supplied conversion; suppress UNCHANGED exceptions *)
fun BddConv conv tb = DerivedBddRules.BddApConv conv tb handle Conv.UNCHANGED => tb;

(* spells out one state in the bdd b *)
fun gba b vm = 
let val al = bdd.getAssignment (bdd.toAssignment_ b)
    fun lkp i = fst(List.hd (List.filter (fn (k,j) => j=i) (Binarymap.listItems vm)))
    in List.map (fn (i,bl) => (lkp i, bl)) al end

(* folds in all the messing about with pair sets and what nots *)
fun bdd_replace vm b subs = 
    let val vprs = List.map dest_subst subs
	val nprs = List.map (getIntForVar vm o term_to_string2 ## getIntForVar vm o term_to_string2) vprs
	val nsubs =  bdd.makepairSet nprs
	val res = bdd.replace b nsubs  
    in res end

(* given a string from the output of bdd.printset (less the angle brackets), constructs equivalent bdd *)
fun mk_bdd s = 
let val vars = List.map (fn (vr,vl) => if vl=0 then bdd.nithvar vr else bdd.ithvar vr) 
			(List.map (fn arg =>
				      let val var = List.hd arg
					  val vl = List.last arg 
				      in ((Option.valOf o Int.fromString) var,
					  (Option.valOf o Int.fromString) vl) 
				      end) 
				  (List.map (String.tokens (fn c => Char.compare(c,#":")=EQUAL)) 
					    (String.tokens (fn c =>  Char.compare(c,#",")=EQUAL) s)))
    in List.foldl (fn (abdd,bdd) => bdd.AND(abdd,bdd)) (bdd.TRUE) vars end

(* constructs the bdd of one of the states of b, including only the vars in vm *)
fun mk_pt b vm = 
    let 
	val _ = dbgTools.DEN dpfx "mpt" (*DBG*)
	val res = 
	    if bdd.equal bdd.FALSE b then bdd.FALSE
	    else let val b1 =  List.map (fn (vi,tv) => if tv then bdd.ithvar vi else bdd.nithvar vi) 
					(List.filter (fn (vi,tv) => Option.isSome(getVarForInt vm vi))
						 (bdd.getAssignment (bdd.fullsatone b)))
		 in List.foldl (fn (abdd,bdd) => bdd.AND(abdd,bdd)) (bdd.TRUE) b1 end
 	val _ = dbgTools.DBD (dpfx^"mp_res") res (*DBG*)
 	val _ = dbgTools.DEX dpfx "mpt" (*DBG*)
    in res end

(* computes the image under bR of b1 *) (*FIXME: what's with the foldl's in the second last line?*)
fun mk_next state bR vm b1 = 
    let 
	val _ = dbgTools.DEN dpfx "mn" (*DBG*)
	fun getIntForVar v = Binarymap.find(vm,v)
	val sv = List.map term_to_string (strip_pair state)
	val svi =  List.map getIntForVar sv
	val spi = List.map getIntForVar (List.map (fn v => v^"'") sv)
	val s = bdd.makeset svi
	val sp2s =  bdd.makepairSet (ListPair.zip(List.foldl (fn (h,t) => h::t) [] (spi),
						  List.foldl (fn (h,t) => h::t) [] (svi)))
	val res = bdd.replace (bdd.appex bR b1 bdd.And s) sp2s  
	val _ = dbgTools.DEX dpfx "mn" (*DBG*)
    in res end

(* computes the preimage under bR of b1 *)(*FIXME: what's with the foldl's in the second last line?*)
fun mk_prev state bR vm b1 = 
    let 
	val _ = dbgTools.DEN dpfx "mpv" (*DBG*)
	fun getIntForVar v = Binarymap.find(vm,v)
	val sv = List.map term_to_string (strip_pair state)
	val svi =  List.map getIntForVar sv
	val spi = List.map getIntForVar (List.map (fn v => v^"'") sv)
	val sp = bdd.makeset spi
	val s2sp =  bdd.makepairSet (ListPair.zip(List.foldl (fn (h,t) => h::t) [] (svi),
						  List.foldl (fn (h,t) => h::t) [] (spi)))
	val res = bdd.appex bR (bdd.replace b1 s2sp) bdd.And sp 
	val _ = dbgTools.DEX dpfx "mpv" (*DBG*)
    in res end

fun mk_g'' ((fvt',t')::fvl) (fvt,t) ofvl = 
       if (Binaryset.isEmpty(Binaryset.intersection(fvt,fvt'))) 
       then mk_g'' fvl (fvt,t) ofvl
       else let val ofvl' = List.filter (fn (_,t) => not(Term.compare(t,t')=EQUAL)) ofvl 
	    in Binaryset.add(mk_g'' ofvl' (Binaryset.union(fvt,fvt'),t) ofvl',(fvt',t')) end
| mk_g'' [] (fvt,t) ofvl = Binaryset.add (Binaryset.empty (Term.compare o (snd ## snd)),(fvt,t))

fun mk_g' ((fvt,t)::fvl) = 
    let val fvs' = mk_g'' fvl (fvt,t) fvl
	val fvs = Binaryset.addList(Binaryset.empty (Term.compare o (snd ## snd)),fvl)
    in (fvs'::(mk_g' (Binaryset.listItems (Binaryset.difference(fvs,fvs'))))) end
| mk_g' [] = [] 

(* group terms in tc by free_vars *)
fun mk_g tc =
    let val fvl = ListPair.zip(List.map (fn t => Binaryset.addList(Binaryset.empty Term.compare, free_vars t)) tc,tc)
	val vcfc = mk_g' fvl 
    in List.map (fn l => List.foldl (fn ((fvt,t),(fvta,ta)) => (Binaryset.union(fvt,fvta),t::ta)) (Binaryset.empty Term.compare,[]) l) (List.map Binaryset.listItems vcfc) end
  
(* given a string*bool list and a term list, uses the first list as a set of substitutions for the terms, and simplify,
   filtering out any that simplify to true  *)
(* this is used with the output of gba (t being the conjuncts of R as grouped by mk_g) to get a term representation for the next state of the state given by sb *)
fun mk_sb sb t = 
 let val hsb = List.map (fn (t1,t2) => (mk_var(t1,bool)) |-> (if t2 then T else F)) sb
 in List.map (fn (t,t') => if (Term.compare(F,t)=EQUAL) then (t,SOME t') else (t,NONE)) 
	 (List.filter (fn (t,t') => not (Term.compare(T,t)=EQUAL)) 
	 (List.map (fn (t,t') => (rhs(concl(SIMP_CONV std_ss [] (Term.subst hsb t))) handle ex => (Term.subst hsb t),t')) 
	  (ListPair.zip(t,t)))) 
 end

(* return a satisfying assignment for t, as a HOL subst *)
fun findAss t = 
    let val th = SAT_PROVE (mk_neg t) handle HolSatLib.SAT_cex th => th
	val t = strip_conj (fst(dest_imp (concl th)))
        val t1 = List.filter (fn v =>  (if is_neg v then not (is_genvar(dest_neg v)) else not (is_genvar v))) t
	fun ncompx v = not (String.compare(term_to_string v, "x")=EQUAL)
	val t2 = List.filter (fn v => if is_neg v then ncompx (dest_neg v) else ncompx v) t1
    in  List.map (fn v => if is_neg v then (dest_neg v) |-> F else v |-> T) t2 end

(* given a list of vars and a HOL assignment to perhaps not all the vars in the list, 
   return an order preserving list of bool assgns *)
(* this is for use with MAP_EVERY EXISTS_TAC *)
fun exv l ass = 
let val t1 = List.map (fn v => subst ass v) l
    in List.map (fn v => if is_var v then T else v) t1 end;
              
(* given an existential goal, 
 replaces all quantified variables with satisfying values (assumes entire goal is propositional)*)
fun SAT_EXISTS_TAC (asl,w) =
    let val (vl,t) = strip_exists w
	val ass = findAss t
	val exl = exv vl ass
in (MAP_EVERY EXISTS_TAC exl) (asl,w) end

(* take a point bdd (i.e. just one state) and return it as concrete instance of state 
   annotated with var names *)
fun pt_bdd2state state vm pb = 
    let val _ = dbgTools.DEN dpfx "pb2s"(*DBG*)
	val _ = dbgTools.DBD (dpfx^"pb2s_pb") pb(*DBG*)
	val _ = Vector.app (dbgTools.DNM (dpfx^"pb2s_pb_support")) (bdd.scanset (bdd.support pb)) (*DBG*)
	val i2val = list2imap((bdd.getAssignment o bdd.toAssignment_) pb)
	val res = list_mk_pair (List.map (fn v => if Binarymap.find(i2val,Binarymap.find(vm,v)) 
						  then mk_bool_var v else mk_neg (mk_bool_var v)
					 handle ex => mk_bool_var v) 
					 (List.map term_to_string2 (strip_pair state))) 
	val _ = dbgTools.DEX dpfx "pb2s"(*DBG*)
    in res end
   

(* make varmap. if ordering is not given, just shuffle the current and next state vars. 
   FIXME: do a better default ordering *)
fun mk_varmap state bvm = 
    let val bvm = if (Option.isSome bvm) then Option.valOf bvm 
		  else let val st = strip_pair state
			   val st' = List.map prime st
			   val bvm = List.map (term_to_string2) (List.concat (List.map (fn (v,v') => [v',v]) 
										       (ListPair.zip(st,st'))))
		       in bvm end
	val vm = List.foldr (fn(v,vm') => Varmap.insert v vm') (Varmap.empty) 
			    (ListPair.zip(bvm,(List.tabulate(List.length bvm,I))))
	val _ = if (bdd.getVarnum()<(List.length bvm)) 
		then bdd.setVarnum (List.length bvm) else () (* this tells BuDDy where and what the vars are *)	  
    in vm end

end
end

(* 
(*FIXME: move this comment into documentation *)
(* debugging usage example *)
(* this assumes I1, R1, T1, ks_def and wfKS_ks have been computed... see alu.sml or ahb_total.sml or scratch.sml on howto for that*)
load "cearTools"; 
load "debugTools";
open cearTools; 
open debugTools;
val sc = DerivedBddRules.statecount;
val dtb = PrimitiveBddRules.dest_term_bdd;
open PrimitiveBddRules;
        val vm = List.foldr (fn(v,vm') => Varmap.insert v vm') (Varmap.empty)
			    (ListPair.zip(bvm,(List.tabulate(List.length bvm,fn x => x))))
	val _ = bdd.setVarnum (List.length bvm) (* this tells BuDDy where and what the vars are *)
	val tbRS = muTools.RcomputeReachable (R1,I1) vm;
	val brs = Primiti#veBddRules.getBdd tbRS;
	val Ree = Array.fromList []
	val RTm = muCheck.RmakeTmap T1 vm	
        val Tm = List.map (fn (nm,tb) => (nm,getTerm tb)) (Binarymap.listItems RTm) (* using nontotal R for ahbapb composition *)
	val (dks_def,wfKS_dks) = muCheck.mk_wfKS Tm I1 NONE NONE
	val chk = fn mf => muCheck.muCheck RTm Ree I1 mf (dks_def,wfKS_dks) vm NONE handle ex => Raise ex;
(* note how dbg below returns debugging info such as a bad state, it's forward and rear states and more readable versions of those *)
fun chk2 cf = let val tb2 = chk (ctl2mu cf) 
		  val bb2 = PrimitiveBddRules.getBdd tb2 
		  val bd = bdd.DIFF(brs,bdd.AND(brs,bb2))
		  val dbg = if bdd.equal bi (bdd.AND(bi,bdd.AND(brs,bb2))) then NONE
			    else let val Rtb = Binarymap.find (RTm,".") 
				     val b2 = mk_pt bd vm
				     val bn = mk_next I1 (getBdd Rtb) vm b2
				     val bp = mk_prev I1 (getBdd Rtb) vm b2
				     val sb = mk_sb (gba b2 vm) (strip_conj (getTerm Rtb)) 
				 in SOME (Rtb,b2,bn,bp,sb) end
	      in (tb2,bdd.AND(brs,bb2),bd,dbg) end;

*)


