
(* utility functions for environments *) 

structure envTools =
struct

local

open Globals HolKernel Parse goalstackLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open Psyntax;

open bossLib;
open pairTheory;
open pred_setTheory;
open pred_setLib;
open stringLib;
open listTheory;
open simpLib;
open pairSyntax;
open pairLib;
open PrimitiveBddRules;
open DerivedBddRules;
open Binarymap;
open PairRules;
open pairTools;
open setLemmasTheory;
open muSyntax
open muSyntaxTheory;
open muTheory;
open boolSyntax;
open Drule;
open Tactical;
open Conv;
open Rewrite;
open Tactic;
open boolTheory;
open listSyntax;
open stringTheory;
open stringBinTree;
open boolSimps;
open pureSimps;
open listSimps;
open numLib;
open reachTheory;
open bddTools
open envTheory
open lazyTools

in

fun env_type state = stringLib.string_ty --> ((type_of state) --> bool)

val _ = set_trace "notify type variable guesses" 0;
val empty_env_tm = ``env$EMPTY_ENV``
val env_tm = inst [alpha|->(env_type ``x``)]  ``e`` (* FIXME: get rid of the x *)
val _ = set_trace "notify type variable guesses" 1;

(* rvl: list of (rel var:string,corresponding boolean term for state set:bool) pairs 
   state: term representing state vector (type is bool # bool # ... # bool)
   OUT: term for env: string -> 'state->bool, of the form \rv. if rv=rv1 then \state.s1 else if rv=rv2 ... else \state.F *)
 fun mk_env (rvh::rvt) state = ``(^(mk_env rvt state))[[[^(fromMLstring(fst rvh))<--^(mk_pabs(state,(snd rvh)))]]]``
 |   mk_env [] state = (inst [alpha |-> type_of state] empty_env_tm)

(* given an env e[[[Q<--X]]], return (e,(Q,x)) *)
fun dest_env ie = let val (test,x,ie2) = dest_cond(body(snd(dest_eq(concl(ONCE_REWRITE_CONV [ENV_UPDATE_def] ie))))) 
		 in (fst (dest_comb ie2),(snd(dest_eq test),x)) end

(* given an env term, returns the term  assigned to q *) 
local 
fun get_env_val_aux empty_env q e = 
    if (Term.compare(empty_env,e)=EQUAL) then F
    else let val (_,ll) = strip_comb e
	 in if (Term.compare(q,List.nth(ll,1))=EQUAL) then List.nth(ll,2) else get_env_val_aux empty_env q (List.nth(ll,0)) end 
in fun get_env_val state q e = get_env_val_aux (mk_abs(mk_var("q",``:string``),mk_pabs(state,F))) q e end

(*given an env ie s.t. ie(bv)=X, return |- ie(bv) = X without simplifying X and without opening up ie (which is a huge nested cond)*)
local
fun eval_env_thm ie ieo bv seth thl = 
    let val (e,(v,x)) = dest_env ie
    in if (Term.compare(v,bv)=EQUAL) 
       then PURE_REWRITE_CONV ((ISPECL [e,v,x] ENV_EVAL)::thl) (mk_comb(ieo,bv))
       else let val seqth = Binarymap.find(Binarymap.find(seth,fromHOLstring bv),fromHOLstring v) 
	    in eval_env_thm e ieo bv seth ((MP (ISPECL [e,bv,v,x] ENV_UPDATE_INV) seqth)::thl) end
    end
in    
fun eval_env ie ieo bv state seth sel thl = 
    mk_lthm (fn _ => (mk_eq(mk_comb(ieo,bv),get_env_val state bv ie),(fn _ => eval_env_thm ie ieo bv seth thl)))
	    (fn _ => eval_env_thm ie ieo bv seth thl)  
end

(* given an env e[[[Q<--X]]]...[[[Qn<--Xn]]], returns [(Q,X)...(Qn,Xn)] *)
fun strip_env state ie = 
    if (Term.compare(ie, inst [alpha|->type_of state] empty_env_tm)=EQUAL) then []
    else let val (ie2,(q,s)) = dest_env ie in (q,s)::(strip_env state ie2) end 

(* returns the prefix of ie upto and including the last assignment to q *)
fun env_prefix state q ie = 
    fst (List.foldl (fn ((q',s),(ie,done)) => if done then (ie,done) else 
		     let val (ie',(_,_)) = dest_env ie in if (Term.compare(q,q')=EQUAL) then (ie,true) else (ie',false) end) 
	 (ie,false) (strip_env state ie))

(* conversional to access the nth-last map's value in an ie *)
fun ENV_FIND_CONV ie 0 = RAND_CONV 
| ENV_FIND_CONV ie n = RATOR_CONV o RATOR_CONV o RAND_CONV o (ENV_FIND_CONV ie (n-1)) 

(* return theorems for normalised ie and ie', in which the mapping in which ie and ie' are different is moved to the end. 
   ASSERT: ie and ie' are different in only one mapping *semantically*
           it may happen that a mapping is different in syntax, but the semantics are same. This happens *only* if some Q maps
           to {} in ie and FP....0 in ie' (and analogously for gfp's) 
   ASSERT: in ie and ie', the map order is the same i.e. nth mapping in both is for the same var *)
fun ENV_NORM_CONV seth state ie ie' = 
    if (Term.compare(ie,ie')=EQUAL) then (REFL ie,REFL ie') else
    let 
	val _ = print "ENV_NORM_CONV\n"(*DBG*)
	val _ = print_term ie val _ = print " enc ie\n"(*DBG*)
	val _ = print_term ie' val _ = print " enc ie'\n"(*DBG*)
	val maps = strip_env state ie
	val maps' = strip_env state ie'
	val eqths = List.map (fn ((q,s),(q',s')) => (* theorems converting semantically equal terms to syntactically equal ones *)
			       if (Term.compare(s,inst [alpha|->type_of state] pred_setSyntax.empty_tm)=EQUAL) 
			       then SOME (REWRITE_CONV[STATES_def,ENV_EVAL,EMPTY_ENV_def] s') else NONE)
				       (ListPair.zip(maps,maps'))
	val (ie_eqth,_) = List.foldl (fn (eqth,(ie,n)) => (* |- old_ie = old_ie with {}'s replaced by appropriate values to match ie' *)
				     if (Option.isSome eqth) 
				     then (CONV_RULE(RHS_CONV(ENV_FIND_CONV ie n (ONCE_REWRITE_CONV [GSYM(Option.valOf eqth)]))) ie,n+1)
				     else (ie,n)) ((REFL ie),0) eqths 			       
	val _ = print_thm ie_eqth val _ = print " ie_eqth\n"(*DBG*)
	val ie2 = rhs(concl ie_eqth) (* now find the mapping that is different and move it to the end *)
	val _ = print_term ie2 val _ = print " ie2\n"(*DBG*)
	val maps2 =  strip_env state ie2
	val (suffix,_) = List.foldl (fn (((q,s),(q',s')),(l,done)) => (* suffix of (ie2,ie') upto the differing mapping *)
				   if done then (l,done) else if (Term.compare(s,s')=EQUAL) 
							   then (((q,s),(q',s'))::l,false) else (((q,s),(q',s'))::l,true))  
				       ([],false) (ListPair.zip(maps2,maps'))
        val res = if List.length suffix=1 then (ie_eqth,REFL ie') (* diff map already at the end *) 
		  else let 
		    val (suff,suff') = ListPair.unzip suffix
		    val ((q,s),rest,(q',s'),rest') = (hd suff,tl suff,hd suff',tl suff') (* so s and s' are the differing assignments *)
		    fun mv_map_to_end_CONV (q,s) rest ie_th = (*go through rest, swapping q with each var in rest, till q is at end*) 
			List.foldl (fn ((q',s'),ie) => 
				    let val iet = rhs(concl ie)
					val ep = env_prefix state q' iet 
					val (ep',(_,_)) = dest_env iet
					val (ep'',(_,_)) = dest_env ep'
					val th = MP (ISPECL [ep'',q,q',s,s'] ENV_SWAP) 
					    (Binarymap.find(Binarymap.find(seth,fromHOLstring q),fromHOLstring q'))
					val _ = print_thm th val _ = print " env th\n"
				    in CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV [th])) ie end) 
			ie_th rest 
		in (mv_map_to_end_CONV (q,s) rest ie_eqth,mv_map_to_end_CONV (q',s') rest' (REFL ie')) end
	val _ = print "ENV_NORM_CONV done\n"(*DBG*)
    in res end

end
end
