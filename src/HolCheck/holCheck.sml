
(* user interface to HolCheck *)
structure holCheck =
struct

local 

open Globals HolKernel Parse
open ksTools
open ctlCheck
open cearTools
open PrimitiveBddRules
open Binarymap
open Listsort
open boolTheory
open holCheckTools
open bddTools
open boolSyntax

val dbghc = holCheckTools.dbgall

fun DMSG m v = if v then let val _ = print "holCheck: " val _ = holCheckTools.DMSG m v in () end else ()

datatype hcinit = 
    CTL_INIT of ((thm * thm) option * 
		 ((term list * thm * thm * (string,term_bdd) dict) option *
		  ((term * thm * (int, thm) dict * thm * term_bdd) * term * term * term *
		   (string * term_bdd) array * (thm * thm * thm) * int) option) option) option
  | ABS_INIT of ((term list * thm * thm * (string,term_bdd) dict) option *
		 ((term * thm * (int, thm) dict * thm * term_bdd) * term * term * term * 
		  (string * term_bdd) array * (thm * thm * thm) * int) option) option

fun get_ctl_init (CTL_INIT ic) = ic | get_ctl_init _ = failwith ("get_ctl_init: Cache type mismatch")
fun get_abs_init (ABS_INIT ic) = ic | get_abs_init _ = failwith ("get_abs_init: Cache type mismatch")

fun merge_init_caches ctlic absic = 
    let val _ = DMSG (ST "merge_init_caches\n") (dbghc)(*DBG*)
	val cic = get_ctl_init (Option.valOf ctlic)
	val aic = get_abs_init (Option.valOf absic)
	val (ctlic,absic) = 
	    if (Option.isSome cic) then 
		if (Option.isSome aic) then (ctlic,absic) (* both caches already init'd *)
		else let val absicsnd  = snd(Option.valOf(snd(Option.valOf cic)))					 
			 val (_,_,_,RTm) = Option.valOf(fst(Option.valOf(snd(Option.valOf cic))))
		     in (ctlic,SOME (ABS_INIT (SOME (SOME ([],TRUTH,TRUTH,RTm),
						     if Option.isSome absicsnd then (* only if abstraction took place *)
							 let val (a,b,c,d,e,_,f) = Option.valOf absicsnd 
							 in SOME (a,b,c,d,e,(TRUTH,TRUTH,TRUTH),f) end 
						     else NONE))))
		     end (* ctl's abs's shareables given to abs *)
	    else if (Option.isSome aic) 
	    then let val absicsnd = snd(Option.valOf aic)
		     val (_,_,_,RTm) = Option.valOf(fst(Option.valOf aic))
		 in (SOME (CTL_INIT (SOME (NONE,SOME (SOME ([],TRUTH,TRUTH,RTm),
						      if Option.isSome absicsnd then (* only if abstraction took place *)
							  let val (a,b,c,d,e,_,f) = Option.valOf absicsnd 
							  in SOME (a,b,c,d,e,(TRUTH,TRUTH,TRUTH),f) end 
						      else NONE)))),absic) 
		 end (* abs's shareables given to ctl*)
	    else (ctlic,absic) (* both caches empty *)
	val _ = DMSG (ST "merge_init_caches done\n") (dbghc)(*DBG*)
    in (ctlic,absic) end

fun get_ks_defs (ctlic,absic)  = 
    let val _ = DMSG (ST "get_ks_def\n") (dbghc)(*DBG*)
	val cic = get_ctl_init (Option.valOf ctlic)
	val aic = get_abs_init (Option.valOf absic)
	val ksd = 
	    (if (Option.isSome cic) then 
		 let val (_,ks_def,_,_) =  Option.valOf(fst(Option.valOf(snd(Option.valOf cic)))) in 
		     if (Term.compare(concl ks_def,T)=EQUAL) then NONE else SOME ks_def end (* aic may have been stuffed by cic*)       
	     else NONE,
	     if (Option.isSome aic) then 
		 let val (_,ks_def,_,_) =  Option.valOf(fst(Option.valOf aic)) 
		 in  if (Term.compare(concl ks_def,T)=EQUAL) then NONE else SOME ks_def end (* aic may have been stuffed by cic*)
   	     else NONE)
	val _ = DMSG (ST "get_ks_def done\n") (dbghc)(*DBG*)
    in ksd end

fun holCheck_aux (I1,T1,_,ksname,_,_) state apl vm (CTL_INIT init_cache) f = 
    let val (results,init_cache) = ctlCheck I1 (snd(hd T1)) state vm apl ksname init_cache f
    in (results, SOME (CTL_INIT init_cache)) end
|   holCheck_aux (I1,T1,Ric,ksname,_,_) state apl vm (ABS_INIT init_cache) f = 
    let val (results,init_cache) =  absCheck I1 T1 state Ric vm apl ksname init_cache f 
    in (results, SOME (ABS_INIT init_cache)) end

in 

(*FIXME: should return mu model as well even if mc only done for ctl *)
fun holCheck  (TR as (I1,T1,_,_,bvm,state)) fl apl init_cache = 
    let val state = if Option.isSome state then Option.valOf state else mk_state I1 T1
	val vm = mk_varmap state bvm
	val (results,init_cache) = 
	    List.foldl (fn (f,(results,(ctlic,absic))) =>  
			   let val is_mu = ((String.compare(fst(dest_type(type_of f)),"mu"))=EQUAL)
			       val (ctlic,absic) = merge_init_caches ctlic absic
			       val (res,ic) = if is_mu
					      then holCheck_aux TR state apl vm (Option.valOf absic) f
					      else holCheck_aux TR state apl vm (Option.valOf ctlic) f 
			       val _ = DMSG (ST "holCheck call done\n") (dbghc)(*DBG*)
			   in (results@[res],if is_mu then (ctlic,ic) else (ic,absic)) end)  
		       ([],if not (Option.isSome init_cache) then (SOME (CTL_INIT NONE), SOME (ABS_INIT NONE)) 
			   else Option.valOf init_cache) fl
    in (results, get_ks_defs init_cache, SOME init_cache) end

end
end