
(* user interface to HolCheck *)
structure holCheck :> holCheck =
struct

local

    open Globals HolKernel Parse
    open bddTools ksTools ctlCheck cearTools modelTools internalCacheTools

    val dpfx = "hc_"

    fun init model =
	let val _ = dbgTools.DEN dpfx "i"(*DBG*)
	    val _ = if bdd.isRunning() then () else bdd.init 1000000 10000 (* FIXME: allow user to supply the nums here *)
	    val (I1,T1,Ric,ksname,bvm,state,fl,_,ic) = dest_model model
	    val state = if isSome state then valOf state else mk_state I1 T1
	    val (apl,apsubs) = if get_flag_abs model then holCheckTools.mk_abs_APs fl state else (NONE,[])
	    val vm = mk_varmap state bvm
	    val _ = dbgTools.DEX dpfx "i"(*DBG*)
	in (I1,T1,Ric,ksname,bvm,state,fl,ic,vm,apl,apsubs) end

in

fun holCheck model =
    let val _ = dbgTools.DEN dpfx "hc"(*DBG*)
	val _ = profTools.bgt (dpfx^"hc")(*PRF*)
	val (I1,T1,Ric,ksname,bvm,state,fl,ic,vm,apl,apsubs) = init model
	val (results,ic) =
	    List.foldl (fn ((nf,f),(results,ic)) =>
			   let
			       val _ = dbgTools.DST (dpfx^"hc_nf: "^nf) (*DBG*)
			       val is_mu = ((String.compare(fst(dest_type(type_of f)),"mu"))=EQUAL)
			       val (res,ic) =
				   if is_mu
				   then let val (r,(i,c)) = absCheck I1 T1 state Ric vm ksname (get_abs ic,get_common ic)
								     (nf,f) (apl,apsubs)
					in (r,((set_common c) o (set_abs i)) ic) end
				   else let val (r,(i,c)) = ctlCheck I1 T1 state Ric vm ksname (get_ctl ic,get_common ic)
								     (nf,f) (apl,apsubs)
					in (r,((set_common c) o (set_ctl i)) ic) end
			   in (results@[res],ic) end)
		       ([],if isSome ic then valOf ic else set_vm vm empty_ic) fl
	val _ = profTools.ent (dpfx^"hc")(*PRF*)
	val _ = dbgTools.DEX dpfx "hc"(*DBG*)
    in (((set_ic ic) o (set_results results)) model) end

end
end
