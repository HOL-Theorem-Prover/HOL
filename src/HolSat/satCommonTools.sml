  
(* miscellaneous useful stuff that doesn't fit in anywhere else *)
structure satCommonTools = 
struct 

local

open Globals HolKernel Parse 

open boolSyntax Term Drule

in

 
fun pair_map f (x,y) = (f x,f y)

(*********** terms **************)

val mk_var = Term.mk_var;

val land = rand o rator

fun is_T tm = Term.compare(tm,T)=EQUAL

fun is_F tm = Term.compare(tm,F)=EQUAL

(************ HOL **************)

(* Like CONJUNCTS but assumes the conjunct is bracketed right-assoc. *)
(* Not tail recursive. Here only as a reference implementation *)
fun NTL_CONJUNCTSR th =
    if is_conj (concl th)
    then 
	let val (th1,th2) = CONJ_PAIR th
	in th1::(NTL_CONJUNCTSR th2) end
    else [th]

(* CPS version of NTL_CONJUNCTSL. Does not grow call stack. *)
fun CONJUNCTSR th = 
    let fun CPS_CONJUNCTSR th k = 
	    if is_conj (concl th)
	    then let val (th1,th2) = CONJ_PAIR th
		 in CPS_CONJUNCTSR th2 (fn ret => k (th1::ret)) end
	    else k [th]
    in CPS_CONJUNCTSR th I end

fun ERC lt tm =
    if is_comb lt 
	then let val ((ltl,ltr),(tml,tmr)) = pair_map dest_comb (lt,tm)
	     in (ERC ltl tml)@(ERC ltr tmr) end
    else 
	if is_var lt
	    then [lt |-> tm]
	else []

(* (E)asy REWR_CONV which assumes that the supplied theorem is ground and quantifier free, 
   so type instantiation and free/bound var checks are not needed *)
(* no restrictions on the term argument *)
fun EREWR_CONV th tm = 
    let 
	val lt = lhs(concl th)
	val il = ERC lt tm
    in INST il th end


end
end
