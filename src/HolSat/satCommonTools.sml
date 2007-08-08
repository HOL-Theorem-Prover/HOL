  
(* miscellaneous useful stuff that doesn't fit in anywhere else *)
structure satCommonTools = 
struct 

local

open Globals HolKernel Parse boolSyntax Term Drule
open satTheory

in

structure RBM = Redblackmap

fun rbapply m k = RBM.find(m,k)

fun tryrbapplyd m k d = rbapply m k handle NotFound => d

 
fun pair_map f (x,y) = (f x,f y)

(*********** terms **************)

val mk_var = Term.mk_var;

val land = rand o rator

fun is_T tm = Term.compare(tm,T)=EQUAL

fun is_F tm = Term.compare(tm,F)=EQUAL

fun termFromFile fname = 
    let val ins        = TextIO.openIn (fname^".term")
	val res        = TextIO.inputAll ins
	val _          = TextIO.closeIn ins
    in Term [QUOTE res] end

fun termToFile fname t = 
let val fout = TextIO.openOut (fname^".term")
    val _ = TextIO.output (fout,with_flag (show_types,true) term_to_string t)
    val _ = TextIO.flushOut fout
    val _ = TextIO.closeOut fout
in () end

(************ HOL **************)

local 
    val t = mk_var("t",bool)
    val NOT_NOT2 = SPEC_ALL NOT_NOT
in
fun NOT_NOT_CONV tm = INST [t|->rand(rand tm)] NOT_NOT2
end

(* Like CONJUNCTS but assumes the conjunct is bracketed right-assoc. *)
(* Not tail recursive. Here only as a reference implementation *)
fun NTL_CONJUNCTSR th =
    if is_conj (concl th)
    then 
	let val (th1,th2) = CONJ_PAIR th
	in th1::(NTL_CONJUNCTSR th2) end
    else [th]

(* CPS version of NTL_CONJUNCTSR. Does not grow call stack. *)
fun CONJUNCTSR th = 
    let fun CPS_CONJUNCTSR th k = 
	    if is_conj (concl th)
	    then let val (th1,th2) = CONJ_PAIR th
		 in CPS_CONJUNCTSR th2 (fn ret => k (th1::ret)) end
	    else k [th]
    in CPS_CONJUNCTSR th I end

end
end
