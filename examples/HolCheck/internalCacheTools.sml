structure internalCacheTools =
struct

local

open Globals HolKernel Parse
open PrimitiveBddRules
open Binarymap

in

open Abbrev

type common_ic =
     {abs_df : ((term * term_bdd) * term * term * term * (string * term_bdd) array * int * thm * (int,thm) dict * thm) option}

type mu_ic = {ks:(term list * thm * thm * (string,term_bdd) dict * (thm * thm) option) option,
	      th:((thm list * (thm * term_bdd option * term) *
		   (thm * (thm * thm) * term list * (term_bdd * term_bdd) list) *
		   (thm * thm * thm * thm * term * term * term * term * term list *
		    hol_type)) * term * thm list) option}

type abs_ic = {mu: mu_ic,
	       mth:((thm list * (thm * term_bdd option * term) *
		   (thm * (thm * thm) * term list * (term_bdd * term_bdd) list) *
		   (thm * thm * thm * thm * term * term * term * term * term list *
		    hol_type)) * term * thm list) option, (* theorems from muCheck when doing abstraction *)
	       ks: (term * (string * term) list * term_bdd *
		    (term list * thm * thm *  (string,term_bdd) dict)) option,
	       (*ks2: (term list * thm * thm * (thm * thm) option) option,*)
	       th: (thm * thm * thm *thm) option
	        }

type ctl_ic = {th:(thm * thm) option,
	       ks:(term list * thm * thm * (string, term_bdd) dict * thm * term) option,
	       abs: abs_ic}

type ic = {common: common_ic,
	   ctl: ctl_ic,
	   abs: abs_ic,
	   vm: (string, int) dict option}

val empty_ic = {common={abs_df=NONE},
		ctl={th=NONE,ks=NONE,
		     abs={th=NONE,ks=NONE,mu={ks=NONE,th=NONE},mth=NONE}},
		abs={th=NONE,ks=NONE,mu={ks=NONE,th=NONE},mth=NONE},
		vm=NONE}

fun get_common (ic:ic) = #common(ic)
fun get_ctl (ic:ic) = #ctl(ic)
fun get_abs (ic:ic) = #abs(ic)
fun get_vm (ic:ic) = #vm(ic)

fun set_common c (ic:ic) ={common=c,ctl= #ctl(ic),abs= #abs(ic),vm =  #vm(ic)}
fun set_vm vm1 (ic:ic) = {common= #common(ic),ctl= #ctl(ic),abs= #abs(ic),vm = SOME vm1}
fun set_abs a (ic:ic) = {common= #common(ic),ctl= #ctl(ic),abs=a,vm= #vm(ic)}
fun set_ctl c (ic:ic) = {common= #common(ic),ctl=c,abs= #abs(ic),vm= #vm(ic)}

end
end

