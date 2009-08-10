structure ctlSyntax =
struct

local

open Globals HolKernel Parse

open bossLib
open pairTheory
open pred_setTheory
open pred_setLib
open stringLib
open listTheory
open simpLib
open pairSyntax
open pairLib
open PrimitiveBddRules
open DerivedBddRules
open Binarymap
open PairRules
open pairTools
open setLemmasTheory
open boolSyntax
open Drule
open Tactical
open Conv
open Rewrite
open Tactic
open bddTools
open stringBinTree
open ctlTheory
open boolTheory
open ksTools
open commonTools

in

val _ = set_trace "notify type variable guesses" 0;
val ksR_tm = ``ctl$kripke_structure_R``
val ksS0_tm = ``ctl$kripke_structure_S0``

val ksSu_tm = ``ctl$kripke_structure_S_fupd``
val ksS0u_tm = ``ctl$kripke_structure_S0_fupd``
val ksRu_tm = ``ctl$kripke_structure_R_fupd``
val ksPu_tm = ``ctl$kripke_structure_P_fupd``
val ksLu_tm = ``ctl$kripke_structure_L_fupd``

infixr 5 C_AND

fun (l C_AND r) = ``C_AND2 (^l) (^r)``

val _ = new_constant("BC_AF",bool-->bool)
val BCAF = mk_const("BC_AF",bool-->bool)
val _ = new_constant("BC_AX",bool-->bool)
val BCAX = mk_const("BC_AX",bool-->bool)
val _ = new_constant("BC_AG",bool-->bool)
val BCAG = mk_const("BC_AG",bool-->bool)
val _ = new_constant("BC_EF",bool-->bool)
val BCEF = mk_const("BC_EF",bool-->bool)
val _ = new_constant("BC_EX",bool-->bool)
val BCEX = mk_const("BC_EX",bool-->bool)
val _ = new_constant("BC_EG",bool-->bool)
val BCEG = mk_const("BC_EG",bool-->bool)

fun list_C_AND l =
if (List.null l) then ``C_BOOL B_TRUE``
else if (List.null (List.tl l)) then (List.hd l)
else (List.hd l) C_AND (list_C_AND (List.tl l))

fun C_OR(l,r) = ``C_OR2 (^l) (^r)``
infixr 5 C_OR

fun list_C_OR l =
if (List.null l) then ``C_BOOL B_FALSE``
else if (List.null (List.tl l)) then (List.hd l)
else (List.hd l) C_OR (list_C_OR (List.tl l))

val C_T = ``C_BOOL B_TRUE``
val C_F = ``C_BOOL B_FALSE``
val C_BPROP_tm = ``ctl$B_PROP``

fun C_NOT tm = ``C_NOT ^tm``

fun C_IMP(l,r) = ``C_IMP2 ^l ^r``
infixr 2 C_IMP;

fun C_AX tm = ``C_AX ^tm``;

fun C_AG tm = ``C_AG ^tm``
fun C_EG tm = ``C_EG ^tm``
fun C_EF tm = ``C_EF ^tm``
fun C_EX tm = ``C_EX ^tm``
fun C_EG tm = ``C_EG ^tm``
fun C_AF tm = ``C_AF ^tm``
fun C_AU(l,r) = ``C_AU(^l,^r)``
infixr 1 C_AU;

fun C_IFF(l,r) = ``C_IFF (^l) (^r)``
infix C_IFF;

fun C_AP state p = ``C_BOOL (B_PROP ^(ksTools.mk_AP state p))``;

val _ = set_trace "notify type variable guesses" 1;

fun get_ctl_prop_type f =  (hd o snd o dest_type o type_of) f

(* return a list of all terms of the form AP p that occur in f *)
fun find_BPROPs f = let val p_ty  = get_ctl_prop_type f
		     val pvar = mk_var("p",p_ty)
		 in find_terms (can (match_term (mk_comb(inst [alpha|-> p_ty] C_BPROP_tm,pvar)))) f end

val get_ctl_S = (rand o rand o rator)
val get_ctl_S0 = (rand o rand o rator o rand)
val get_ctl_R = (rand o rand o rator o rand o rand)
val get_ctl_P = (rand o rand o rator o rand o rand o rand)
val get_ctl_L = (rand o rand o rator o rand o rand o rand o rand)

fun mk_cks s_ty p_ty ks_ty S S0 R P L = (* FIXME: this assumes alpha stands for st_ty etc. This could change if HOL records change *)
let val ksSu = inst [alpha |-> s_ty,beta |-> p_ty] ksSu_tm
    val ksS0u = inst [alpha |-> s_ty,beta |-> p_ty] ksS0u_tm
    val ksRu = inst [alpha |-> s_ty,beta |-> p_ty] ksRu_tm
    val ksPu = inst [alpha |-> p_ty,beta |-> s_ty] ksPu_tm (* FIXME: why are alpha and beta inverted here? *)
    val ksLu = inst [alpha |-> s_ty,beta |-> p_ty] ksLu_tm
    val arb_cks = inst [alpha |-> ks_ty] boolSyntax.arb
in List.foldr (fn ((u,v),ks) => mk_comb(mk_comb (u,mk_comb(inst [alpha |-> type_of v, beta |->type_of v] combinSyntax.K_tm,v)),ks))
	      arb_cks  [(ksSu,S),(ksS0u,S0),(ksRu,R),(ksPu,P),(ksLu,L)] end

fun bool2ctl state p_ty f =
if is_bool_var f  then C_AP state f
else if is_T f    then inst [alpha|->p_ty] C_T
else if is_F f    then inst [alpha|->p_ty] C_F
else if is_neg f  then C_NOT (bool2ctl state p_ty (rand f))
else if is_conj f then (bool2ctl state p_ty (land f)) C_AND (bool2ctl state p_ty (rand f))
else if is_disj f then (bool2ctl state p_ty (land f)) C_OR  (bool2ctl state p_ty (rand f))
else if is_imp f  then (bool2ctl state p_ty (land f)) C_IMP (bool2ctl state p_ty (rand f))
else if is_eq f   then (bool2ctl state p_ty (land f)) C_IFF (bool2ctl state p_ty (rand f))
else if is_cond f then let val (c,a,b) = dest_cond f
		       in ((bool2ctl state p_ty c) C_OR (bool2ctl state p_ty b)) C_AND
			  ((bool2ctl state p_ty (mk_neg c)) C_OR (bool2ctl state p_ty a)) end
else case (fst(dest_const(fst(strip_comb f)))) of
	 "BC_AF" => C_AF (bool2ctl state p_ty (rand f))
       | "BC_AX" => C_AX (bool2ctl state p_ty (rand f))
       | "BC_AG" => C_AG (bool2ctl state p_ty (rand f))
       | "BC_EF" => C_EF (bool2ctl state p_ty (rand f))
       | "BC_EX" => C_EX (bool2ctl state p_ty (rand f))
       | "BC_EG" => C_EG (bool2ctl state p_ty (rand f))
       | _       => failwith ("Unrecognized term passed to ctlSyntax.b2ctl: "^(term_to_string f))


end
end