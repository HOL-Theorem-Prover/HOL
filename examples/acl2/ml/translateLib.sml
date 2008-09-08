(*****************************************************************************)
(* File: translateLib.sml                                                    *)
(* Author: James Reynolds                                                    *)
(*                                                                           *)
(* Provides tools to assist in proving theorems about translation between    *)
(* s-expressions and native HOL                                              *)
(*****************************************************************************)

open Feedback Lib Type Term boolSyntax Thm Drule Tactical Thm_cont Tactic Conv;

(*****************************************************************************)
(* DOUBLE_MATCH: Like PART_MATCH but matches variables in the term as well   *)
(*****************************************************************************)

local
	val match = mk_HOL_ERR "translateLib" "DOUBLE_MATCH" "Couldn't match terms"

	fun inst_it a b = ((* print_term a ; print " --> " ; print_term b ; print "\n" ; *) inst (match_type (type_of a) (type_of b)))
	
	(* fun subst a = (app (fn {redex,residue} => (print_term redex ; print " |-> " ; print_term residue ; print "\n")) a ; Term.subst a); *)

	(* Matches instantiating free variables to terms if possible, or instantiating t1 |-> t2 if not *)
	fun tmatch (t1,t2) = 
	case (strip_comb t1)
	of (fx,x::xs) => (case (strip_comb t2)
		of (fy,y::ys) => 
			let 	val diff = length (y::ys) - length (x::xs)
				val (fy',ys,fx',xs) = if 0 < diff 	then (list_mk_comb(fy,(List.take(y::ys,diff))),List.drop(y::ys,diff),fx,x::xs)
									else (fy,y::ys,list_mk_comb(fx,(List.take(x::xs,~diff))),List.drop(x::xs,~diff))
			in
				(fn f' => foldl (fn (m,f) => tmatch ((f ## f) m) o f) f' (map (f' ## f') (zip xs ys)))
				(if is_var fx' then 		(subst [inst_it fx' fy' fx' |-> fy'])
				else (if same_const fx' fy' then 	I
				else (if is_var fy' then 	(subst [inst_it fy' fx' fy' |-> fx'] o inst_it fy' fx') else raise match)))
			end
		| (fy,[]) => if is_var fy then subst [inst_it fy t1 fy |-> t1] o inst_it fy t1 else raise match)
	| (fx,[]) => 
		if is_var fx then (subst [inst_it fx t2 fx |-> t2])  else 
			(if same_const fx t2 then I else (if is_var t2 then (subst [inst_it t2 fx t2 |-> fx] o inst_it t2 fx) else raise match))
in
	fun DOUBLE_MATCH opr1 opr2 term thm = 
	let	val t1 = (opr1 o concl o SPEC_ALL) thm
	in	PART_MATCH opr1 (SPEC_ALL thm) (tmatch (opr2 t1,opr2 term) term)
	end
end;


(*****************************************************************************)
(* CHOOSEP: Tactic to choose values if a predicate exists                    *)
(*****************************************************************************)

local
fun snd_to_last_imp term = 
    case (strip_imp term) of ([],a) => a |  (xs,a) => last xs;
fun last_two_imps term =
    case (strip_imp term) of ([],a) => a | (xs,a) => mk_imp(last xs,a);
fun MATCH opr1 opr2 de_thms a =
    tryfind (DOUBLE_MATCH opr1 opr2 a o DISCH_ALL o SPEC_ALL o UNDISCH_ALL) 
    de_thms
	
fun fix_hyps de_thms thm = 
let val hs = mapfilter (fn x => (x,(fn (a,b) => 
    	     (GENL a o MATCH last_two_imps I de_thms) b) (strip_forall x)))
	   (filter is_forall (hyp thm))
in  if null hs then thm else 
       fix_hyps de_thms (foldl (uncurry PROVE_HYP o (snd ## I))
       		(foldl (uncurry INST_TY_TERM) thm
		       (map (uncurry match_term o (I ## concl)) hs)) hs)
end;
val sexp_to_term = rand o lhs o concl
val var = rhs o concl
fun exist L thm = 
let val new_var =
    	if is_var (var thm)
	   then mk_var(prime((fst o dest_var o var) thm),
	   	             (type_of o sexp_to_term) thm)
           else variant (free_varsl L)
	   		(mk_var("x",(type_of o sexp_to_term) thm))
in EXISTS (Psyntax.mk_exists(new_var,
   	subst [sexp_to_term thm |-> new_var] (concl thm)),sexp_to_term thm) thm
end	
in
fun CHOOSEP decode_encode_thms x = 
	DISCH_ALL (fix_hyps decode_encode_thms 
	 (MATCH_MP (
          (DISCH x o UNDISCH_ALL o 
	    MATCH snd_to_last_imp (rator o rand) decode_encode_thms) x)
         (ASSUME x)))
fun CHOOSEP_TAC decode_encode_thms (assums,goal) = 
	MAP_EVERY 
	 (CHOOSE_THEN SUBST_ALL_TAC o GSYM) 
	 (mapfilter (fn x => exist (goal::assums) 
	   (fix_hyps decode_encode_thms
	    (MATCH_MP ((DISCH x o UNDISCH_ALL o MATCH snd_to_last_imp 
	     rand decode_encode_thms) x) (ASSUME x)))) assums)
        (assums,goal)
end;

(*****************************************************************************)
(* DISJ_CASES_UNIONL: Like DISJ_CASES_UNION but with a list                  *)
(*****************************************************************************)

fun DISJ_CASES_UNIONL nchotomy thms = 
let	val concls = map concl thms
	fun make_or (n,t) =
	let	val (pre,post) = (I ## tl) (split_after n concls);
	in	foldl (uncurry DISJ2) (if not (null post) then DISJ1 t (list_mk_disj post) else t) (rev pre)
	end
in
	DISJ_CASESL nchotomy (map make_or (enumerate 0 thms))
end;
	
(*****************************************************************************)
(* Some common destructors / constructors                                    *)
(*****************************************************************************)

fun raise_error a b = raise (mk_HOL_ERR "translateLib" a b)

(* Create and destruct acl2_cond *)
val ite_tm = ``ite``;

fun mk_acl2_cond (p,a,b) = 
	if not (type_of a = ``:sexp`` andalso type_of b = ``:sexp`` andalso type_of p = ``:sexp``) then raise_error "mk_acl2_cond" "Arguments not of type :sexp"
	else mk_comb(mk_comb(mk_comb(ite_tm,p),a),b);

fun dest_acl2_cond term = 
    case strip_comb term
     of (ite,[p,a,b]) =>
         if same_const ite ite_tm
         then (p,a,b)
         else raise_error "dest_acl2_cond" "not an application of \"ite\""
      | _ => raise_error "dest_acl2_cond" "not an application of \"ite\""

fun is_acl2_cond term = 
     case strip_comb term
     of (ite,[p,a,b]) => same_const ite ite_tm | _ => false;


(* Create and destruct acl2_cons *)
val acl2_cons_tm = ``cons``;

fun mk_acl2_cons (a,b) = 
	if not (type_of a = ``:sexp`` andalso type_of b = ``:sexp``) then raise_error "mk_acl2_cons" "Arguments not of type :sexp"
	else mk_comb(mk_comb(acl2_cons_tm,a),b);

fun dest_acl2_cons term = 
	case strip_comb term
		of (acl2_cons,[a,b]) => if same_const acl2_cons acl2_cons_tm then (a,b) else raise_error "dest_acl2_cons" "not an application of \"cons\""
		| _                  => raise_error "dest_acl2_cons" "not an application of \"cons\"";

fun strip_cons term = 
	case (strip_comb term)
		of (a,[l,r]) => if same_const a ``cons`` then (strip_cons l) @ (strip_cons r) else [term]
		 | _         => [term];

(* Create and destruct acl2_true *)
val acl2_true_tm = ``$|=``;

val mk_acl2_true = curry mk_comb acl2_true_tm;

fun dest_acl2_true term = 
	case strip_comb term 
	of (acl2_true,[a]) => if same_const acl2_true acl2_true_tm then a else raise_error "dest_acl2_true" "Not an application of \"|=\""
	| _                => raise_error "dest_acl2_true" "Not an application of \"|=\"";

fun is_acl2_true term = 
	case strip_comb term of (acl2_true,[a]) => same_const acl2_true acl2_true_tm | _ => false;

(*****************************************************************************)
(* RAT_CONG_TAC:                                                             *)
(*                                                                           *)
(* Abbreviates as x = rep_rat (abs_rat (abs_frac (a,b))) and adds the        *)
(* rational equivalence:                                                     *)
(*    |- frac_nmr x * frac_dnm (abs_frac (a,b)) =                            *)
(*	        frac_nmr (abs_frac (a,b)) * frac_dnm x                       *)
(*                                                                           *)
(*****************************************************************************)

val RAT_CONG_TAC = 
	REPEAT (POP_ASSUM MP_TAC) THEN
	REPEAT (Q.PAT_ABBREV_TAC 
	       `x = rep_rat (abs_rat (abs_frac (a''''',b''''')))`) THEN
	REPEAT (DISCH_TAC) THEN
	EVERY_ASSUM (fn th => 
		    (ASSUME_TAC o Rewrite.REWRITE_RULE [ratTheory.RAT] o 
		    		  AP_TERM ``abs_rat``)
		    (Rewrite.REWRITE_RULE [markerTheory.Abbrev_def] th) 
		    handle e => ALL_TAC) THEN
	RULE_ASSUM_TAC (Rewrite.REWRITE_RULE [ratTheory.RAT_EQ]);

(*****************************************************************************)
(* A ?- ?m. P m /\ (m = A) /\ ....                                           *)
(* -------------------------------- EQUAL_EXISTS_TAC                         *)
(*          A ?- P A /\ ....                                                 *)
(*****************************************************************************)

fun EQUAL_EXISTS_TAC (a,g) = 
let val (v,body) = dest_exists g
    val eq_thms = filter is_eq (strip_conj body)
    val term = first (curry op= v o lhs) eq_thms
in 
    EXISTS_TAC (rhs term) (a,g)
end;

(*****************************************************************************)
(* A u {!a b... P ==> !c d ... Q ==> ... ==> X} ?- G                         *)
(* ------------------------------------------------- FIX_CI_TAC              *)
(*   A u {!a b c d ... . P /\ Q /\ ... ==> X} ?- G                           *)
(*                                                                           *)
(* Allows an assumption generated by completeInduct_on to be used by         *)
(* FIRST_ASSUM MATCH_MP_TAC.                                                 *)
(*                                                                           *)
(*****************************************************************************)

val FIX_CI_TAC = 
    RULE_ASSUM_TAC (CONV_RULE (REPEATC (
    		   (STRIP_QUANT_CONV RIGHT_IMP_FORALL_CONV) ORELSEC
		   (STRIP_QUANT_CONV (REWR_CONV boolTheory.AND_IMP_INTRO)))));

