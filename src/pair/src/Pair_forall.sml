(* --------------------------------------------------------------------- *)
(* 		Copyright (c) Jim Grundy 1992				*)
(*									*)
(* Jim Grundy, hereafter referred to as "the Author', retains the	*)
(* copyright and all other legal rights to the Software contained in	*)
(* this file, hereafter referred to as "the Software'.			*)
(* 									*)
(* The Software is made available free of charge on an "as is' basis.	*)
(* No guarantee, either express or implied, of maintenance, reliability	*)
(* or suitability for any purpose is made by the Author.		*)
(* 									*)
(* The user is granted the right to make personal or internal use	*)
(* of the Software provided that both:					*)
(* 1. The Software is not used for commercial gain.			*)
(* 2. The user shall not hold the Author liable for any consequences	*)
(*    arising from use of the Software.					*)
(* 									*)
(* The user is granted the right to further distribute the Software	*)
(* provided that both:							*)
(* 1. The Software and this statement of rights is not modified.	*)
(* 2. The Software does not form part or the whole of a system 		*)
(*    distributed for commercial gain.					*)
(* 									*)
(* The user is granted the right to modify the Software for personal or	*)
(* internal use provided that all of the following conditions are	*)
(* observed:								*)
(* 1. The user does not distribute the modified software. 		*)
(* 2. The modified software is not used for commercial gain.		*)
(* 3. The Author retains all rights to the modified software.		*)
(*									*)
(* Anyone seeking a licence to use this software for commercial purposes*)
(* is invited to contact the Author.					*)
(* ---------------------------------------------------------------------*)
(* CONTENTS: functions for dealing with paired universal quantification.*)
(* ---------------------------------------------------------------------*)
(*$Id$*)

(* ------------------------------------------------------------------------- *)
(* Paired Specialisation:                                                    *)
(*    A |- !p.t                                                              *)
(*  ------------- PSPEC c [where c is free for p in t]                       *)
(*   A |- t[c/p]                                                             *)
(* ------------------------------------------------------------------------- *)

structure Pair_forall :> Pair_forall =
struct
open HolKernel Parse Drule Tactical Tactic Conv Rewrite;

    open Rsyntax;  
    open Pair_syn;
    open Pair_basic;
    open Pair_both1;
	
infix THEN;
infix ##;

   type term = Term.term
   type thm  = Thm.thm
   type tactic = Abbrev.tactic

val FORALL_DEF = boolTheory.FORALL_DEF;
  
fun PAIR_ERR{function=fnm,message=msg} 
    = raise HOL_ERR{message=msg,origin_function=fnm,
                    origin_structure="pair lib"};
    
fun failwith msg = PAIR_ERR{function=msg,message=""};

val PSPEC =
    let val spec_thm =
	prove
	(
	    --`!(x:'a) f. $!f ==> (f x)`--
	,
	    GEN_TAC THEN
	    GEN_TAC THEN
	    (PURE_ONCE_REWRITE_TAC [FORALL_DEF]) THEN
	    BETA_TAC THEN
	    DISCH_TAC THEN
	    (PURE_ASM_REWRITE_TAC []) THEN
	    BETA_TAC
	) 
	val gxty = (==`:'a`==) 
	val gfty = (==`:'a -> bool`==) 
	val gx = genvar gxty 
	val gf = genvar gfty 
	val sth = ISPECL [gx,gf] spec_thm 
    in
	fn x =>
	fn th =>
	let val f = rand (concl th) 
	    val xty = type_of x
	    and fty = type_of f 
	    val gxinst = mk_var{Name=(#Name o dest_var) gx, Ty=xty} 
	    and gfinst = mk_var{Name=(#Name o dest_var) gf, Ty=fty}
	in
	    (CONV_RULE PBETA_CONV)
	    (MP (INST_TY_TERM ([{residue=x,redex=gxinst},
                                {residue=f,redex=gfinst}],
			       [{residue=xty,redex=gxty}]) sth) th)
	end
    end
handle HOL_ERR _ => failwith "PSPEC";

fun PSPECL xl th = rev_itlist PSPEC xl th;

fun IPSPEC x th =
    let val {Bvar=p,Body=tm} = dest_pforall(concl th) 
	handle HOL_ERR _ => PAIR_ERR{function="IPSPEC",
			    message="input theorem not universally quantified"}
	val (_,inst) = match_term p x 
	    handle HOL_ERR _ => PAIR_ERR{function="IPSPEC",
			        message="can't type-instantiate input theorem"}
    in
	PSPEC x (INST_TYPE inst th) 
	handle HOL_ERR _ => PAIR_ERR{function="IPSPEC",
			     message="type variable free in assumptions"}
    end;

val IPSPECL =
    let val tup = end_itlist (fn f => fn s =>mk_pair{fst=f,snd=s})
	fun strip [] = K []
	     | strip (_::ts) = fn t => let val {Bvar,Body} = dest_pforall t
				       in
					   Bvar::(strip ts Body)
				       end
    in
	fn xl =>
	if (null xl) then
	    I
	else
	    let val tupxl = tup xl 
		val striper = strip xl 
	    in
		fn th =>
		let val pl = striper (concl th) 
		    handle HOL_ERR _ => PAIR_ERR{function="IPSPECL",
				 message="list of terms too long for theorem"}
		    val (_,inst) = match_term (tup pl) tupxl 
			handle HOL_ERR _ => PAIR_ERR{function="IPSPECL",
				message="can't type-instantiate input theorem"}
		in
		    PSPECL xl (INST_TYPE inst th) 
		    handle HOL_ERR _ => PAIR_ERR{function="IPSPECL",
				 message="type variable free in assumptions"}
		end
	    end
    end;

					 
fun PSPEC_PAIR th =
    let val {Bvar=p,...} = dest_pforall (concl th) 
	val p' = pvariant (free_varsl (hyp th)) p 
    in
	(p', PSPEC p' th) 
    end;

val PSPEC_ALL =
    let fun f p (ps,l) = 
	let val p' = pvariant ps p 
	in
	    ((free_vars p')@ps,p'::l) 
	end
    in
	fn th =>
	let val (hxs,con) = (free_varsl ## I) (dest_thm th) 
	    val fxs = free_vars con
	    and pairs = fst(strip_pforall con) 
	in
	    PSPECL (snd(itlist f pairs (hxs @ fxs,[]))) th
	end
    end;

fun GPSPEC th =
    let val (_,t) = dest_thm th 
    in
	if is_pforall t then
	    GPSPEC (PSPEC (genlike (#Bvar (dest_pforall t))) th)
	else
	    th
    end;
    

fun PSPEC_TAC (t,x) =
    if (not (is_pair t)) andalso (is_var x) then
	SPEC_TAC (t,x)
    else if (is_pair t) andalso (is_pair x) then
	let val {fst=t1,snd=t2} = dest_pair t 
	    val {fst=x1,snd=x2} = dest_pair x 
	in
	    (PSPEC_TAC (t2,x2)) THEN
	    (PSPEC_TAC (t1,x1)) THEN
	    (CONV_TAC UNCURRY_FORALL_CONV)
	end
    else if (not (is_pair t)) andalso (is_pair x) then
	let val x' = genvar (type_of x) 
	in
	    (SPEC_TAC (t,x')) THEN
	    (CONV_TAC (GEN_PALPHA_CONV x))
	end
    else (* (is_pair t) & (is_var x) *)
	let val {fst,snd} = dest_pair t
	    val x' = mk_pair{fst=genvar(type_of fst),snd=genvar(type_of snd)}
	in
	    (PSPEC_TAC (t,x')) THEN
	    (CONV_TAC (GEN_PALPHA_CONV x))
	end
    handle HOL_ERR _ => failwith "PSPEC_TAC";
		    
(* ------------------------------------------------------------------------- *)
(* Paired Gerneralisation:                                                   *)
(*    A |- t                                                                 *)
(*  ----------- PGEN p [where p is not free in A]                            *)
(*   A |- !p.t                                                               *)
(* ------------------------------------------------------------------------- *)

fun PGEN p th =
    if is_var p then
	GEN p th
    else (* is_pair p *)
	let val {fst=v1, snd=v2} = dest_pair p 
	in
	    CONV_RULE UNCURRY_FORALL_CONV (PGEN v1 (PGEN v2 th))
	end
    handle HOL_ERR _ => failwith "PGEN" ;

fun PGENL xl th = itlist PGEN xl th;;

fun P_PGEN_TAC p :tactic = fn (a,t) =>
    let val {Bvar=x,Body=b} = (dest_pforall t) 
	handle HOL_ERR _ => PAIR_ERR{function="P_PGEN_TAC",
			     message="Goal not universally quantified"}
    in
	if (is_var x) andalso (is_var p) then
	    X_GEN_TAC p (a,t)
	else if (is_pair x) andalso (is_pair p) then
	    let val {fst=p1,snd=p2} = dest_pair p 
	    in
		((CONV_TAC CURRY_FORALL_CONV) THEN
		(P_PGEN_TAC p1) THEN
		(P_PGEN_TAC p2)) (a,t)
	    end
	else if (is_var p) andalso (is_pair x) then
	    let val x' = genvar (type_of p) 
	    in
		((CONV_TAC (GEN_PALPHA_CONV x')) THEN
		 (X_GEN_TAC p)) (a,t)
	    end
	else (*(is_pair p) & (is_var x)*)
	    let val {fst,snd} = dest_pair p
		val x' = mk_pair{fst=genvar(type_of fst),snd=genvar(type_of snd)}
	    in
		((CONV_TAC (GEN_PALPHA_CONV x')) THEN
		(P_PGEN_TAC p)) (a,t)
	    end
    end
handle HOL_ERR _ => failwith "P_PGEN_TAC" ;

val PGEN_TAC : tactic = fn (a,t)  =>
    let val {Bvar=x,Body=b} = (dest_pforall t) 
	handle HOL_ERR _ => PAIR_ERR{function="PGEN_TAC",
			     message="Goal not universally quantified"}
    in
	P_PGEN_TAC (pvariant (free_varsl(t::a)) x) (a,t)
    end;
    
fun FILTER_PGEN_TAC tm : tactic = fn (a,t) =>
    if (is_pforall t) andalso (not (tm = (#Bvar (dest_pforall t)))) then
	PGEN_TAC (a,t)
    else
	failwith "FILTER_PGEN_TAC";
end;
