(* ---------------------------------------------------------------------*)
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
(* CONTENTS: functions for paired existential quantifications.          *)
(* ---------------------------------------------------------------------*)
(*$Id$*)

structure Pair_exists :> Pair_exists =
struct
open HolKernel Parse Drule Tactical Tactic Conv Thm_cont;
open Let_conv; (* PAIRED_BETA_CONV is in here, not in 0/1. *)

    open Rsyntax;
    open Pair_syn;
    open Pair_basic;
    open Pair_both1;
    open Pair_forall;
infix ##  |->;

   type term  = Term.term
   type thm   = Thm.thm
   type goal  = Abbrev.goal
   type conv  = Abbrev.conv
   type tactic = Abbrev.tactic

val EXISTS_DEF = boolTheory.EXISTS_DEF;
val EXISTS_UNIQUE_DEF = boolTheory.EXISTS_UNIQUE_DEF;

fun mk_fun(y1,y2) = mk_type{Tyop="fun",Args=[y1,y2]};
	
fun PAIR_ERR{function=fnm,message=msg} 
    = raise HOL_ERR{message=msg,origin_function=fnm,
                    origin_structure="pair lib"};
    
fun failwith msg = PAIR_ERR{function=msg,message=""};

val PEXISTS_CONV =
    let val f = (--`f:'a->bool`--)
	val th1 = AP_THM EXISTS_DEF f 
	val th2 = GEN f ((CONV_RULE (RAND_CONV BETA_CONV)) th1) 
    in
	fn tm =>
	let val {Bvar=p,Body=b} = dest_pexists tm 
	    val g = mk_pabs{Bvar=p,Body=b}
	in
	    (CONV_RULE (RAND_CONV PBETA_CONV)) (ISPEC g th2)
	end
    end
handle HOL_ERR _ => failwith "PEXISTS_CONV" ;

(* ------------------------------------------------------------------------- *)
(*    A |- ?p. t[p]                                                          *)
(* ------------------ PSELECT_RULE                                           *)
(*  A |- t[@p .t[p]]                                                         *)
(* ------------------------------------------------------------------------- *)

val PSELECT_RULE = CONV_RULE PEXISTS_CONV ;

(* ------------------------------------------------------------------------- *)
(* PSELECT_CONV "t [@p. t[p]]" = (|- (t [@p. t[p]]) = (?p. t[p]))            *)
(* ------------------------------------------------------------------------- *)

val PSELECT_CONV =
    let fun find_first p tm =
	if p tm then
	    tm
	else if is_abs tm then
	    find_first p (body tm)
	else if is_comb tm then
	    let val {Rator=f,Rand=a} = dest_comb tm 
	    in
		(find_first p f) handle HOL_ERR _ => (find_first p a)
	    end
	else    
	    failwith""
    in
	fn tm =>
	let fun right t = ((is_pselect t) andalso
			   (rhs (concl (PBETA_CONV (mk_comb{Rator=(rand t),
							    Rand=t})))) = tm)
	    val epi = find_first right tm 
	    val {Bvar=p,Body=b} = dest_pselect epi 
	in
	    SYM (PEXISTS_CONV (mk_pexists{Bvar=p,Body=b})) 
	end
    end
handle HOL_ERR _ => failwith "PSELECT_CONV" ;


(* ------------------------------------------------------------------------- *)
(*  A |- t[@p .t[p]]                                                         *)
(* ------------------ PEXISTS_RULE                                           *)
(*    A |- ?p. t[p]                                                          *)
(* ------------------------------------------------------------------------- *)

val PEXISTS_RULE = CONV_RULE PSELECT_CONV ;

(* ------------------------------------------------------------------------- *)
(*    A |- P t                                                               *)
(* -------------- PSELECT_INTRO                                              *)
(*  A |- P($@ P)                                                             *)
(* ------------------------------------------------------------------------- *)

val PSELECT_INTRO = SELECT_INTRO ;

(* ------------------------------------------------------------------------- *)
(*  A1 |- f($@ f)  ,  A2, f p |- t                                           *)
(* -------------------------------- PSELECT_ELIM th1 ("p", th2) [p not free] *)
(*          A1 u A2 |- t                                                     *)
(* ------------------------------------------------------------------------- *)

fun  PSELECT_ELIM th1 (v,th2) =
    let val {Rator=f,Rand=sf} = dest_comb (concl th1)
	val t1 = MP (PSPEC sf (PGEN v (DISCH (mk_comb{Rator=f,Rand=v}) th2))) th1
	val t2 = ALPHA (concl t1) (concl th2) 
    in
	EQ_MP t2 t1
    end
handle HOL_ERR _ => failwith "PSELECT_ELIM" ;

(* ------------------------------------------------------------------------- *)
(*  A |- t[q]                                                                *)
(* ----------------- PEXISTS ("?p. t[p]", "q")                               *)
(*  A |- ?p. t[p]                                                            *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS (fm,tm) th =
    let val {Bvar=p,Body=b} = dest_pexists fm
	val th1 = PBETA_CONV (mk_comb{Rator=mk_pabs{Bvar=p,Body=b},Rand=tm})
	val th2 = EQ_MP (SYM th1) th 
	val th3 = PSELECT_INTRO th2 
	val th4 = AP_THM(INST_TYPE [{residue=type_of p,
				     redex=mk_vartype "'a"}] EXISTS_DEF)
                        (mk_pabs{Bvar=p, Body=b}) 
	val th5 = TRANS th4 (BETA_CONV(rhs(concl th4)))
    in
	EQ_MP (SYM th5) th3
    end
handle HOL_ERR _ => failwith "PEXISTS" ;

(* ------------------------------------------------------------------------- *)
(*  A1 |- ?p. t[p]  ,  A2, t[v] |- u                                         *)
(* ---------------------------------- PCHOOSE (v,th1) th2 [v not free]       *)
(*             A1 u A2 |- u                                                  *)
(* ------------------------------------------------------------------------- *)

val PCHOOSE =
    let val f = (--`f:'a->bool`--)
	val t1 = AP_THM EXISTS_DEF f 
	val t2 = GEN f ((CONV_RULE (RAND_CONV BETA_CONV)) t1) 
    in
        fn (v,th1) =>
	fn th2 =>
	let val p = rand (concl th1) 
	    val th1' = EQ_MP (ISPEC p t2) th1 
	    val u1 = UNDISCH (fst 
                       (EQ_IMP_RULE (PBETA_CONV (mk_comb{Rator=p,Rand=v})))) 
	    val th2' = PROVE_HYP u1 th2 
	in
	    PSELECT_ELIM th1' (v,th2')
	end
    end
handle HOL_ERR _ => failwith "PCHOOSE" ;

fun P_PCHOOSE_THEN v ttac pth :tactic =
    let val {Bvar=p,Body=b} = dest_pexists (concl pth) 
	handle HOL_ERR _ => failwith "P_PCHOOSE_THEN" 
    in
	fn (asl,w) =>
	let val th = itlist ADD_ASSUM (hyp pth)
	                    (ASSUME
			     (rhs(concl(PBETA_CONV
                                 (mk_comb{Rator=mk_pabs{Bvar=p,Body=b},
		                          Rand=v})))))
	    val (gl,prf) = ttac th (asl,w) 
	in
	    (gl, (PCHOOSE (v, pth)) o prf) 
	end
    end;

fun PCHOOSE_THEN ttac pth :tactic =
    let val {Bvar=p,Body=b} = dest_pexists (concl pth) 
	handle HOL_ERR _ => failwith "CHOOSE_THEN" 
    in
	fn (asl,w) =>
	let val q = pvariant ((thm_free_vars pth) @ (free_varsl (w::asl))) p 
	    val th =
		itlist
		    ADD_ASSUM
		    (hyp pth)
		    (ASSUME
	              (rhs (concl
	               (PAIRED_BETA_CONV (mk_comb{Rator=mk_pabs{Bvar=p,Body=b},
			                          Rand=q})))))
	    val (gl,prf) = ttac th (asl,w) 
	in
	    (gl, (PCHOOSE (q, pth)) o prf) 
	end
    end;


fun P_PCHOOSE_TAC p = P_PCHOOSE_THEN p ASSUME_TAC ;

val PCHOOSE_TAC = PCHOOSE_THEN ASSUME_TAC ;

(* ------------------------------------------------------------------------- *)
(*  A ?- ?p. t[p]                                                            *)
(* =============== PEXISTS_TAC "u"                                           *)
(*    A ?- t[u]                                                              *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_TAC v :tactic = fn (a, t) =>
    let val {Bvar=p,Body=b} = dest_pexists t 
    in
	([(a, rhs (concl (PBETA_CONV (mk_comb{Rator=mk_pabs{Bvar=p,Body=b},
                                              Rand=v}))))
         ],
	 fn [th] => PEXISTS (t,v) th)
    end
handle HOL_ERR _ => failwith "PEXISTS_TAC" ;

(* ------------------------------------------------------------------------- *)
(*  |- ?!p. t[p]                                                             *)
(* -------------- PEXISTENCE                                                 *)
(*  |- ?p. t[p]                                                              *)
(* ------------------------------------------------------------------------- *)

fun PEXISTENCE th =
    let val {Bvar=p,Body=b} = dest_pabs (rand (concl th)) 
	val th1 =
	    AP_THM
	    (INST_TYPE [{residue=type_of p,redex=mk_vartype "'a"}]
                       EXISTS_UNIQUE_DEF)
	    (mk_pabs{Bvar=p,Body=b}) 
	val th2 = EQ_MP th1 th 
	val th3 = CONV_RULE BETA_CONV th2 
    in
	CONJUNCT1 th3 
    end
handle HOL_ERR _ => failwith "PEXISTENCE" ;
    
(* ------------------------------------------------------------------------- *)
(* PEXISTS_UNIQUE_CONV "?!p. t[p]" =                                         *)
(*   (|- (?!p. t[p]) = (?p. t[p] /\ !p p'. t[p] /\ t[p'] ==> (p='p)))        *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_UNIQUE_CONV tm =
    let val {Bvar=p,Body=b} = dest_pabs (rand tm) 
	val p' = pvariant (p::(free_vars tm)) p 
	val th1 =
	    AP_THM
	    (INST_TYPE [{residue=type_of p,redex=mk_vartype "'a"}] 
                       EXISTS_UNIQUE_DEF)
	    (mk_pabs{Bvar=p,Body=b}) 
	val th2 = CONV_RULE (RAND_CONV BETA_CONV) th1 
	val th3 = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (ABS_CONV 
				       (GEN_PALPHA_CONV p'))))) th2 
	val th4 = CONV_RULE (RAND_CONV (RAND_CONV (GEN_PALPHA_CONV p))) th3 
	val th5 = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (PABS_CONV
		             (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
			      (RATOR_CONV (RAND_CONV PBETA_CONV)))))))))) th4 
    in
	CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (PABS_CONV
	    (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
	    (RAND_CONV PBETA_CONV))))))))) th5
    end
handle HOL_ERR _ => failwith "PEXISTS_UNIQUE_CONV" ;

(* ------------------------------------------------------------------------- *)
(* P_PSKOLEM_CONV : introduce a skolem function.                             *)
(*                                                                           *)
(*   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                      *)
(*        =                                                                  *)
(*      (?f. !x1...xn. tm[x1,..,xn,f x1 ... xn]                              *)
(*                                                                           *)
(* The first argument is the function f.                                     *)
(* ------------------------------------------------------------------------- *)

local fun BABY_P_PSKOLEM_CONV f =
    if (not(is_pvar f)) then
	PAIR_ERR{function="P_SKOLEM_CONV",
                 message="first argument not a variable"}
    else
	fn tm =>
	let val (xs,{Bvar=y,Body=P}) = (I ## dest_exists) (strip_pforall tm) 
	    val fx = list_mk_comb(f,xs) 
		handle HOL_ERR _ => PAIR_ERR{function="P_SKOLEM_CONV",
			        message="function variable has the wrong type"}
	in
	    if (free_in f tm) then
		PAIR_ERR{function="P_SKOLEM_CONV",
			 message="skolem function free in the input term"}
	    else
		let val pat = mk_exists{Bvar=f,
					Body=(list_mk_pforall
					          (xs,subst [{residue=fx,
							      redex=y}] P))} 
		    val fnc = list_mk_pabs(xs,mk_select{Bvar=y,Body=P}) 
		    val bth = SYM(LIST_PBETA_CONV (list_mk_comb(fnc,xs))) 
		    val thm1 =
			SUBST[y |-> bth] P (SELECT_RULE(PSPECL xs (ASSUME tm)))
		    val imp1 = DISCH tm (EXISTS (pat,fnc) (PGENL xs thm1)) 
		    val thm2 = PSPECL xs (ASSUME (#Body(dest_exists pat))) 
		    val thm3 = PGENL xs (EXISTS (mk_exists{Bvar=y,Body=P},fx) 
                                                thm2)
		    val imp2 = DISCH pat (CHOOSE (f,ASSUME pat) thm3) 
		in
		    IMP_ANTISYM_RULE imp1 imp2
		end
	end
in
    fun P_PSKOLEM_CONV f =
	if (not (is_pvar f)) then
	    PAIR_ERR{function="P_SKOLEM_CONV",
		     message="first argument not a variable pair"}
	else
	    fn tm =>
	    let val (xs,{Bvar=y,Body=P}) = (I##dest_pexists) (strip_pforall tm)
		handle HOL_ERR _ => PAIR_ERR{function="P_SKOLEM_CONV",
				     message="expecting `!x1...xn. ?y.tm`"} 
		val FORALL_CONV =
		     end_itlist
			(curry (op o))
			(map (K (RAND_CONV o PABS_CONV)) xs) 
	    in
		if is_var f then
		    if is_var y then
			BABY_P_PSKOLEM_CONV f tm
		    else (* is_pair y *)
			let val y' = genvar (type_of y) 
			    val tha1 =
				(FORALL_CONV (RAND_CONV (PALPHA_CONV y'))) tm
			in
			    CONV_RULE (RAND_CONV (BABY_P_PSKOLEM_CONV f)) tha1
			end
		else (* is_par f *)
		    let val {fst=f1,snd=f2} = dest_pair f 
			val thb1 = 
			    if is_var y then
				let val (y1',y2') =
				    (genvar ## genvar) (dest_prod (type_of y)) 
				    handle HOL_ERR _ => 
                                     PAIR_ERR{function="P_PSKOLEM_CONV",
			       message="existential variable not of pair type"}
				in
				(FORALL_CONV
				  (RAND_CONV
				   (PALPHA_CONV (mk_pair{fst=y1',snd=y2'}))))tm
				end
			    else
				REFL tm 
			val thb2 =
			    CONV_RULE
			    (RAND_CONV (FORALL_CONV CURRY_EXISTS_CONV))
			    thb1 
			val thb3 = CONV_RULE (RAND_CONV (P_PSKOLEM_CONV f1)) 
                                             thb2 
			val thb4 = CONV_RULE(RAND_CONV
					     (RAND_CONV (PABS_CONV 
							 (P_PSKOLEM_CONV f2))))
                                            thb3
		    in
			CONV_RULE (RAND_CONV UNCURRY_EXISTS_CONV) thb4
		    end
	    end
end;

(* ------------------------------------------------------------------------- *)
(* PSKOLEM_CONV : introduce a skolem function.                               *)
(*                                                                           *)
(*   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                      *)
(*        =                                                                  *)
(*      (?y'. !x1...xn. tm[x1,..,xn,f x1 ... xn]                             *)
(*                                                                           *)
(* Where y' is a primed variant of y not free in the input term.             *)
(* ------------------------------------------------------------------------- *)

val PSKOLEM_CONV =
    let fun mkfn tm tyl =
	if is_var tm then
	    let val {Name=n,Ty=t} = dest_var tm 
	    in
		mk_var{Name=n, Ty=itlist (fn ty1 => fn ty2 =>
				       mk_fun(ty1,ty2)) tyl t}
	    end
	else
	    let val {fst=p1,snd=p2} = dest_pair tm 
	    in
		mk_pair{fst=mkfn p1 tyl, snd=mkfn p2 tyl}
	    end
    in
	fn tm =>
	let val (xs,{Bvar=y,Body=P}) = (I ## dest_pexists) (strip_pforall tm) 
	    val f = mkfn y (map type_of xs) 
	    val f' = pvariant (free_vars tm) f
	in
	    P_PSKOLEM_CONV f' tm 
	end
    end
handle HOL_ERR _ => failwith "PSKOLEM_CONV: expecting `!x1...xn. ?y.tm`";

end;
