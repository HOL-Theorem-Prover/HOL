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
(* CONTENTS: Functions which are common to both paried universal and	*)
(*           existential quantifications and which rely on more		*)
(*           primitive functions from all.ml and exi.ml.		*)
(* ---------------------------------------------------------------------*)
(*$Id$*)

(* ------------------------------------------------------------------------- *)
(* Paired stripping tactics, same as basic ones, but they use PGEN_TAC       *)
(* and PCHOOSE_THEN rather than GEN_TAC and CHOOSE_THEN                      *)
(* ------------------------------------------------------------------------- *)

structure Pair_both2 :> Pair_both2 =
struct
	
open HolKernel Parse Drule Conv Tactical Tactic Thm_cont;
    open Pair_syn;
    open Pair_basic;
    open Pair_forall;
    open Pair_exists;

   type term  = Term.term
   type thm   = Thm.thm
   type conv = Abbrev.conv
   type tactic = Abbrev.tactic
   type thm_tactic = Abbrev.thm_tactic
   type thm_tactical = Abbrev.thm_tactical

infix ##;
infix ORELSE;
fun mk_fun(y1,y2) = mk_type{Tyop="fun",Args=[y1,y2]};

	
    
fun PAIR_ERR{function=fnm,message=msg} 
    = raise HOL_ERR{message=msg,origin_function=fnm,
                    origin_structure="pair lib"};
    
fun failwith msg = PAIR_ERR{function=msg,message=""};
	val bool_ty = (==`:bool`==);
    
val PSTRIP_THM_THEN =
    FIRST_TCL [CONJUNCTS_THEN, DISJ_CASES_THEN, PCHOOSE_THEN];

val PSTRIP_ASSUME_TAC =
    (REPEAT_TCL PSTRIP_THM_THEN) CHECK_ASSUME_TAC;

val PSTRUCT_CASES_TAC =
    REPEAT_TCL PSTRIP_THM_THEN
	 (fn th => SUBST1_TAC th  ORELSE  ASSUME_TAC th);

fun PSTRIP_GOAL_THEN ttac = FIRST [PGEN_TAC, CONJ_TAC, DISCH_THEN ttac];

fun FILTER_PSTRIP_THEN ttac tm =
    FIRST [
	FILTER_PGEN_TAC tm,
	FILTER_DISCH_THEN ttac tm,
	CONJ_TAC ];

val PSTRIP_TAC = PSTRIP_GOAL_THEN PSTRIP_ASSUME_TAC;

val FILTER_PSTRIP_TAC = FILTER_PSTRIP_THEN PSTRIP_ASSUME_TAC;

(* ------------------------------------------------------------------------- *)
(*  A |- !p. (f p) = (g p)                                                   *)
(* ------------------------ PEXT                                             *)
(*       A |- f = g                                                          *)
(* ------------------------------------------------------------------------- *)

fun PEXT th =
    let val {Bvar=p,...} = dest_pforall (concl th) 
	val p' = pvariant (thm_free_vars th) p 
	val th1 = PSPEC p' th 
	val th2 = PABS p' th1 
	val th3 = (CONV_RULE (RATOR_CONV (RAND_CONV PETA_CONV))) th2 
    in
	(CONV_RULE (RAND_CONV PETA_CONV)) th3
    end
handle HOL_ERR _ => failwith "PEXT";

(* ------------------------------------------------------------------------- *)
(* P_FUN_EQ_CONV "p" "f = g" = |- (f = g) = (!p. (f p) = (g p))              *)
(* ------------------------------------------------------------------------- *)

val P_FUN_EQ_CONV =
    let val gpty = (==`:'a`==)
	val grange = (==`:'b`==) 
	val gfty = (==`:'a->'b`==) 
	val gf = genvar gfty 
	val gg = genvar gfty 
	val gp = genvar gpty 
	val imp1 = DISCH_ALL (GEN gp (AP_THM (ASSUME (mk_eq{lhs=gf,rhs=gg}))
                                             gp)) 
	val imp2 =
	    DISCH_ALL
	    (EXT (ASSUME (mk_forall{Bvar=gp,
                            Body=mk_eq{lhs=mk_comb{Rator=gf,Rand=gp},
				       rhs=mk_comb{Rator=gg,Rand=gp}}})))
	val ext_thm = (IMP_ANTISYM_RULE imp1 imp2)
    in
	fn p =>
	fn tm =>
	let val {lhs=f,rhs=g} = dest_eq tm 
	    val fty = type_of f 
	    and pty = type_of p 
	    val gfinst = mk_var{Name=(#Name o dest_var)gf,Ty=fty}
	    and gginst = mk_var{Name=(#Name o dest_var)gg,Ty=fty}
	    val rnge = hd (tl(#Args(dest_type fty)))
	    val th =
		INST_TY_TERM
		    ([{residue=f,redex=gfinst},{residue=g,redex=gginst}],
		     [{residue=pty,redex=gpty},{residue=rnge,redex=grange}])
		    ext_thm
	in
	    (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV p)))) th 
	end
    end;


(* ------------------------------------------------------------------------- *)
(*      A |- !p. t = u                                                       *)
(* ------------------------ MK_PABS                                          *)
(*  A |- (\p. t) = (\p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun MK_PABS th =
    let val {Bvar=p,...} = dest_pforall (concl th) 
	val th1 = (CONV_RULE (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
						   (UNPBETA_CONV p)))))) th 
	val th2 = (CONV_RULE (RAND_CONV (PABS_CONV (RAND_CONV
					(UNPBETA_CONV p))))) th1 
	val th3 = PEXT th2 
	val th4 = (CONV_RULE (RATOR_CONV (RAND_CONV (PALPHA_CONV p)))) th3 
    in
	(CONV_RULE (RAND_CONV (PALPHA_CONV p))) th4
    end
handle HOL_ERR _ => failwith "MK_PABS";

(* ------------------------------------------------------------------------- *)
(*  A |- !p. t p = u                                                         *)
(* ------------------ HALF_MK_PABS                                           *)
(*  A |- t = (\p. u)                                                         *)
(* ------------------------------------------------------------------------- *)

fun HALF_MK_PABS th = 
    let val {Bvar=p,...} = dest_pforall (concl th) 
	val th1 = (CONV_RULE (RAND_CONV (PABS_CONV (RAND_CONV 
						    (UNPBETA_CONV p))))) th 
	val th2 = PEXT th1 
    in 
	(CONV_RULE (RAND_CONV (PALPHA_CONV p))) th2
    end
handle HOL_ERR _ => failwith "HALF_MK_PABS" ;

(* ------------------------------------------------------------------------- *)
(*      A |- !p. t = u                                                       *)
(* ------------------------ MK_PFORALL                                       *)
(*  A |- (!p. t) = (!p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun MK_PFORALL th =
    let val {Bvar=p,...} = dest_pforall (concl th) 
    in
	AP_TERM
	(mk_const{Name="!",
		  Ty=mk_fun(mk_fun(type_of p,bool_ty),bool_ty)})
	(MK_PABS th)
    end
handle HOL_ERR _ => failwith "MK_PFORALL" ;


(* ------------------------------------------------------------------------- *)
(*      A |- !p. t = u                                                       *)
(* ------------------------ MK_PEXISTS                                       *)
(*  A |- (?p. t) = (?p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun MK_PEXISTS th =
    let val {Bvar=p,...} = dest_pforall (concl th) 
    in
	AP_TERM
	(mk_const{Name="?",
		  Ty=mk_fun(mk_fun(type_of p, bool_ty), bool_ty)})
	(MK_PABS th)
    end
handle HOL_ERR _ => failwith "MK_PEXISTS" ;

(* ------------------------------------------------------------------------- *)
(*      A |- !p. t = u                                                       *)
(* ------------------------ MK_PSELECT                                       *)
(*  A |- (@p. t) = (@p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun MK_PSELECT th =
    let val {Bvar=p,...} = dest_pforall (concl th) 
	val pty = type_of p 
    in
	AP_TERM
	(mk_const{Name="@",
		  Ty=mk_fun(mk_fun(pty, bool_ty), pty)})
	(MK_PABS th)
    end
handle HOL_ERR _ => failwith "MK_PSELECT" ;

(* ------------------------------------------------------------------------- *)
(*       A |- t = u                                                          *)
(* ------------------------ PFORALL_EQ "p"                                   *)
(*  A |- (!p. t) = (!p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun PFORALL_EQ p th =
   let val pty = type_of p 
   in
       AP_TERM
       (mk_const{Name="!",
		 Ty=mk_fun(mk_fun(pty, bool_ty), bool_ty)})
       (PABS p th)
   end
handle HOL_ERR _ => failwith "PFORALL_EQ" ;

(* ------------------------------------------------------------------------- *)
(*       A |- t = u                                                          *)
(* ------------------------ PEXISTS_EQ "p"                                   *)
(*  A |- (?p. t) = (?p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_EQ p th =
    let val pty = type_of p 
    in
	AP_TERM
	(mk_const{Name="?",
		  Ty=mk_fun(mk_fun(pty, bool_ty), bool_ty)})
	(PABS p th)
    end 
handle HOL_ERR _ => failwith "PEXISTS_EQ" ;

(* ------------------------------------------------------------------------- *)
(*       A |- t = u                                                          *)
(* ------------------------ PSELECT_EQ "p"                                   *)
(*  A |- (@p. t) = (@p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun PSELECT_EQ p th =
    let val pty = type_of p 
    in
	AP_TERM
	(mk_const{Name="@",
		  Ty=mk_fun(mk_fun(pty, bool_ty ), pty)})
	(PABS p th)
    end
handle HOL_ERR _ => failwith "PSELECT_EQ" ;

(* ------------------------------------------------------------------------- *)
(*                A |- t = u                                                 *)
(* ---------------------------------------- LIST_MK_PFORALL [p1;...pn]       *)
(*  A |- (!p1 ... pn. t) = (!p1 ... pn. u)                                   *)
(* ------------------------------------------------------------------------- *)

val LIST_MK_PFORALL = itlist PFORALL_EQ ;

(* ------------------------------------------------------------------------- *)
(*                A |- t = u                                                 *)
(* ---------------------------------------- LIST_MK_PEXISTS [p1;...pn]       *)
(*  A |- (?p1 ... pn. t) = (?p1 ... pn. u)                                   *)
(* ------------------------------------------------------------------------- *)

val LIST_MK_PEXISTS = itlist PEXISTS_EQ ;
		
(* ------------------------------------------------------------------------- *)
(*         A |- P ==> Q                                                      *)
(* -------------------------- EXISTS_IMP "p"                                 *)
(*  A |- (?p. P) ==> (?p. Q)                                                 *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_IMP p th =
    let val {ant=a,conseq=c} = dest_imp (concl th) 
	val th1 = PEXISTS (mk_pexists{Bvar=p,Body=c},p) (UNDISCH th) 
	val asm = mk_pexists{Bvar=p,Body=a} 
	val th2 = DISCH asm (PCHOOSE (p, ASSUME asm) th1) 
    in
	(CONV_RULE (RAND_CONV (GEN_PALPHA_CONV p))) th2 
    end
handle HOL_ERR _ => failwith "PEXISTS_IMP";

(* ------------------------------------------------------------------------- *)
(* SWAP_PFORALL_CONV "!p q. t" = (|- (!p q. t) = (!q p. t))                  *)
(* ------------------------------------------------------------------------- *)

fun SWAP_PFORALL_CONV pqt =
    let val {Bvar=p,Body=qt} = dest_pforall pqt 
	val {Bvar=q,Body=t} = dest_pforall qt 
	val p' = genlike p 
	val q' = genlike q 
	val th1 = GEN_PALPHA_CONV p' pqt 
	val th2 = CONV_RULE(RAND_CONV (RAND_CONV 
				       (PABS_CONV (GEN_PALPHA_CONV q')))) th1 
        val t' = (#Body o dest_pforall o #Body o dest_pforall o rhs o concl)th2
	val pqt' = list_mk_pforall([p',q'],t')
        and qpt' = list_mk_pforall([q',p'],t')
	val th3 = IMP_ANTISYM_RULE
	          ((DISCH pqt' o PGENL[q',p'] o PSPECL[p',q'] o ASSUME)pqt')
	          ((DISCH qpt' o PGENL[p',q'] o PSPECL[q',p'] o ASSUME)qpt')
	val th4 = CONV_RULE(RAND_CONV(GEN_PALPHA_CONV q))th3
	val th5 = CONV_RULE(RAND_CONV (RAND_CONV 
				       (PABS_CONV (GEN_PALPHA_CONV p)))) th4
    in
	TRANS th2 th5
    end
handle HOL_ERR _ => failwith "SWAP_PFORALL_CONV";


(* ------------------------------------------------------------------------- *)
(* SWAP_PEXISTS_CONV "?p q. t" = (|- (?p q. t) = (?q p. t))                  *)
(* ------------------------------------------------------------------------- *)

fun SWAP_PEXISTS_CONV xyt =
   let val {Bvar = x,Body = yt} = dest_pexists xyt
       val {Bvar = y, Body = t} = dest_pexists yt
       val xt = mk_pexists {Bvar = x, Body = t}
       val yxt = mk_pexists{Bvar = y, Body = xt}
       val t_thm = ASSUME t
   in
   IMP_ANTISYM_RULE
         (DISCH xyt (PCHOOSE (x,ASSUME xyt) (PCHOOSE (y, (ASSUME yt))
          (PEXISTS (yxt,y) (PEXISTS (xt,x) t_thm)))))
         (DISCH yxt (PCHOOSE (y,ASSUME yxt) (PCHOOSE (x, (ASSUME xt))
         (PEXISTS (xyt,x) (PEXISTS (yt,y) t_thm)))))
   end
handle HOL_ERR _ => failwith "SWAP_PEXISTS_CONV";

(* --------------------------------------------------------------------- *)
(* PART_PMATCH : just like PART_MATCH but doesn't mind leading paird q.s *)
(* --------------------------------------------------------------------- *)

fun PART_PMATCH partfn th =
    let val pth = GPSPEC (GSPEC (GEN_ALL th))  
	val pat = partfn (concl pth) 
	val matchfn = match_term pat 
    in
	fn tm => INST_TY_TERM (matchfn tm) pth
    end;
    

(* --------------------------------------------------------------------- *)
(*  A ?- !v1...vi. t'                                                    *)
(* ================== MATCH_MP_TAC (A' |- !x1...xn. s ==> !y1...tm. t)	 *)
(*  A ?- ?z1...zp. s'                                                    *)
(* where z1, ..., zp are (type instances of) those variables among	 *)
(* x1, ..., xn that do not occur free in t.				 *)
(* --------------------------------------------------------------------- *)

val PMATCH_MP_TAC : thm_tactic =
    let fun efn p (tm,th) = 
	let val ntm = mk_pexists{Bvar=p,Body=tm}
	in
	    (ntm, PCHOOSE (p, ASSUME ntm) th)
	end
    in
	fn thm =>
	let val (tps,{ant,conseq}) = ((I ## dest_imp) o strip_pforall o concl) 
                                     thm
	    handle HOL_ERR _ => PAIR_ERR{function="MATCH_MP_TAC",
				 message="not an implication"}
	    val (cps,con) = strip_forall conseq
	    val th1 = PSPECL cps (UNDISCH (PSPECL tps thm))
	    val eps = filter (fn p => not (occs_in p con)) tps 
	    val th2 = uncurry DISCH (itlist efn eps (ant,th1))
	in
	    fn (A,g) =>
	    let val (gps,gl) = strip_pforall g 
		val ins = match_term con gl 
		    handle HOL_ERR _ => PAIR_ERR{function="PMATCH_MP_TAC",
					 message="no match"}
		val ith = INST_TY_TERM ins th2
		val newg = #ant(dest_imp(concl ith))
		val gth = PGENL gps (UNDISCH ith)
		    handle HOL_ERR _ => PAIR_ERR{function="PMATCH_MP_TAC",
					 message="generalized pair(s)"}
	    in
		([(A,newg)], fn [th] => PROVE_HYP th gth)
	    end
	end
    end;


(* --------------------------------------------------------------------- *)
(*  A1 |- !x1..xn. t1 ==> t2   A2 |- t1'            			*)
(* --------------------------------------  PMATCH_MP			*)
(*        A1 u A2 |- !xa..xk. t2'					*)
(* --------------------------------------------------------------------- *)

fun gen_assoc (keyf,resf)item =
 let fun assc (v::rst) = if (item = keyf v) then resf v else assc rst
       | assc [] = raise PAIR_ERR{function="gen_assoc", message="not found"}
 in
    assc
 end;
   

val PMATCH_MP =
    let fun variants asl [] = []
	  | variants asl (h::t) = 
	    let val h' = variant (asl@(filter (fn e => not (e = h)) t)) h 
	    in
		{residue=h',redex=h}::(variants (h'::asl) t) 
	    end
	fun frev_assoc e2 (l:(''a,''a)subst) = gen_assoc(#redex,#residue)e2 l
	    handle HOL_ERR _ => e2 
    in
	fn ith =>
	let val t = (#ant o dest_imp o snd o strip_pforall o concl) ith
	    handle HOL_ERR _ => PAIR_ERR{function="PMATCH_MP",
				 message="not an implication"}
	in
	    fn th =>
	    let val (B,t') = dest_thm th 
		val ty_inst = snd (match_term t t')
		val ith_ = INST_TYPE ty_inst ith
		val (A_, forall_ps_t_imp_u_) = dest_thm ith_ 
		val (ps_,t_imp_u_) = strip_pforall forall_ps_t_imp_u_ 
		val {ant=t_,conseq=u_} = dest_imp (t_imp_u_) 
		val pvs = free_varsl ps_ 
		val A_vs = free_varsl A_ 
		val B_vs = free_varsl B 
		val tm_inst = fst (match_term t_ t') 
		val (match_vs, unmatch_vs) = partition (C free_in t_) 
                                                       (free_vars u_) 
		val rename = subtract unmatch_vs (subtract A_vs pvs) 
		val new_vs = free_varsl (map (C frev_assoc tm_inst) match_vs) 
		val renaming = variants (new_vs@A_vs@B_vs) rename 
		val (specs,insts) = partition (C mem (free_varsl pvs) o #redex)
		    (renaming@tm_inst) 
		val spec_list = map (subst specs) ps_ 
		val mp_th = MP (PSPECL spec_list (INST insts ith_)) th 
		val gen_ps = (filter (fn p => null (subtract (rip_pair p) 
						             rename)) ps_) 
		val qs = map (subst renaming) gen_ps
	    in
		PGENL qs mp_th
	    end
	end
    end
handle HOL_ERR _ => failwith "PMATCH_MP: can't instantiate theorem";

end;
