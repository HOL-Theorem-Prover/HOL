(* =====================================================================*)
(* FILE: cond_rewr.sml	    	    					*)
(* AUTHOR: Wai Wong  	DATE: 10 Feb 1993				*)
(* TRANSLATOR: Paul Curzon DATE: 27 May 1993				*)
(* CONDITIONAL REWRITING    	    					*)
(* ---------------------------------------------------------------------*)

structure Cond_rewrite :> Cond_rewrite =
struct

open HolKernel boolLib Rsyntax;

infix ## THEN THENL ORELSEC;

fun COND_REWR_ERR {function,message} =
          HOL_ERR{origin_structure = "Cond_rewrite",
                  origin_function = function,
                  message = message};

val frees = rev o Term.free_vars;

val subtract = op_set_diff aconv
val intersect = op_intersect aconv

fun match_aa tm1 tm2 = [match_term tm1 tm2] handle e => [] ;

fun match_ok vs (l:((term,term) subst * (hol_type,hol_type) subst) list) =
  ((length l) = 1) andalso
   let val subst = hd l
   val tm_subst = fst subst
   val ty_subst = snd subst
   in
     (null ty_subst) andalso
     (let val vlist = (map #redex tm_subst)
      in
      ((set_eq vs vlist) orelse (null vlist))
      end)
   end ;

fun match_aal fvars ante [] = []
 |  match_aal fvars ante (asm::asml) =
      let val ml = match_aa ante asm
      in
       if (match_ok (intersect fvars (frees ante)) ml)
       then [(fst(hd ml), asm)]
       else (match_aal fvars ante asml)
      end ;

fun subset s1 s2 = (* s1 is a subset of s2 *)
    set_eq s2 (union s1 s2);

fun match_asm fvars asm (ml,pl) [] = (ml,pl)
 | match_asm fvars asm (ml,pl) (ante :: antes) =
     let val mlist = match_aal fvars ante asm
     in
      if null mlist then (* no match *)
        (match_asm fvars asm (ml,pl) antes)
      else
       (let val ml' = fst (hd mlist)
        in
        if (subset ml ml')
        then (* found consistant match *)
          (match_asm fvars asm (ml', (ante::pl)) antes)
    	else if (subset ml' ml)
    	then (* found consistant match *)
    	  (match_asm fvars asm (ml, (ante::pl)) antes)
    	else (*  inconsistant match *)
    	  (match_asm fvars asm (ml, pl) antes)
       end)
    end ;

(* ---------------------------------------------------------------------*)
(* MATCH_SUBS1 = -   	    	    					*)
(* : thm ->  ((term # term) list # (type # type) list) list -> term list*)
(*  -> term list -> (term list # thm)	    	    			*)
(* MATCH_SUBS1 th m1 asm fvs = [tm1,...], th'   			*)
(* INPUTS:   	    	    	    					*)
(*  th is the theorem whose instances are required.			*)
(*  m1 is a list indicating an instantiation of th.			*)
(*  asm is a list of terms from which instances of the antecedents of th*)
(*   are found.	    	    	    					*)
(*  fvs is a set fo variables which do not appear in the lhs of the 	*)
(*   conclusion of th.	    	    					*)
(* RETURNS:  	    	    	    					*)
(*  tmi's are instances of the antecedents of th which do not appear in	*)
(*   the assumptions asm	    	    				*)
(*  th' is an instance of th resulting from substituting the matches in	*)
(*   m1 and the matches newly found in the assumption asm.		*)
(* ---------------------------------------------------------------------*)

fun var_cap th fv sv newvs =
  if not(is_forall (concl th))
  then (newvs,th)
  else
   (let val {Bvar=v, Body=b} = dest_forall (concl th)
     val (nv,th') = (I ## (GEN v)) (var_cap (SPEC v th) fv sv newvs)
     in
     if  (mem v fv) then
      if (mem v sv) then
       (let val v' =  (variant (fv @ sv) v)
	    in
	     ((v':: nv), (CONV_RULE (GEN_ALPHA_CONV v') th'))
	    end)
      else ((v :: nv),th')
     else (nv,th')
     end);

fun MATCH_SUBS1 th fvs asm (m1:((term,term)subst * (hol_type,hol_type)subst)) =
    let fun afilter l fvs =
    	   mapfilter (fn (a,a') =>
                          if null(intersect fvs (frees a))
    	                  then raise COND_REWR_ERR{function="MATCH_SUBS1",
                                                   message=""}
                          else a') l
    val subfrees = flatten (map (frees o #residue) (fst m1))
    val thm1 = INST_TYPE (snd m1) th
    val (nv, thm1') = var_cap thm1 fvs subfrees []
    val thm2 = INST (fst m1) (SPEC_ALL thm1')
    val antes = fst(strip_imp (snd (strip_forall(concl thm1'))))
    val antes' = fst(strip_imp(concl thm2))
    in
    if (null fvs)
    then (*not free vars *)
    	((subtract antes' (intersect antes' asm)), (UNDISCH_ALL thm2))
    else let
        val rlist = match_asm nv asm ([],[])
    	                      (afilter (combine(antes, antes')) nv)
        val thm2a = INST (fst rlist) thm2
        val (new_antes, _) = strip_imp (concl thm2a)
    	val thm3 = UNDISCH_ALL thm2a
    	val sgl =  subtract new_antes (intersect new_antes asm)
      in
    	(sgl,thm3)
      end
   end;

fun MATCH_SUBS th fvs asm mlist =
    let val mll = map (MATCH_SUBS1 th fvs asm) mlist
    val (tms,thms) = (flatten ## I) (split mll)
    in
    ((if (null tms) then [] else [list_mk_conj (op_mk_set aconv tms)]), thms)
    end;

(* --------------------------------------------------------------------- *)
(* COND_REWR_TAC = -	    	    					 *)
(* : ((term -> term -> ((term # term) list # (type # type) list) list) ->*)
(*   thm_tactic)	    	    	    				 *)
(* COND_REWR_TAC fn th	    	    					 *)
(* fn is a search function which returns a list of matches in the format *)
(* of the list returned by the system function match.			 *)
(* th is the theorem used for rewriting which should be in the following *)
(* form: |- !x1...xn y1..ym. P1[xi yj] ==> ...==> Pl[xi,yj] ==>		 *)
(*   (Q[x1...xn] = R[xi yj])	    	    				 *)
(* The variables x's appears in the lefthand side of the conclusion, and *)
(* the variables y's do not appear in the lefthand side of the conclusion*)
(* This tactic uses the search function fn to find any matches of Q in 	 *)
(* the goal. It fails of no match is found, otherwise, it does:		 *)
(* 1) instantiating the input theorem (using both the type and the	 *)
(*    matched terms),	    	    					 *)
(* 2) searching the assumptions to find any matches of the antecedents,	 *)
(* 3) if there is any antecedents which does not has match in the 	 *)
(*    assumptions, it is put up as a subgoal and also added to the 	 *)
(*    assumption list of the original goal,				 *)
(* 4) substitutes these instances into the goal. 			 *)
(* Complications: if {yi} is not empty, step 2 will try to find instance *)
(* of Pk and instantiate the y's using these matches.			 *)
(* --------------------------------------------------------------------- *)

fun COND_REWR_TAC f th =
  (fn (asm,gl) =>
    (let val (vars,body) = strip_forall (concl th)
    	val (antes,eqn) = strip_imp body
    	val {lhs=tml, rhs=tmr} = dest_eq eqn
        val freevars = subtract vars (frees tml)
    	val mlist = f tml gl
    	val (sgl,thms) = (MATCH_SUBS th freevars asm mlist)
     in
     if null mlist
     then raise COND_REWR_ERR{function="COND_REWR_TAC", message="no match"}
     else if (null sgl)
     then ((SUBST_TAC thms) (asm,gl))
     else
       ((SUBGOAL_THEN (hd sgl) STRIP_ASSUME_TAC THENL[
         REPEAT CONJ_TAC, SUBST_TAC thms]) (asm,gl))
    end
    handle HOL_ERR {message = message,...} =>
            (raise COND_REWR_ERR {function="COND_REWR_TAC",
                                      message=message})));

(* ---------------------------------------------------------------------*)
(* search_top_down carries out a top-down left-to-right search for 	*)
(* matches of the term tm1 in the term tm2. 				*)
(* ---------------------------------------------------------------------*)

fun search_top_down tm1 tm2 =
    [(match_term tm1 tm2)] handle _ =>
     (if (is_comb tm2)
      then  let val {Rator=rator,Rand=rand} = dest_comb tm2
            in
    	     ((search_top_down tm1 rator) @ (search_top_down tm1 rand))
            end
      else if (is_abs tm2)
      then let val {Bvar=v,Body=body} = dest_abs tm2
            in
    	     search_top_down tm1 body
            end
      else []);

(*---------------------------------------------------------------*)
(* COND_REWR_CANON: thm -> thm	    				 *)
(* converts a theorem to a canonical form for conditional	 *)
(* rewriting. The input theorem should be in the following form: *)
(* !x1 ... xn. P1[xi] ==> ... ==> !y1 ... ym. Pr[xi,yi] ==>	 *)
(* (!z1 ... zk. u[xi,yi,zi] = v[xi,yi,zi])			 *)
(* The output theorem is in the form accepted by COND_REWR_THEN. *)
(* It first moves all universal quantifications to the outermost *)
(* level (possibly doing alpha conversion to avoid making free	 *)
(* variables become bound, then converts any Pj which is itself  *)
(* a conjunction using ANTE_CONJ_CONV repeatedly.		 *)
(*---------------------------------------------------------------*)

fun COND_REWR_CANON th =
    let fun X_CONV conv tm =
        (conv ORELSEC
        (if is_imp tm then RAND_CONV (X_CONV conv) else NO_CONV)) tm
    val rule = CONV_RULE(REPEATC(X_CONV ANTE_CONJ_CONV))
    val th' = CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV) th
    val vars = fst(strip_forall (concl th'))
    in
     (GENL vars (rule(SPEC_ALL th')))
    end;

(*---------------------------------------------------------------*)
(* COND_REWRITE1_TAC : thm_tactic	    			 *)
(*---------------------------------------------------------------*)

val COND_REWRITE1_TAC:thm_tactic = fn  th =>
    COND_REWR_TAC search_top_down (COND_REWR_CANON th);

(* --------------------------------------------------------------------- *)
(* COND_REWR_CONV = 	    	    					 *)
(* : ((term -> term -> ((term # term) list # (type # type) list) list) ->*)
(*   thm -> conv)    	    	    					 *)
(* COND_REWR_CONV fn th tm  	    					 *)
(* th is a theorem in the usual format for conditional rewriting.	 *)
(* tm is a term on which conditinal rewriting is performed. 		 *)
(* fn is a function attempting to match the lhs of the conclusion of th  *)
(* to the input term tm or any subterm(s) of it. The list returned by 	 *)
(* this function is used to instantiate the input theorem. the resulting *)
(* instance(s) are used in a REWRITE_CONV to produce the final theorem.  *)
(* --------------------------------------------------------------------- *)

fun COND_REWR_CONV f th = (fn tm =>
    let val (vars,b) = strip_forall (concl th)
    val tm1 = lhs(snd(strip_imp b))
    val ilist = f tm1 tm
    in
    if (null ilist)
    then raise COND_REWR_ERR{function="COND_REWR_CONV", message="no match"}
    else  let val thm1 = SPEC_ALL th
    	  val rlist = map (fn l => UNDISCH_ALL(INST_TY_TERM l thm1)) ilist
          in
    	    REWRITE_CONV rlist tm
          end
    end
    handle HOL_ERR {message = message,...} =>
            (raise COND_REWR_ERR {function="COND_REWR_CONV",
                                      message=message})):conv;


(* ---------------------------------------------------------------------*)
(* COND_REWRITE1_CONV : thm list -> thm -> conv				*)
(* COND_REWRITE1_CONV thms thm tm	    				*)
(* ---------------------------------------------------------------------*)
fun COND_REWRITE1_CONV thms th = (fn tm =>
    let val thm1 = COND_REWR_CONV search_top_down (COND_REWR_CANON th) tm
    in
     itlist PROVE_HYP thms thm1
    end):conv;

end (* structure Cond_rewrite *)
