(* =====================================================================*)
(* FILE: res_rules.ml	    DATE: 1 Aug 92	BY: Wai Wong		*)
(* TRANSLATED	    	    DATE: 28 May 93	BY: Paul Curzon		*)
(* This file contains rules, conversions and tactics supporting		*)
(* restricted quantifiers.   	    					*)
(* =====================================================================*)


structure Res_quan :> Res_quan =
struct


open HolKernel Drule Conv Tactic Tactical Resolve Thm_cont Rewrite;
infix ## THEN THENL THENC;
infixr -->;

 type term     = Term.term
 type thm      = Thm.thm
 type tactic   = Abbrev.tactic
 type conv     = Abbrev.conv
 type thm_tactic = Abbrev.thm_tactic;


fun RES_QUAN_ERR {function,message} =
    HOL_ERR{origin_structure = "Res_quan",
            origin_function = function,
                    message = message};
open Cond_rewrite;

(* ===================================================================== *)
(* Syntactic operations on restricted quantifications.                   *)
(* These ought to be generalised to all kinds of restrictions,           *)
(* but one thing at a time.                                              *)
(* --------------------------------------------------------------------- *)

val (mk_resq_forall,mk_resq_exists,mk_resq_select,mk_resq_abstract) =
 let fun mk_resq_quan cons s (x,t1,t2) =
      let val xty = type_of x
          val t2_ty = type_of t2
          val ty = (xty --> Type.bool) --> (xty --> t2_ty)
                    --> 
                   (if cons="RES_ABSTRACT" then (xty --> t2_ty) else
                    if cons="RES_SELECT"   then xty else Type.bool)
        in
          mk_comb{Rator=mk_comb{Rator=mk_const{Name=cons,Ty=ty},Rand=t1},
                  Rand=mk_abs{Bvar=x,Body=t2}}
        end
        handle _ => raise RES_QUAN_ERR {function="mk_resq_quan",message = s}
    in
    (mk_resq_quan "RES_FORALL"   "mk_resq_forall",
     mk_resq_quan "RES_EXISTS"   "mk_resq_exists",
     mk_resq_quan "RES_SELECT"   "mk_resq_select",
     mk_resq_quan "RES_ABSTRACT" "mk_resq_abstract")
    end;


fun list_mk_resq_forall (ress,body) =
   (itlist (fn (v,p) => fn  b => mk_resq_forall(v,p,b)) ress body)
           handle _ => raise RES_QUAN_ERR {function="list_mk_resq_forall",
                                           message = ""};

fun list_mk_resq_exists (ress,body) =
   (itlist (fn (v,p) => fn  b => mk_resq_exists(v,p,b)) ress body)
           handle _ => raise RES_QUAN_ERR {function="list_mk_resq_exists",
                                           message = ""};

val (dest_resq_forall,dest_resq_exists,dest_resq_select,dest_resq_abstract) =
    let fun dest_resq_quan cons s =
         let val check = assert (fn c => #Name(dest_const c) = cons)
         in
           fn tm => (let val {Rator = op1 ,Rand = rand1} = dest_comb tm
                     val {Rator = op2, Rand = c1} = dest_comb op1
                     val _ = check op2
                     val {Bvar = c2,Body = c3} = dest_abs rand1
                     in
                       (c2,c1,c3)
                     end)
        end
           handle _ => raise RES_QUAN_ERR {function="dest_resq_quan",
                                            message = s}
    in
    (dest_resq_quan "RES_FORALL"   "dest_resq_forall",
     dest_resq_quan "RES_EXISTS"   "dest_resq_exists",
     dest_resq_quan "RES_SELECT"   "dest_resq_select",
     dest_resq_quan "RES_ABSTRACT" "dest_resq_abstract")
    end ;

fun strip_resq_forall fm =
  let val (bv,pred,body) = dest_resq_forall fm
      val (prs, core) = strip_resq_forall body
  in ((bv, pred)::prs, core)
  end
  handle _ => ([],fm);

fun strip_resq_exists fm =
  let val (bv,pred,body) = dest_resq_exists fm
      val (prs, core) = strip_resq_exists body
  in ((bv, pred)::prs, core)
  end
  handle _ => ([],fm);


val is_resq_forall = can dest_resq_forall;
val is_resq_exists = can dest_resq_exists;
val is_resq_select = can dest_resq_select;
val is_resq_abstract = can dest_resq_abstract;


(* ===================================================================== *)
(* Derived rules    	    	    					 *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Rule to strip off a restricted universal quantification.              *)
(*                                                                       *)
(*    A |- !x :: P. t                                                    *)
(*   -------------------  RESQ_SPEC (--`x'`--)                           *)
(*    A, P x' |- t                                                       *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

fun RESQ_SPEC v' th =
    let val dthm = res_quanTheory.RES_FORALL
    in
        let val (v,P,tm) = dest_resq_forall (concl th)
        in
         BETA_RULE (UNDISCH_ALL (ISPEC v'
                    (EQ_MP (ISPECL[P,mk_abs{Bvar=v,Body=tm}] dthm) th)))
        end
    end
    handle HOL_ERR{message = s,...} =>
        raise RES_QUAN_ERR {function="RESQ_SPEC",message = s};

(* ---------------------------------------------------------------------*)
(* RESQ_SPECL : term list -> thm -> thm					*)
(* An analogy to SPECL as RESQ_SEPC to SPEC.				*)
(* Instatiate a list of restricted universal quantifiers.		*)
(* ---------------------------------------------------------------------*)
fun RESQ_SPECL vs th = rev_itlist RESQ_SPEC vs th;

(* ---------------------------------------------------------------------*)
(* RESQ_SPEC_ALL : thm -> thm						*)
(* An analogy to SPEC_ALL as RESQ_SEPC to SPEC.				*)
(* Strip a list of restricted universal quantifiers.			*)
(* ---------------------------------------------------------------------*)
fun RESQ_SPEC_ALL th =
    let val vs = map fst (fst (strip_resq_forall (concl th)))
    in
      rev_itlist RESQ_SPEC vs th
    end;

(* ---------------------------------------------------------------------*)
(* GQSPEC : tm -> thm -> thm						*)
(* Instantiate a universal quantifier which may be either an ordinary	*)
(* or restricted.							*)
(* ---------------------------------------------------------------------*)
fun GQSPEC tm th =
    if (is_resq_forall (concl th))
    then RESQ_SPEC tm th
    else ISPEC tm th;

(* --------------------------------------------------------------------- *)
(* GQSPECL : term list -> thm -> thm					*)
(* Instantiate a list of universal quantifiers which may be a mixture	*)
(* of ordinary or restricted in any order.				*)
(* --------------------------------------------------------------------- *)
fun GQSPECL tms th = rev_itlist GQSPEC tms th;

(* --------------------------------------------------------------------- *)
(* GQSPEC_ALL : thm -> thm						*)
(* Strip a list of universal quantifiers which may be a mixture		*)
(* of ordinary or restricted in any order.				*)
(* --------------------------------------------------------------------- *)
fun GQSPEC_ALL th =
    if (is_resq_forall (concl th))
    then  let val v = #1 (dest_resq_forall (concl th))
          in
    	   GQSPEC_ALL (RESQ_SPEC v th)
          end
    else if (is_forall (concl th))
    then let val v = #Bvar (dest_forall (concl th))
         in
    	  GQSPEC_ALL (SPEC v th)
         end
    else th ;

(* --------------------------------------------------------------------- *)
(* Rule to strip off a restricted universal quantification.              *)
(* but keeping the implication.	    					 *)
(*                                                                       *)
(*    A |- !x :: P. t                                                    *)
(*   -------------------  RESQ_HALF_SPEC                                 *)
(*    A |- !x. P x ==> t                                                 *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)
fun RESQ_HALF_SPEC th =
    let val dthm = res_quanTheory.RES_FORALL
    in
      let val (v,P,tm) = dest_resq_forall (concl th)
      in
         CONV_RULE ((ONCE_DEPTH_CONV BETA_CONV)THENC (GEN_ALPHA_CONV v))
              (EQ_MP (ISPECL[P,mk_abs{Bvar=v,Body=tm}] dthm) th)
      end
    end
    handle HOL_ERR{message = s,...} =>
        raise RES_QUAN_ERR {function="RESQ_HALF_SPEC",message = s};

(* --------------------------------------------------------------------- *)
(* Rule to strip off a restricted existential quantification.            *)
(*                                                                       *)
(*    A |- ?x :: P. t                                                    *)
(*   --------------------- RESQ_HALF_EXISTS                              *)
(*    A |- ?x. P x /\ t[x]                                               *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)
fun RESQ_HALF_EXISTS th =
    let val dthm = res_quanTheory.RES_EXISTS
    in
     let val (v,P,tm) = dest_resq_exists (concl th)
     in
      CONV_RULE ((ONCE_DEPTH_CONV BETA_CONV)THENC (GEN_ALPHA_CONV v))
          (EQ_MP (ISPECL[P,mk_abs{Bvar=v,Body=tm}] dthm) th)
        end
    end
    handle HOL_ERR{message = s,...} =>
        raise RES_QUAN_ERR {function="RESQ_HALF_EXISTS",message = s};


(* --------------------------------------------------------------------- *)
(* Rule to introduce a restricted universal quantification.              *)
(*                                                                       *)
(*    A |- t [x]                                                         *)
(*   ------------------  RESQ_GEN ((--`x`--), (--`P`--))                 *)
(*    A |- !x :: P. t                                                    *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

fun RESQ_GEN (v,P) th =
    let val dthm = res_quanTheory.RES_FORALL
    fun REV_MATCH_EQ_MP th1 th2 = MATCH_MP (snd (EQ_IMP_RULE th1)) th2
    val P' = mk_comb{Rator=P,Rand=v}
    val B' = mk_abs{Bvar=v, Body=concl th}
    val th1 = CONV_RULE (DEPTH_CONV BETA_CONV)(ISPECL[P,B']dthm)
    in
      REV_MATCH_EQ_MP th1 (GEN v
    	(CONV_RULE(DEPTH_CONV BETA_CONV)(DISCH P' th)))
    end
    handle HOL_ERR{message = s,...} =>
        raise RES_QUAN_ERR {function="RESQ_GEN",message = s};

fun RESQ_GENL vps th = itlist RESQ_GEN vps th;

fun RESQ_GEN_ALL th =
    let fun dest_p tm =
        let val {Rator=p,Rand=v} = dest_comb tm
        in
    	   if not(is_var v)
           then raise RES_QUAN_ERR {function="RESQ_GEN_ALL",message = ""}
           else (v,p)
        end
    in
       itlist RESQ_GEN (mapfilter dest_p (hyp th)) th
    end;

(* --------------------------------------------------------------------- *)
(* RESQ_MATCH_MP : thm -> thm -> thm  					*)
(* RESQ_MATCH_MP (|- !x :: P. Q[x]) (|- P x') returns |- Q[x']  	    	*)
(* --------------------------------------------------------------------- *)

fun RESQ_MATCH_MP th1 th2 =
    MATCH_MP (RESQ_HALF_SPEC th1) th2;

(* ===================================================================== *)
(* Tactics   	    	    	    					*)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Tactic to strip off a restricted universal quantification.            *)
(*                                                                       *)
(*    A ?- !x :: P. t                                                    *)
(*   ===================  RESQ_HALF_GEN_TAC                              *)
(*    A ?- !x. P x ==> t                                                 *)
(*                                                                       *)
(*    A ?- !x :: P. t                                                    *)
(*   ===================  RESQ_GEN_TAC                                   *)
(*    A, P x ?- ==> t                                                    *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

val (RESQ_HALF_GEN_TAC:tactic, RESQ_GEN_TAC:tactic) =
    let val RESQ_FORALL = res_quanTheory.RES_FORALL
    fun gtac tac (asl, w) =
       let val (var,cond,body) = dest_resq_forall w
       val thm = RIGHT_CONV_RULE (GEN_ALPHA_CONV var)
                     (ISPECL [cond, mk_abs{Bvar=var,Body=body}] RESQ_FORALL)
       in
          (SUBST1_TAC thm THEN tac) (asl, w)
       end
    in
         ((gtac BETA_TAC), (gtac (GEN_TAC THEN BETA_TAC THEN DISCH_TAC)))
    end;

(* --------------------------------------------------------------------- *)
(* Tactic to strip off a universal quantification which may be either	*)
(* ordinary ore restricted, i.e. a generic version of GEN_TAC and 	*)
(* RESQ_GEN_TAC.            						*)
(* --------------------------------------------------------------------- *)
fun GGEN_TAC (asl,gl) =
    if (is_forall gl)
    then GEN_TAC (asl, gl)
    else if (is_resq_forall gl)
         then (RESQ_GEN_TAC) (asl,gl)
         else raise RES_QUAN_ERR {function="GGEN_TAC",
                  message = "goal is not (restricted) universally quantified"};


(* --------------------------------------------------------------------- *)
(* Tactic to strip off a restricted existential quantification.          *)
(*                                                                       *)
(*    A ?- ?x :: P. t                                                    *)
(*   ===================  RESQ_EXISTS_TAC (--`x'`--)                     *)
(*    A ?-  P x' /\ t                                                    *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

fun RESQ_EXISTS_TAC tm =
   (fn (asl, w) =>
    let val RESQ_EXISTS = res_quanTheory.RES_EXISTS
    val (var,cond,body) = dest_resq_exists w
    val thm = RIGHT_CONV_RULE (GEN_ALPHA_CONV var)
        (ISPECL [cond, mk_abs{Bvar=var,Body=body}] RESQ_EXISTS)
    in
     (SUBST1_TAC thm THEN EXISTS_TAC tm THEN BETA_TAC) (asl, w)
    end):tactic;

(* --------------------------------------------------------------------- *)
(* Resolution using the supplied theorem which contains restricted 	 *)
(* quantifier. This is first converted to an implication then the normal *)
(* resolution tactic is applied.	    				 *)
(* --------------------------------------------------------------------- *)

(*
fun MATCH_MP impth  =
    let val sth = SPEC_ALL impth
    val matchfn = match_term (#conseq(dest_imp(concl sth)))
    in
     fn th =>
       MP (INST_TY_TERM (matchfn (concl th)) sth) th
    end;
*)

(* ===================================================================== *)
(* Conversions		    	    					 *)
(* --------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------     *)
(* If conversion c maps term (--`\i.t1`--) to theorem |- (\i.t1) = (\i'.t1'),*)
(* then RF_BODY_CONV c (--`!i :: P. t1`--) returns the theorem               *)
(*     |- (!i :: P. t1) = (!i' :: P. t1')                                    *)
(*                                                                           *)
(* If conversion c maps term (--`t1`--) to the theorem |- t1 = t1',          *)
(* then RF_CONV c (--`!i :: P. t1`--) returns the theorem                    *)
(*     |- (!i :: P. t1) = (!i :: P. t1')                                     *)
(* ---------------------------------------------------------------------     *)

val LHS_CONV = RATOR_CONV o RAND_CONV;
val RHS_CONV = RAND_CONV;
fun BOTH_CONV c = (LHS_CONV c THENC RHS_CONV c);
fun LEFT_THENC_RIGHT c1 c2 = (LHS_CONV c1 THENC RHS_CONV c2);

val RF_BODY_CONV = RAND_CONV;
val RF_PRED_CONV = (RATOR_CONV o RAND_CONV);
val RF_CONV = (RAND_CONV o ABS_CONV);
fun PRED_THENC_BODY c1 c2 =
   (((RATOR_CONV o RAND_CONV) c1) THENC ((RAND_CONV o ABS_CONV) c2));

(* --------------------------------------------------------------------- *)
(* RESQ_FORALL_CONV (--`!x :: P. t[x]`--)   				 *)
(*     |- !x :: P. t[x] = !x. P x ==> t[x]   	    			 *)
(* --------------------------------------------------------------------- *)

val RESQ_FORALL_CONV = (fn tm =>
    let val dthm = res_quanTheory.RES_FORALL
    val (var,pred,t) = dest_resq_forall tm
    in
       RIGHT_CONV_RULE ((GEN_ALPHA_CONV var) THENC (ONCE_DEPTH_CONV BETA_CONV))
                       (ISPECL [pred,mk_abs{Bvar=var,Body=t}] dthm)
    end
    handle _ =>
        raise RES_QUAN_ERR {function="RESQ_FORALL_CONV",message = ""})
    :conv;

(* --------------------------------------------------------------------- *)
(* LIST_RESQ_FORALL_CONV (--`!x1 :: P1. ... !xn::Pn. t[x1...xn]`--)	 *)
(* |- !x1 :: P1. ... !xn::Pn. t[x1...xn] = 				 *)
(*    !x1...xn. P1 x1 ==> ... ==> Pn xn ==> t[x1...xn]  		 *)
(* --------------------------------------------------------------------- *)

val LIST_RESQ_FORALL_CONV  = (fn tm =>
    RIGHT_CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
    (TOP_DEPTH_CONV RESQ_FORALL_CONV tm)):conv;

(* --------------------------------------------------------------------- *)
(* IMP_RESQ_FORALL_CONV (--`!x. P x ==> t[x]`--)			 *)
(*     |- !x. P x ==> t[x] = !x :: P. t[x]    	    			 *)
(* --------------------------------------------------------------------- *)

val IMP_RESQ_FORALL_CONV  = (fn tm =>
    let val dthm = res_quanTheory.RES_FORALL
    val {Bvar=var, Body=a} = dest_forall tm
    val {ant=ante,conseq=t} = dest_imp a
    val {Rator=pred,Rand=v} = dest_comb ante
    in
     if not(var = v)
     then raise RES_QUAN_ERR {function="IMP_RESQ_FORALL_CONV",
                              message = "term not in the correct form"}
     else
       SYM (RIGHT_CONV_RULE ((GEN_ALPHA_CONV var) THENC
                             (ONCE_DEPTH_CONV BETA_CONV))
                            (ISPECL [pred,mk_abs{Bvar=var,Body=t}] dthm))
    end
     handle HOL_ERR _ =>
        raise RES_QUAN_ERR {function="IMP_RESQ_FORALL_CONV",message = ""})
    :conv;

(* --------------------------------------------------------------------- *)
(* RESQ_FORALL_AND_CONV (--`!i :: P. t1 /\ t2`--)  =                     *)
(*     |- (!i :: P. t1 /\ t2) = (!i :: P. t1) /\ (!i :: P. t2)           *)
(* --------------------------------------------------------------------- *)

val RESQ_FORALL_AND_CONV = (fn tm =>
    let val rthm = res_quanTheory.RESQ_FORALL_CONJ_DIST
    val (var,pred,conj) = dest_resq_forall tm
    val {conj1=left,conj2=right} = dest_conj conj
    val left_pred = mk_abs{Bvar=var,Body=left}
    val right_pred = mk_abs{Bvar=var,Body=right}
    val thm = ISPECL [pred, left_pred, right_pred] rthm
    val c = LEFT_THENC_RIGHT
        (RF_CONV(BOTH_CONV BETA_CONV)) (BOTH_CONV(RF_CONV BETA_CONV))
    in
       CONV_RULE c thm
    end
     handle HOL_ERR _ =>
        raise RES_QUAN_ERR {function="RESQ_FORALL_AND_CONV",message = ""})
    :conv;


(* --------------------------------------------------------------------- *)
(* AND_RESQ_FORALL_CONV (--`(!i :: P. t1) /\ (!i :: P. t2)`--) =         *)
(*     |- (!i :: P. t1) /\ (!i :: P. t2) = (!i :: P. t1 /\ t2)           *)
(* --------------------------------------------------------------------- *)

val AND_RESQ_FORALL_CONV = (fn tm =>
    let val rthm = res_quanTheory.RESQ_FORALL_CONJ_DIST
    val conj1 = rand(rator tm) and conj2 = rand tm
    val (var1,pred1,body1) = dest_resq_forall conj1
    val (var2,pred2,body2) = dest_resq_forall conj2
    val thm = SYM(
        ISPECL[pred1,
               mk_abs{Bvar=var1,Body=body1},
               mk_abs{Bvar=var2,Body=body2}] rthm)
    val c = LEFT_THENC_RIGHT
        (BOTH_CONV(RF_CONV BETA_CONV)) (RF_CONV(BOTH_CONV BETA_CONV))
    in
      CONV_RULE c thm
    end
     handle HOL_ERR _ =>
        raise RES_QUAN_ERR {function="AND_RESQ_FORALL_CONV",message = ""})
    :conv;

(* --------------------------------------------------------------------- *)
(* RESQ_FORALL_SWAP_CONV (--`!i :: P. !j :: Q. R`--) =                         *)
(*     |- (!i :: P. !j :: Q. R) = (!j :: Q. !i :: P. R)                  *)
(* --------------------------------------------------------------------- *)

val RESQ_FORALL_SWAP_CONV = (fn tm =>
    let val rthm = res_quanTheory.RESQ_FORALL_REORDER
    val (i,P,body) = dest_resq_forall tm
    val (j,Q,R) = dest_resq_forall body
    val thm1 = ISPECL [P,Q,mk_abs{Bvar=i, Body=mk_abs{Bvar=j, Body=R}}] rthm
    (* Reduce the two beta-redexes on either side of the equation. *)
    val c1 = RF_CONV(RF_CONV(RATOR_CONV BETA_CONV THENC BETA_CONV))
    val thm2 = CONV_RULE (LHS_CONV c1 THENC RHS_CONV c1) thm1
    (* Rename the bound variables in the quantifications. *)
    val c2 =
        LHS_CONV(RF_CONV(RF_BODY_CONV(ALPHA_CONV j)) THENC
            RF_BODY_CONV(ALPHA_CONV i)) THENC
        RHS_CONV(RF_CONV(RF_BODY_CONV(ALPHA_CONV i)) THENC
            RF_BODY_CONV(ALPHA_CONV j))
    in
     if i=j orelse free_in i Q orelse free_in j P
     then raise RES_QUAN_ERR {function="RESQ_FORALL_SWAP",message = ""}
     else CONV_RULE c2 thm2
    end
     handle HOL_ERR _ =>
        raise RES_QUAN_ERR {function="RESQ_FORALL_SWAP",message = ""})
    :conv;


(* --------------------------------------------------------------------- *)
(* RESQ_EXISTS_CONV (--`?x::P. t`--) --> |- ?x::P. t = ?x. P x /\ t[x]   *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)
val RESQ_EXISTS_CONV = (fn tm' =>
    let val dthm = res_quanTheory.RES_EXISTS
    val (v,P,tm) = dest_resq_exists tm'
    in
     RIGHT_CONV_RULE ((ONCE_DEPTH_CONV BETA_CONV)THENC (GEN_ALPHA_CONV v))
     (ISPECL[P,mk_abs{Bvar=v,Body=tm}] dthm)
    end
     handle HOL_ERR {message = s,...} =>
        raise RES_QUAN_ERR {function="RESQ_EXISTS_CONV",message = s})
    :conv;


(* --------------------------------------------------------------------- *)
(* RESQ_REWR_CANON : thm -> thm	    					 *)
(* convert a theorem into a canonical form for COND_REWR_TAC		 *)
(* --------------------------------------------------------------------- *)

val RESQ_REWR_CANON =
    COND_REWR_CANON o (CONV_RULE ((TOP_DEPTH_CONV RESQ_FORALL_CONV)));


(* --------------------------------------------------------------------- *)
(* RESQ_REWRITE1_TAC : thm_tactic					 *)
(* RESQ_REWRITE1_TAC |- !x::P. u[x] = v[x]				 *)
(* transforms the input restricted quantified theorem to implicative     *)
(* form then do conditional rewriting.					 *)
(* --------------------------------------------------------------------- *)

fun RESQ_REWRITE1_TAC th' =
    let val th = RESQ_REWR_CANON th'
    in
      COND_REWR_TAC search_top_down th
    end;

(* --------------------------------------------------------------------- *)
(* RESQ_REWRITE1_CONV : thm list -> thm -> conv				 *)
(* RESQ_REWRITE1_CONV thms thm tm	    				 *)
(* The input theorem thm should be restricted quantified equational 	 *)
(* theorem ie. the form suitable for RESQ_REWRITE_TAC. The input term tm *)
(* should be an instance of the left-hand side of the conclusion of thm. *)
(* The theorem list thms should contains theorems matching the conditions*)
(* in the input thm. They are used to discharge the conditions. The 	 *)
(* conditions which cannot be discharged by matching theorems will be 	 *)
(* left in the assumption.   	    					 *)
(* --------------------------------------------------------------------- *)
fun RESQ_REWRITE1_CONV thms th =
  (fn  tm =>
    let val th' = CONV_RULE ((TOP_DEPTH_CONV RESQ_FORALL_CONV)
        THENC (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)) th
    in
      COND_REWRITE1_CONV thms th' tm
    end):conv;

(* ===================================================================== *)
(* Functions for making definition with restrict universal quantified	 *)
(* variables.	    	    	    					 *)
(* The auxiliary functions used here are taken from the system directly. *)
(* --------------------------------------------------------------------- *)


(* check that tm is a <varstruct> where:

   <varstruct> ::= <var> | (<varstruct>,...,<varstruct>)

  and that there are no repeated variables. Return list of variables.
*)

fun check_varstruct tm =
  if is_var tm
  then [tm]
  else
   let val {fst=t1,snd=t2} = dest_pair tm
               handle _ => raise RES_QUAN_ERR {function="check_varstruct",
                                               message = "bad varstruct"}

   val l1 = check_varstruct t1
   val l2 = check_varstruct t2
   in
    if intersect l1 l2 = []
    then l1@l2
    else raise RES_QUAN_ERR {function="check_varstruct",
                             message = "repeated variable in varstruct"}
   end;


(* check that tm is a <lhs> where:

   <lhs> ::= <var> | <lhs> <varstruct>

 and that no variables are repeated. Return list of variables.
*)

fun check_lhs tm =
 if is_var tm
 then [tm]
 else if is_const tm
 then raise RES_QUAN_ERR {function="check_lhs",
                          message = "attempt to redefine the constant " ^
                                    (#Name(dest_const tm))}
 else if not(is_comb tm)
 then raise RES_QUAN_ERR {function="check_lhs",
              message ="lhs not of form (--`x = ...`--) or (--`f x = ... `--)"}
 else
  let val {Rator=t1,Rand=t2} = dest_comb tm
  val l1 = check_lhs t1
  val l2 = check_varstruct t2
  in
     if intersect l1 l2 = []
     then l1@l2
     else raise RES_QUAN_ERR {function="check_lhs",
                              message = "var used twice"}
  end;

(*  if (--`C ... = (...:ty)`--) then  (get_type (--`C ...`--) ty) gives the
   type of C.
*)


fun get_type left rightty =
  if is_var left then rightty
  else get_type (rator left)  (Parse.Type`:^(type_of(rand left))->^rightty`)
  handle _ => raise RES_QUAN_ERR {function="get_type",  message = "bad lhs"};

(* ---------------------------------------------------------------------*)
(* RESQ_DEF_EXISTS_RULE `!x1::P1. ... !xn::Pn. 			        *)
(*   C y x1 ... xn z = t[y,x1,...,xn,z]`returns a theorem which is      *)
(* suitable to be used in new_specification				*)
(* If there are free variables in Pi, then Skolem conversion will be 	*)
(* done, so the constant C will become C' m where m is free in Pi.	*)
(* ---------------------------------------------------------------------*)

fun RESQ_DEF_EXISTS_RULE tm =
    let val (gvars,tm') = strip_forall tm
    val (ress,{lhs=lh,rhs=rh}) = ((I ## dest_eq) o strip_resq_forall) tm'
    	handle _ => raise RES_QUAN_ERR {function="RESQ_DEF_EXISTS_RULE",
                                        message = "definition not an equation"}
    val leftvars = check_lhs lh
    val cty = get_type lh (type_of rh)
    val rightvars = free_vars rh
    val resvars = map fst ress
    val finpred = mk_set (flatten (map (free_vars o snd) ress))
    val pConst = hd leftvars
    val cname = #Name(dest_var pConst)
    in
    if not(Lexis.allowed_term_constant cname) then
    	raise RES_QUAN_ERR {function="RESQ_DEF_EXISTS_RULE",
                        message = (cname^" is not allowed as a constant name")}
    else if (mem pConst resvars) then
    	raise RES_QUAN_ERR {function="RESQ_DEF_EXISTS_RULE",
                        message = (cname^" is restrict bound")}
    else if not(all (fn x => mem x leftvars) resvars) then
    	raise RES_QUAN_ERR {function="RESQ_DEF_EXISTS_RULE",
                           message = "restrict bound var not in lhs"}
    else if not(set_eq(intersect
    	(union finpred leftvars) rightvars)rightvars) then
    	raise RES_QUAN_ERR {function="RESQ_DEF_EXISTS_RULE",
                            message = "unbound var in rhs"}
    else if mem(hd leftvars)rightvars then
    	raise RES_QUAN_ERR {function="RESQ_DEF_EXISTS_RULE",
                            message = "recursive definitions not allowed"}
    else if not(null(subtract (type_vars_in_term rh)
                              (type_vars_in_term pConst))) then
    	raise RES_QUAN_ERR {function="RESQ_DEF_EXISTS_RULE",
                           message = (dest_vartype(hd(subtract
                                         (type_vars_in_term rh)
                                         (type_vars_in_term pConst)))^
                                     "an unbound type variable in definition")}
    else
      let val gl =
         list_mk_forall
           (finpred,
            mk_exists
               {Bvar=pConst,
                Body=list_mk_resq_forall
                       (ress,
    	                list_mk_forall
                           ((subtract(tl leftvars) resvars),
                            mk_eq{lhs=lh,rhs=rh}))})
      val ex = list_mk_abs((tl leftvars), rh)
      val defthm = prove(gl,
    	REPEAT GEN_TAC THEN EXISTS_TAC ex THEN BETA_TAC
    	THEN REPEAT RESQ_GEN_TAC THEN REPEAT GEN_TAC THEN REFL_TAC)
      in
       if is_forall(concl defthm)
       then CONV_RULE SKOLEM_CONV defthm
       else defthm
      end
    end
     handle HOL_ERR {message = s,...} =>
        raise RES_QUAN_ERR {function="RESQ_DEF_EXISTS_RULE",message = s};

(* --------------------------------------------------------------------- *)
(* new_gen_resq_definition flag (name, (--`!x1::P1. ... !xn::Pn. 	 *)
(*   C y x1 ... xn z = t[y,x1,...,xn,z]`--))				 *)
(* This makes a new constant definition via new_specification.		 *)
(*  The definition is stored in the current theory under the give name.  *)
(*  flag specifies the syntactic status of the new constant. It should	 *)
(*    be either "constant", or "infix" or "binder".			 *)
(* --------------------------------------------------------------------- *)

open Parse

fun new_gen_resq_definition flag (name, tm) = let
  val def_thm = RESQ_DEF_EXISTS_RULE tm
  val cname = (#Name o dest_var o #Bvar o dest_exists o concl) def_thm
in

  new_specification {name=name,
                     consts= [{fixity = flag, const_name = cname}],
                     sat_thm = def_thm}
end;

val new_resq_definition =  new_gen_resq_definition Prefix;

fun new_infixl_resq_definition (name,tm,fix) =
    new_gen_resq_definition (Infixl fix) (name,tm);
fun new_infixr_resq_definition (name,tm,fix) =
    new_gen_resq_definition (Infixr fix) (name,tm);

val new_binder_resq_definition =  new_gen_resq_definition Binder;

(* --------------------------------------------------------------------- *)
(* RESOLUTION								*)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* check st l : Fail with st if l is empty, otherwise return l.		*)
(* --------------------------------------------------------------------- *)
local fun check st l =
    if null l
    then raise RES_QUAN_ERR {function="check",
                  message = st}
    else l

(* --------------------------------------------------------------------- *)
(* check_res th : Fail if th is not in the form:			*)
(* !x0 ... xn. !y :: P. t   otherwise, it returns the following theorem	*)
(* !x0 ... xn y. P ==> t.    	    					*)
(* --------------------------------------------------------------------- *)

and  check_res th =
    if is_forall (concl th) then
(*        CONV_RULE (ONCE_DEPTH_CONV RESQ_FORALL_CONV) th *)
    	GEN_ALL(RESQ_HALF_SPEC(SPEC_ALL th))
    else (RESQ_HALF_SPEC th)
      handle _ => raise RES_QUAN_ERR {function="check_res",
                          message = "not restricted forall"};
in
(* --------------------------------------------------------------------- *)
(* RESQ_IMP_RES_THEN  : Resolve a restricted quantified theorem against	*)
(* the assumptions.	    	    					*)
(* --------------------------------------------------------------------- *)

fun RESQ_IMP_RES_THEN ttac resth =
    let val th = check_res resth
    in
     IMP_RES_THEN ttac th
    end
    handle HOL_ERR{message = s,...} =>
        raise RES_QUAN_ERR {function="RESQ_IMP_RES_THEN",message = s}

(* --------------------------------------------------------------------- *)
(* RESQ_RES_THEN : Resolve all restricted universally quantified 	*)
(* assumptions against the rest.	    				*)
(* --------------------------------------------------------------------- *)
and RESQ_RES_THEN (ttac:thm_tactic) (asl,g) =
    let val a = map ASSUME asl
    val ths = mapfilter check_res a
    val imps = check "RESQ_RES_THEN: no restricted quantification " ths
    val l = itlist (fn th=>append (mapfilter (MATCH_MP th) a)) imps []
    val res = check "RESQ_RES_THEN: no resolvents " l
    val tacs = check "RESQ_RES_THEN: no tactics" (mapfilter ttac res)
    in
        EVERY tacs (asl,g)
    end
end;

fun RESQ_IMP_RES_TAC th g =
    RESQ_IMP_RES_THEN (REPEAT_GTCL RESQ_IMP_RES_THEN STRIP_ASSUME_TAC) th g
    handle _ => ALL_TAC g;

fun RESQ_RES_TAC g =
    RESQ_RES_THEN (REPEAT_GTCL RESQ_IMP_RES_THEN STRIP_ASSUME_TAC) g
    handle _ => ALL_TAC g;


end; (* Res_quan *)
