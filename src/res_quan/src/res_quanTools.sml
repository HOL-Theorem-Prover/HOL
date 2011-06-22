(* =====================================================================*)
(* FILE: res_rules.ml	    DATE: 1 Aug 92	BY: Wai Wong		*)
(* TRANSLATED	    	    DATE: 28 May 93	BY: Paul Curzon		*)
(* UPDATED                  DATE: 30 Oct 01     BY: Joe Hurd            *)
(* This file contains rules, conversions and tactics supporting		*)
(* restricted quantifiers.   	    					*)
(* =====================================================================*)

(*
*)
structure res_quanTools :> res_quanTools =
struct

open HolKernel Parse Drule Conv Tactic Tactical Thm_cont
     Rewrite boolSyntax res_quanTheory boolTheory simpLib Cond_rewrite;

infix THENR ORELSER ++ ||;


local  (* Fix the grammar used by this file *)
  val ambient_grammars = Parse.current_grammars();
  val _ = Parse.temp_set_grammars boolTheory.bool_grammars
in

val bool_ss = boolSimps.bool_ss;
val op++ = op THEN;
val op|| = op ORELSE;
fun f THENR g = g o f;
fun f ORELSER g = fn x => f x handle HOL_ERR _ => g x;

val ERR = mk_HOL_ERR "res_quanTools";

(* ===================================================================== *)
(* Syntactic operations on restricted quantifications.                   *)
(* These ought to be generalised to all kinds of restrictions,           *)
(* but one thing at a time.                                              *)
(*  (These now all come from boolSyntax.)                                *)
(* --------------------------------------------------------------------- *)



(* ===================================================================== *)
(* Conversions		    	    					 *)
(* --------------------------------------------------------------------- *)

local
  fun RES_QUAN_CONV c tm =
    let
      val b = snd (dest_comb tm)
    in
      (if is_abs b then
         let
           val v = fst (dest_abs b)
         in
           c
           THENC RAND_CONV (ALPHA_CONV v)
           THENC RAND_CONV (ABS_CONV (RAND_CONV BETA_CONV))
         end
       else c) tm
    end;
in
  val RES_FORALL_CONV = RES_QUAN_CONV (REWR_CONV RES_FORALL);
  val RES_EXISTS_CONV = RES_QUAN_CONV (REWR_CONV RES_EXISTS);
  val RES_SELECT_CONV = RES_QUAN_CONV (REWR_CONV RES_SELECT);
end;

val RES_EXISTS_UNIQUE_CONV =
  REWR_CONV RES_EXISTS_UNIQUE THENC
  TRY_CONV
  (LAND_CONV (RAND_CONV (ABS_CONV BETA_CONV)) THENC
   RAND_CONV
   (RAND_CONV
    (ABS_CONV
     (RAND_CONV
      (ABS_CONV
       (LAND_CONV ((LAND_CONV BETA_CONV) THENC (RAND_CONV BETA_CONV))))))));

(* ---------------------------------------------------------------------     *)
(* If conversion c maps term (--`\i.t1`--) to theorem |- (\i.t1) = (\i'.t1'),*)
(* then RF_BODY_CONV c (--`!i :: P. t1`--) returns the theorem               *)
(*     |- (!i :: P. t1) = (!i' :: P. t1')                                    *)
(*                                                                           *)
(* If conversion c maps term (--`t1`--) to the theorem |- t1 = t1',          *)
(* then RF_CONV c (--`!i :: P. t1`--) returns the theorem                    *)
(*     |- (!i :: P. t1) = (!i :: P. t1')                                     *)
(* ---------------------------------------------------------------------     *)

fun BOTH_CONV c = (LAND_CONV c THENC RAND_CONV c);
fun LEFT_THENC_RIGHT c1 c2 = (LAND_CONV c1 THENC RAND_CONV c2);

val RF_BODY_CONV = RAND_CONV;
val RF_PRED_CONV = (RATOR_CONV o RAND_CONV);
val RF_CONV = (RAND_CONV o ABS_CONV);
fun PRED_THENC_BODY c1 c2 =
   (((RATOR_CONV o RAND_CONV) c1) THENC ((RAND_CONV o ABS_CONV) c2));

(* --------------------------------------------------------------------- *)
(* IMP_RES_FORALL_CONV (--`!x. P x ==> t[x]`--)			 *)
(*     |- !x. P x ==> t[x] = !x :: P. t[x]    	    			 *)
(* --------------------------------------------------------------------- *)

val IMP_RES_FORALL_CONV  = (fn tm =>
    let val dthm = res_quanTheory.RES_FORALL
    val (var, a) = dest_forall tm
    val (ante,t) = dest_imp a
    val (pred,v) = dest_comb ante
    in
     if not(var = v)
     then raise ERR "IMP_RES_FORALL_CONV" "term not in the correct form"
     else
       SYM (RIGHT_CONV_RULE ((GEN_ALPHA_CONV var) THENC
                             (ONCE_DEPTH_CONV BETA_CONV))
                            (ISPECL [pred,mk_abs(var,t)] dthm))
    end
     handle HOL_ERR _ =>
        raise ERR "IMP_RES_FORALL_CONV" "")
    :conv;

(* --------------------------------------------------------------------- *)
(* RES_FORALL_AND_CONV (--`!i :: P. t1 /\ t2`--)  =                     *)
(*     |- (!i :: P. t1 /\ t2) = (!i :: P. t1) /\ (!i :: P. t2)           *)
(* --------------------------------------------------------------------- *)

val RES_FORALL_AND_CONV = (fn tm =>
    let val rthm = res_quanTheory.RES_FORALL_CONJ_DIST
    val (var,pred,conj) = dest_res_forall tm
    val (left,right) = dest_conj conj
    val left_pred = mk_abs(var,left)
    val right_pred = mk_abs(var,right)
    val thm = ISPECL [pred, left_pred, right_pred] rthm
    val c = LEFT_THENC_RIGHT
        (RF_CONV(BOTH_CONV BETA_CONV)) (BOTH_CONV(RF_CONV BETA_CONV))
    in
       CONV_RULE c thm
    end
     handle HOL_ERR _ =>
        raise ERR "RES_FORALL_AND_CONV" "")
    :conv;

(* --------------------------------------------------------------------- *)
(* AND_RES_FORALL_CONV (--`(!i :: P. t1) /\ (!i :: P. t2)`--) =         *)
(*     |- (!i :: P. t1) /\ (!i :: P. t2) = (!i :: P. t1 /\ t2)           *)
(* --------------------------------------------------------------------- *)

val AND_RES_FORALL_CONV = (fn tm =>
    let val rthm = res_quanTheory.RES_FORALL_CONJ_DIST
    val conj1 = rand(rator tm) and conj2 = rand tm
    val (var1,pred1,body1) = dest_res_forall conj1
    val (var2,pred2,body2) = dest_res_forall conj2
    val thm = SYM(
        ISPECL[pred1, mk_abs(var1,body1), mk_abs(var2,body2)] rthm)
    val c = LEFT_THENC_RIGHT
        (BOTH_CONV(RF_CONV BETA_CONV)) (RF_CONV(BOTH_CONV BETA_CONV))
    in
      CONV_RULE c thm
    end
     handle HOL_ERR _ =>
        raise ERR "AND_RES_FORALL_CONV" "")
    :conv;

(* --------------------------------------------------------------------- *)
(* RES_FORALL_SWAP_CONV (--`!i :: P. !j :: Q. R`--) =                         *)
(*     |- (!i :: P. !j :: Q. R) = (!j :: Q. !i :: P. R)                  *)
(* --------------------------------------------------------------------- *)

val RES_FORALL_SWAP_CONV = (fn tm =>
    let val rthm = res_quanTheory.RES_FORALL_REORDER
    val (i,P,body) = dest_res_forall tm
    val (j,Q,R) = dest_res_forall body
    val thm1 = ISPECL [P,Q,mk_abs(i, mk_abs(j, R))] rthm
    (* Reduce the two beta-redexes on either side of the equation. *)
    val c1 = RF_CONV(RF_CONV(RATOR_CONV BETA_CONV THENC BETA_CONV))
    val thm2 = CONV_RULE (LAND_CONV c1 THENC RAND_CONV c1) thm1
    (* Rename the bound variables in the quantifications. *)
    val c2 =
        LAND_CONV(RF_CONV(RF_BODY_CONV(ALPHA_CONV j)) THENC
            RF_BODY_CONV(ALPHA_CONV i)) THENC
        RAND_CONV(RF_CONV(RF_BODY_CONV(ALPHA_CONV i)) THENC
            RF_BODY_CONV(ALPHA_CONV j))
    in
     if i=j orelse free_in i Q orelse free_in j P
     then raise ERR "RES_FORALL_SWAP" ""
     else CONV_RULE c2 thm2
    end
     handle HOL_ERR _ =>
        raise ERR "RES_FORALL_SWAP" "")
    :conv;

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
    let val th' = CONV_RULE ((TOP_DEPTH_CONV RES_FORALL_CONV)
        THENC (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)) th
    in
      COND_REWRITE1_CONV thms th' tm
    end):conv;

(* ===================================================================== *)
(* Derived rules    	    	    					 *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Rule to specialize a restricted universal quantification.             *)
(*                                                                       *)
(*    A |- !x :: P. M x                                                  *)
(*   -------------------  RESQ_HALF_SPEC                                 *)
(*    A |- t IN P ==> M [t/x]                                            *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

fun RESQ_HALF_SPEC tm = CONV_RULE RES_FORALL_CONV THENR SPEC tm;

(* --------------------------------------------------------------------- *)
(* Specialize a list of universal quantifiers which may be a mixture	 *)
(* of ordinary or restricted in any order.				 *)
(* --------------------------------------------------------------------- *)

fun GEN_RESQ_HALF_SPECL spec res_spec =
  let
    fun half_specl asms [] th = foldl (uncurry DISCH) th asms
      | half_specl asms (s :: rest) th =
      if is_res_forall (concl th) then
        let
          val th = res_spec s th
          val (a, _) = dest_imp (concl th)
        in
          half_specl (a :: asms) rest (UNDISCH th)
        end
      else if is_forall (concl th) then half_specl asms rest (spec s th)
      else raise ERR "GEN_RESQ_HALF_SPECL" "not a universal quantifier"
  in
    half_specl []
  end;

val RESQ_HALF_SPECL = GEN_RESQ_HALF_SPECL SPEC RESQ_HALF_SPEC;

(* --------------------------------------------------------------------- *)
(* Rule to specialize a possibly restricted universal quantification.    *)
(*                                                                       *)
(*    A |- !x :: P. M x       A |- !x. M x                               *)
(*   -------------------     --------------    RESQ_SPEC ``t``           *)
(*    A, t IN P |- M t          A |- M t                                 *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

fun RESQ_SPEC tm = (RESQ_HALF_SPEC tm THENR UNDISCH) ORELSER SPEC tm;

(* ---------------------------------------------------------------------*)
(* RESQ_SPECL : term list -> thm -> thm					*)
(* An analogy to SPECL as RESQ_SEPC to SPEC.				*)
(* Instatiate a list of possibly restricted universal quantifiers.	*)
(* ---------------------------------------------------------------------*)

val RESQ_SPECL = C (foldl (uncurry RESQ_SPEC));

(* --------------------------------------------------------------------- *)
(* RESQ_MATCH_MP : thm -> thm -> thm  					 *)
(* RESQ_MATCH_MP (|- !x :: P. Q x) (|- t IN P) returns |- Q t  	    	 *)
(* --------------------------------------------------------------------- *)

fun RESQ_MATCH_MP th1 th2 = MATCH_MP (CONV_RULE RES_FORALL_CONV th1) th2;

(* --------------------------------------------------------------------- *)
(* RESQ_REWR_CANON : thm -> thm	    					 *)
(* convert a theorem into a canonical form for COND_REWR_TAC		 *)
(* --------------------------------------------------------------------- *)

val RESQ_REWR_CANON =
    COND_REWR_CANON o (CONV_RULE ((TOP_DEPTH_CONV RES_FORALL_CONV)));

(* ===================================================================== *)
(* Tactics   	    	    	    					*)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Tactic to strip off a restricted existential quantification.          *)
(*                                                                       *)
(*    A ?- ?x :: P. t                                                    *)
(*   ===================  RESQ_EXISTS_TAC (--`x'`--)                     *)
(*    A ?-  x' IN P /\ t                                                 *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

fun RESQ_EXISTS_TAC tm = CONV_TAC RES_EXISTS_CONV ++ EXISTS_TAC tm;

(* --------------------------------------------------------------------- *)
(* Tactic to strip off a restricted universal quantification.            *)
(* User supplies a thm tactic for the x IN P theorem that results.       *)
(* --------------------------------------------------------------------- *)

fun RESQ_GEN_THEN ttac =
  CONV_TAC RES_FORALL_CONV ++ GEN_TAC ++ DISCH_THEN ttac;

(* --------------------------------------------------------------------- *)
(* A restricted quantification version of STRIP_TAC.                     *)
(* --------------------------------------------------------------------- *)

fun RESQ_HALF_EXISTS_THEN (ttac : thm_tactic) =
  ttac o CONV_RULE RES_EXISTS_CONV;

val RESQ_CHOOSE_THEN =
  RESQ_HALF_EXISTS_THEN THEN_TCL CHOOSE_THEN THEN_TCL CONJUNCTS_THEN;

val RESQ_STRIP_THM_THEN = STRIP_THM_THEN ORELSE_TCL RESQ_CHOOSE_THEN;

fun RESQ_STRIP_GOAL_THEN ttac = STRIP_GOAL_THEN ttac || RESQ_GEN_THEN ttac;

val RESQ_STRIP_ASSUME_TAC = REPEAT_TCL RESQ_STRIP_THM_THEN CHECK_ASSUME_TAC;

val RESQ_STRIP_TAC = RESQ_STRIP_GOAL_THEN RESQ_STRIP_ASSUME_TAC;

(* --------------------------------------------------------------------- *)
(* Tactic to strip off a restricted universal quantification.            *)
(* Uses RESQ_STRIP_ASSUME_TAC to add |- x IN P to the assumptions.       *)
(*                                                                       *)
(*    A ?- !x :: P. t                                                    *)
(*   ===================  RESQ_GEN_TAC                                   *)
(*    A, x IN P ?- t                                                     *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

val RESQ_GEN_TAC = RESQ_GEN_THEN RESQ_STRIP_ASSUME_TAC;

(* --------------------------------------------------------------------- *)
(* RESOLUTION								*)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* check st l : Fail with st if l is empty, otherwise return l.		*)
(* --------------------------------------------------------------------- *)

local fun check st l = if null l then raise ERR "check" st else l

(* --------------------------------------------------------------------- *)
(* check_res th : Fail if th is not in the form:			*)
(* !x0 ... xn. !y :: P. t   otherwise, it returns the following theorem	*)
(* !x0 ... xn y. P ==> t.    	    					*)
(* --------------------------------------------------------------------- *)

and  check_res th =
    if is_forall (concl th) then
    	GEN_ALL (CONV_RULE RES_FORALL_CONV (SPEC_ALL th))
    else CONV_RULE RES_FORALL_CONV th
      handle _ => raise ERR "check_res" "not restricted forall";
in

(* --------------------------------------------------------------------- *)
(* RESQ_IMP_RES_THEN  : Resolve a restricted quantified theorem against	 *)
(* the assumptions.	    	    					 *)
(* --------------------------------------------------------------------- *)

fun RESQ_IMP_RES_THEN ttac resth =
    let val th = check_res resth
    in IMP_RES_THEN ttac th
    end
    handle HOL_ERR{message = s,...} =>
        raise ERR "RESQ_IMP_RES_THEN" s

(* --------------------------------------------------------------------- *)
(* RESQ_RES_THEN : Resolve all restricted universally quantified 	 *)
(* assumptions against the rest.	    			 	 *)
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
(* Restricted quantifier elimination using the simplifier.               *)
(* --------------------------------------------------------------------- *)

val resq_SS =
  simpLib.SSFRAG
  {name=SOME"resq",
   ac = [], congs = [],
   convs =
   [{conv = K (K RES_FORALL_CONV),
     key = SOME ([], Term `RES_FORALL (p:'a -> bool) m`),
     name = "RES_FORALL_CONV", trace = 2},
    {conv = K (K RES_EXISTS_CONV),
     key = SOME ([], Term `RES_EXISTS (p:'a -> bool) m`),
     name = "RES_EXISTS_CONV", trace = 2},
    {conv = K (K RES_SELECT_CONV),
     key = SOME ([], Term `RES_SELECT (p:'a -> bool) m`),
     name = "RES_SELECT_CONV", trace = 2},
    {conv = K (K RES_EXISTS_UNIQUE_CONV),
     key = SOME ([], Term `RES_EXISTS_UNIQUE (p:'a -> bool) m`),
     name = "RES_EXISTS_UNIQUE_CONV", trace = 2}],
   dprocs = [], filter = NONE, rewrs = []};

val resq_ss = simpLib.++ (bool_ss, resq_SS);

val RESQ_TAC =
  FULL_SIMP_TAC resq_ss [] THEN
  POP_ASSUM_LIST (EVERY o map STRIP_ASSUME_TAC o rev);

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
   let val (t1,t2) = pairSyntax.dest_pair tm
               handle _ => raise ERR "check_varstruct" "bad varstruct"

   val l1 = check_varstruct t1
   val l2 = check_varstruct t2
   in
    if intersect l1 l2 = []
    then l1@l2
    else raise ERR "check_varstruct" "repeated variable in varstruct"
   end;

(* check that tm is a <lhs> where:

   <lhs> ::= <var> | <lhs> <varstruct>

 and that no variables are repeated. Return list of variables.
*)

fun check_lhs tm =
 if is_var tm then [tm] else
 if is_const tm
 then raise ERR "check_lhs" ("attempt to redefine the constant " ^
                             fst (dest_const tm))
 else if not(is_comb tm)
 then raise ERR "check_lhs" "lhs not of form (--`x = ...`--) or (--`f x = ... `--)"
 else
  let val (t1,t2) = dest_comb tm
      val l1 = check_lhs t1
      val l2 = check_varstruct t2
  in
     if intersect l1 l2 = []
     then l1@l2
     else raise ERR "check_lhs" "var used twice"
  end;

(*  if (--`C ... = (...:ty)`--) then  (get_type (--`C ...`--) ty) gives the
   type of C.
*)

fun get_type left rightty =
  if is_var left then rightty
  else get_type (rator left)  (type_of(rand left) --> rightty)
  handle _ => raise ERR "get_type" "bad lhs";

(* ---------------------------------------------------------------------*)
(* RESQ_DEF_EXISTS_RULE `!x1::P1. ... !xn::Pn. 			        *)
(*   C y x1 ... xn z = t[y,x1,...,xn,z]`returns a theorem which is      *)
(* suitable to be used in new_specification				*)
(* If there are free variables in Pi, then Skolem conversion will be 	*)
(* done, so the constant C will become C' m where m is free in Pi.	*)
(* ---------------------------------------------------------------------*)

fun RESQ_DEF_EXISTS_RULE tm =
    let val (gvars,tm') = strip_forall tm
    val (ress,(lh,rh)) = ((I ## dest_eq) o strip_res_forall) tm'
    	handle _ => raise ERR "RESQ_DEF_EXISTS_RULE" "definition not an equation"
    val leftvars = check_lhs lh
    val cty = get_type lh (type_of rh)
    val rightvars = free_vars rh
    val resvars = map fst ress
    val finpred = mk_set (flatten (map (free_vars o snd) ress))
    val pConst = hd leftvars
    val cname = fst(dest_var pConst)
    in
    if not(Lexis.allowed_term_constant cname) then
    	raise ERR "RESQ_DEF_EXISTS_RULE" (cname^" is not allowed as a constant name")
    else if (mem pConst resvars) then
    	raise ERR "RESQ_DEF_EXISTS_RULE" (cname^" is restrict bound")
    else if not(all (fn x => mem x leftvars) resvars) then
    	raise ERR "RESQ_DEF_EXISTS_RULE" "restrict bound var not in lhs"
    else if not(set_eq(intersect
    	(union finpred leftvars) rightvars)rightvars) then
    	raise ERR "RESQ_DEF_EXISTS_RULE" "unbound var in rhs"
    else if mem(hd leftvars)rightvars then
    	raise ERR "RESQ_DEF_EXISTS_RULE" "recursive definitions not allowed"
    else if not(null(subtract (type_vars_in_term rh)
                              (type_vars_in_term pConst))) then
    	raise ERR "RESQ_DEF_EXISTS_RULE"
          (dest_vartype(hd(subtract (type_vars_in_term rh)
           (type_vars_in_term pConst))) ^
           "an unbound type variable in definition")
    else
      let val gl = list_mk_forall (finpred,
                    mk_exists(pConst, list_mk_res_forall
                      (ress, list_mk_forall
                              (subtract(tl leftvars) resvars, mk_eq(lh,rh)))))
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
        raise ERR "RESQ_DEF_EXISTS_RULE" s;

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
  val cname = (fst o dest_var o fst o dest_exists o concl) def_thm
in

  Rsyntax.new_specification {name=name,
                     consts= [{fixity = flag, const_name = cname}],
                     sat_thm = def_thm}
end;

val new_resq_definition =  new_gen_resq_definition NONE;

fun new_infixl_resq_definition (name,tm,fix) =
    new_gen_resq_definition (SOME (Infixl fix)) (name,tm);
fun new_infixr_resq_definition (name,tm,fix) =
    new_gen_resq_definition (SOME (Infixr fix)) (name,tm);

val new_binder_resq_definition =  new_gen_resq_definition (SOME Binder);

(* --------------------------------------------------------------------- *)
(* Some restricted quantifier functions using term quotations            *)
(* --------------------------------------------------------------------- *)

fun Q_RESQ_EXISTS_TAC tm = CONV_TAC RES_EXISTS_CONV ++ Q.EXISTS_TAC tm;
fun Q_RESQ_HALF_SPEC tm = CONV_RULE RES_FORALL_CONV THENR Q.SPEC tm;
val Q_RESQ_HALF_SPECL = GEN_RESQ_HALF_SPECL Q.SPEC Q_RESQ_HALF_SPEC;
fun Q_RESQ_SPEC tm = (Q_RESQ_HALF_SPEC tm THENR UNDISCH) ORELSER Q.SPEC tm;
val Q_RESQ_SPECL = C (foldl (uncurry Q_RESQ_SPEC));
fun Q_RESQ_HALF_ISPEC tm = CONV_RULE RES_FORALL_CONV THENR Q.ISPEC tm;
val Q_RESQ_HALF_ISPECL = GEN_RESQ_HALF_SPECL Q.ISPEC Q_RESQ_HALF_ISPEC;
fun Q_RESQ_ISPEC tm = (Q_RESQ_HALF_ISPEC tm THENR UNDISCH) ORELSER Q.ISPEC tm;
val Q_RESQ_ISPECL = C (foldl (uncurry Q_RESQ_ISPEC));

val _ = Parse.temp_set_grammars ambient_grammars
end ;

end; (* res_quanTools *)
