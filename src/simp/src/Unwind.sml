(*-------------------------------------------------------------------
 * UNWIND_EXISTS_CONV : conv
 * UNWIND_FORALL_CONV : conv
 *
 * DESCRIPTION
 *
 * UNWIND_EXISTS_CONV eliminates existential 
 * quantifiers where the quantified variable
 * is restricted to a single point via an equality in the
 * conjuncts of the body.  Given a term of the form
 *    ?x1 x2 ... xn. P1[x1..xn] /\ P2[x1..xn] /\ ... /\ Pm[x1..xn]
 * where one of Pk is
 *        "x1 = F[x2...xn]"
 *   or   "F[x2...xn] = x1"
 *   or   "x1"
 *   or   "~x1"
 * UNWIND_EXISTS_CONV eliminates the variable x1 from the existential
 * quantification and converts the term to
 *     ?x2...xn. P1'[x2...xn] /\ ...P(m-1)'[x2...xn]
 * where P1' through Pm-1' have any occurrences of x1 substituted as
 * F[x2...xn].
 *
 * UNWIND_FORALL_CONV eliminates universal
 * quantifiers where the quantified variable
 * is restricted to a single point via an equality in the
 * conjuncts of the body.  Given a term of the form
 *    !x1 x2 ... xn. P1[x1..xn] ==> P2[x1..xn] ==> ... ==> Pm[x1..xn]
 * where one of Pk (k < m) is
 *        "x1 = F[x2...xn]"
 *   or   "F[x2...xn] = x1"
 *   or   "x1"
 *   or   "~x1"
 * UNWIND_FORALL_CONV eliminates the variable x1 from the
 * quantification and converts the term to
 *     !x2...xn. P1'[x2...xn] ==> ...P(m-1)'[x2...xn] ==> Pm[x1..xn]
 * where P1' through Pm-1' have any occurrences of x1 substituted as
 * F[x2...xn], and Pk has been removed.
 *
 * The constraint can also occur within conjuncts of P1, P2 ... P(m-1).
 *
 * USES
 *
 * Eliminating trivial existential and universal quantifiers.
 *
 * EXAMPLES
 *
 * - UNWIND_EXISTS_CONV (--`?inp. inp /\ P inp`--);
 * |- (?inp. inp /\ P inp) = P T : thm
 *
 * - UNWIND_EXISTS_CONV (--`?inp (f:'a->num). (inp = f x)  /\ P f inp`--);
 * |- (?inp f. (inp = f x) /\ P f inp) = (?f. P f (f x)) : thm
 *
 * - UNWIND_EXISTS_CONV (--`?inp. ~inp /\ P inp`--);
 * |- (?inp. ~inp /\ P inp) = P F : thm
 *
 * UNWIND_FORALL_CONV (--`!x. (x = 3) ==> P x`--);
 * UNWIND_FORALL_CONV (--`!x. (x = 3) /\ Q x ==> P x`--);
 * UNWIND_FORALL_CONV (--`!x. (3 = x) /\ Q x ==> P x`--);
 * UNWIND_FORALL_CONV (--`!x. (x < y) ==> (x = 3) /\ Q x ==> P x`--);
 * UNWIND_FORALL_CONV (--`!Q R. (x = 3) /\ Q /\ P x ==> R Q`--);
 * UNWIND_FORALL_CONV (--`!Q R. (x = 3) /\ ~Q /\ P x ==> R Q`--);
 * 
 * TESTING CODE 
 *
 *------------------------------------------------------------------------*)


structure Unwind :> Unwind =
struct

open refuteLib ho_matchLib;
open HolKernel Parse basicHol90Lib Psyntax liteLib;
open Ho_resolve Trace AC Ho_theorems Ho_rewrite;
infix THEN THENC;

  type thm = Thm.thm
  type conv = Abbrev.conv
  type tactic = Abbrev.tactic

fun WRAP_ERR x = STRUCT_WRAP "Unwind" x;


(*-------------------------------------------------------------------
 * find_var_value
 *
 * Given a quantified variable $var$, and a list of possible restricting
 * terms, we return
 * a conjunct from the list of the form $(var = val)$ or $(val = var)$
 * or $var$ or $~var$.
 * If there is no such conjunct, then the function simply fails.  This
 * whole function would be a whole lot easier in Prolog.
 * 
 * It is the [[check_var]] function which actually does the work.  It
 * takes a variable and a conjunct and returns a value for that variable
 * or fails.  
 * 
 *------------------------------------------------------------------------*)

val false_tm = (--`F`--);
val truth_tm = (--`T`--);

fun check_var var conj =
  if is_eq conj then let
    val (arg1, arg2) = dest_eq conj in
      if (mem arg1 (free_vars arg2) orelse 
          mem arg2 (free_vars arg1)) then
         failwith "check_var - Duplicate values" else
      if (arg1 = var) then arg2 else
      if (arg2 = var) then arg1 
      else failwith "check_var - No value" end
  else if is_neg conj andalso dest_neg conj = var then false_tm 
  else if var = conj then truth_tm
  else failwith "check_var - No value";

fun find_var_value var = 
  let fun fvv [] = failwith "find_var_value - No value equality"
        | fvv (c::cs) = (c, check_var var c) handle HOL_ERR _ => fvv cs;
  in fvv
  end

(*-------------------------------------------------------------------
 * MOVE_EXISTS_RIGHT_CONV : conv
 *
 * If we find that a quantified variable does have a value waiting for
 * it, then we need to move it rightwards as far as possible in the
 * string of existentially quantified variables.  To do this, we develop
 * a [[MOVE_RIGHT_CONV]] that performs just this action.  The basic
 * primitive action is that of swapping two variables in the
 * existentially quantified chain, so we also need a proof that allows us
 * that rewrite.  Having swapped the variable in question to the right,
 * we call the same [[conv]] recursively on the body of the quantification.
 *
 * GSPEC's are "temporary" workarounds for a higher-order-matching
 * renaming bug found by Michael Norrish.  DRS Aug 5 1996,
 *------------------------------------------------------------------------*)

val GSWAP_EXISTS_THM = GSPEC SWAP_EXISTS_THM;
val GSWAP_FORALL_THM = GSPEC SWAP_FORALL_THM;

fun MOVE_EXISTS_RIGHT_CONV tm =
  if (is_exists tm) then
    let val (curvar,  subterm) = dest_exists tm in
      if (is_exists subterm) then 
          (REWR_CONV GSWAP_EXISTS_THM THENC 
           (RAND_CONV (ABS_CONV MOVE_EXISTS_RIGHT_CONV))) tm
      else REFL tm
    end
 else failwith "MOVE_EXISTS_RIGHT_CONV";

fun MOVE_FORALL_RIGHT_CONV tm =
  if (is_forall tm) then
    let val (curvar,  subterm) = dest_forall tm in
      if (is_forall subterm) then 
          (REWR_CONV GSWAP_FORALL_THM THENC 
           (RAND_CONV (ABS_CONV MOVE_FORALL_RIGHT_CONV))) tm
      else REFL tm
    end
  else failwith "MOVE_FORALL_RIGHT_CONV";



(*-------------------------------------------------------------------
 * Utils
 *------------------------------------------------------------------------*)

fun split_at f [] = raise failwith"split_at"
  | split_at f (hd::tl) = 
       if (f hd) 
       then ([],hd,tl) 
       else let val (fr,el,back) = split_at f tl
            in (hd::fr,el,back)
             end;

(*-------------------------------------------------------------------
 * CONJ_TO_FRONT_CONV
 *
 * An conjunct nesting is of the form
 *     T1 /\ T2 
 * where each Ti is a conjunct nesting, or a single term T which
 * is not a conjunct.
 *
 * CONJ_TO_FRONT_CONV takes a conjunct nesting and a special conjunct
 * Txx, and converts the conjunct nesting to
 *     Txx /\ T1 /\ T2 /\ ... /\ Tn
 * where T1 ... TN are the conjuncts in the conjunct nesting (apart
 * from Txx).  Thus the conjunct nesting is also flattened.
 *
 * The implementation of this function may eventually be changed to
 * maintain the structure of the nestings T1, T2 etc.
 *
 * EXAMPLES
 * profile CONJ_TO_FRONT_CONV (--`x = 3`--,--`(x = 3)`--);
 * profile CONJ_TO_FRONT_CONV (--`x = 3`--,--`(x = 3) /\ P x`--);
 * profile CONJ_TO_FRONT_CONV (--`x = 3`--,--`(x = 3) /\ P x /\ Q x`--);
 * profile CONJ_TO_FRONT_CONV(--`(P:num->bool) x`--,--`(x = 3)/\P x /\ Q x`--);
 * profile CONJ_TO_FRONT_CONV (--`(Q:num->bool) x`--,--`(x = 3)/\P x/\Q x`--);
 *------------------------------------------------------------------------*)

fun CONJ_TO_FRONT_CONV conj term =
    let val conjs = strip_conj term
        val (front,e,back) = split_at (fn x => conj = x) conjs 
	    handle HOL_ERR _ => failwith "CONJ_TO_FRONT_CONV"
	val rhs = list_mk_conj (e::(front @ back))
    in CONJ_ACI (mk_eq(term,rhs))
    end;


(*-------------------------------------------------------------------
 * IMP_TO_FRONT_CONV
 *
 * An antecedant nesting is of the form
 *     T1 ==> T2 ==> ... ==> C
 * where each Ti is a conjunct nesting.
 *
 * IMP_TO_FRONT_CONV transforms an antecedant nesting into the form
 *    Txx ==> T1a ==> T1b ==> ... ==> T2a ==> ... ==> C
 * where Txx is a special member of one of the conjunct nestings,
 * and T1a..T1x are the members of conjunct nesting T1 (and so on
 * for T2, T3 etc.), excluding Txx which is now at the front.
 *
 * The implementation of this function may eventually be changed to
 * maintain the structure of nestings T1, T2 etc.
 *
 * NOTE 
 *   The implementation of this routine uses REWRITE_TAC.  A more
 * efficient implementation is certainly possible, but gross
 * to code up!!  Please  supply one if you can work out 
 * the fiddly details of the proof strategy.
 *
 * EXAMPLES
 *   profile IMP_TO_FRONT_CONV (--`x = 3`--) (--`(x = 3) ==> P x`--);
 *   profile IMP_TO_FRONT_CONV (--`x = 3`--) (--`(x = 3) /\ Q x ==> P x`--);
 *   profile IMP_TO_FRONT_CONV (--`x = 3`--) (--`(Q x) ==> (x = 3) /\ Q x ==> P x`--);
 *  profile IMP_TO_FRONT_CONV(--`Q:bool`--)(--`(x = 3) /\ Q /\ P x ==> R Q`--);
 *   profile IMP_TO_FRONT_CONV (--`Q:bool`--)(--`(x = 3)/\P x/\Q ==> R Q`--);
 * IMP_CONJ_CANON (mk_thm([],(--`P ==> Q ==> R`--)));
 * IMP_CONJ_CANON (mk_thm([],(--`P /\ Q ==> R`--)));
 * IMP_CONJ_CANON (mk_thm([],(--`P ==> (Q /\ R) ==> Q`--)));

 *------------------------------------------------------------------------*)
(* new version of strip_imp which breaks apart conjuncts in antecedents *)
fun strip_imp' tm = 
    let val (l,r) = Psyntax.dest_imp tm
        val lants = strip_conj l
        val (rants,rest) = strip_imp' r
    in (lants@rants,rest)
    end
    handle HOL_ERR _ => ([],tm);

fun IMP_TO_FRONT_CONV ante tm =
    let val (antes,concl) = strip_imp' tm;
        val (front,e,back) = split_at (fn x => ante = x) antes
	    handle HOL_ERR _ => failwith "IMP_TO_FRONT_CONV"
        val rhs = list_mk_imp (e::(front @ back),concl)
    in
        prove(mk_eq(tm,rhs), 
	      EQ_TAC THEN
	      DISCH_THEN (fn thm => REPEAT 
                            (DISCH_THEN (fn th => 
                  MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN MP_TAC thm) THEN
	      REPEAT (POP_ASSUM (SUBST1_TAC o EQT_INTRO)) THEN REWRITE_TAC [])
    end
handle e as HOL_ERR _ => WRAP_ERR("IMP_TO_FRONT_CONV",e);
    
(*-------------------------------------------------------------------
 * ENSURE_CONJ_CONV
 *   Prove a term is equal to a term which is a conjunct
 * by introduing T if necessary, as in
 *     P = P /\ T
 *------------------------------------------------------------------------*)

val TRUTH_CONJ_INTRO_THM = TAUT(--`!P. P = P /\ T`--);
fun ENSURE_CONJ_CONV tm =
   if (is_conj tm) then REFL tm else SPEC tm TRUTH_CONJ_INTRO_THM;

(*-------------------------------------------------------------------
 * ENSURE_VAR_EQ_CONV
 *   Make a term into an equality with a particular
 * variable on the left in the case it is
 * of the form P (where P is not an equality) or ~P, otherwise
 * leave it alone.
 *    <P>  P -> P = T
 *    <P>  ~P -> P = F
 *    <P>  P = Q -> P = Q
 *    <P>  Q = P -> P = Q
 * ENSURE_EQ_CONV (--`P:bool`--) (--`P:bool`--);
 * ENSURE_EQ_CONV (--`P:bool`--) (--`~P:bool`--);
 * ENSURE_EQ_CONV (--`P:bool`--) (--`P = (Q:bool)`--);
 * ENSURE_EQ_CONV (--`P:bool`--) (--`Q = (P:bool)`--);
 *------------------------------------------------------------------------*)

val EQF_INTRO_THM = TAUT (--`!P. ~P = (P = F)`--);
val EQT_INTRO_THM = TAUT (--`!P. P = (P = T)`--);

fun ENSURE_EQ_CONV var tm =
   if (is_eq tm)
   then if (lhs tm = var) then REFL tm else SYM_CONV tm
   else if is_neg tm
        then SPEC (dest_neg tm) EQF_INTRO_THM
        else SPEC tm EQT_INTRO_THM;


(*-------------------------------------------------------------------
 * LAST_EXISTS_CONV : Apply a conversion to the last existential in
 * a nesting of existential bindings, i.e.
 *    ?x1 x2 x3...xn.  T1
 * conv gets applied to 
 *    ?xn. T1
 *------------------------------------------------------------------------*)

fun LAST_EXISTS_CONV conv tm =
  let val (var,body) = dest_exists tm
  in if (is_exists body) then RAND_CONV (ABS_CONV (LAST_EXISTS_CONV conv)) tm
     else conv tm
  end;

(*-------------------------------------------------------------------
 * LAST_FORALL_CONV : Apply a conversion to the last universal 
 * quantification in a nesting of universal quantifications, i.e.
 *    !x1 x2 x3...xn.  T1
 * conv gets applied to 
 *    !xn. T1
 *------------------------------------------------------------------------*)

fun LAST_FORALL_CONV conv tm =
  let val (var,body) = dest_forall tm
  in if (is_forall body) then RAND_CONV (ABS_CONV (LAST_FORALL_CONV conv)) tm
     else conv tm
  end;

(*-------------------------------------------------------------------
 * ELIM_EXISTS_CONV : 
 *    Eliminate an existential witnessed by an equality somewhere
 * in the conjunct nesting immediately below the existential.
 *
 * EXAMPLES
 *
 * val inp = --`inp:bool`--;
 * - profile (ELIM_EXISTS_CONV (inp,inp)) (--`?inp. inp /\ P inp`--);
 * - profile (ELIM_EXISTS_CONV (inp, --`inp:bool = y`--))
 *           (--`?inp. Q inp /\ (inp:bool = y)  /\ P inp`--);
 * - ELIM_EXISTS_CONV (inp,--`~inp`--) (--`?inp. Q inp /\ ~inp /\ P inp`--);
 *
 * IMPLEMENTATION:
 *    1. Convert the body by:
 *         a. Moving the appropriate conjunct to the front of the conjunct
 *            nesting.
 *         b. Abstract the other conjuncts by the 
 *            appropriate variable.
 *         c. Ensure the conjunct is an equality (P --> (P = T) etc.) with
 *            the variable to eliminate on the left.
 *    2. Now apply ELIM_EXISTS_THM
 *------------------------------------------------------------------------*)

fun ELIM_EXISTS_CONV (var,conj) =
  RAND_CONV (ABS_CONV 
         (CONJ_TO_FRONT_CONV conj THENC ENSURE_CONJ_CONV THENC 
          LAND_CONV (ENSURE_EQ_CONV var)))
  THENC REWR_CONV UNWIND_THM2;

(*-------------------------------------------------------------------
 * ELIM_FORALL_CONV : 
 *    Eliminate an universal witnessed by an equality somewhere
 * in the antecedant nesting immediately below the quantification.
 *
 *
 * EXAMPLES
 *
 * val inp = --`inp:bool`--;
 * - profile (ELIM_FORALL_CONV (inp,inp)) (--`!inp. inp ==> Q inp ==> P inp`--) handle e => Raise e;
 * - profile (ELIM_FORALL_CONV (inp, --`inp:bool = y`--)) (--`!inp. Q inp ==> (inp:bool = y)  ==> P inp`--);
 * - profile (ELIM_FORALL_CONV (inp,--`~inp`--)) (--`!inp. Q inp /\ R inp ==> ~inp ==> P inp`--);
 *
 * IMPLEMENTATION:
 *    1. Convert the body by:
 *         a. Moving the appropriate antecedent to the front of the
 *           antecedent nesting.
 *         b. Abstract the other antecedents and conclusion by the 
 *            appropriate variable.
 *         c. Ensure the antecedent is an equality (P --> (P = T) etc.) with
 *            the variable to eliminate on the left.
 *    2. Now apply ELIM_FORALL_THM
 *------------------------------------------------------------------------*)

fun ELIM_FORALL_CONV (var,conj) =
  RAND_CONV (ABS_CONV 
         (IMP_TO_FRONT_CONV conj THENC LAND_CONV (ENSURE_EQ_CONV var)))
  THENC REWR_CONV UNWIND_FORALL_THM2;


(*-------------------------------------------------------------------
 * UNWIND_EXISTS_CONV
 *
 * Like ELIM_EXISTS_CONV but does variable reordering as well to
 * work on the top quantifier in a sequence of existenial quantifications.
 *------------------------------------------------------------------------*)

fun UNWIND_EXISTS_CONV tm =
  let val (vars, body) = strip_exists tm 
  in if length vars = 0 then failwith "UNWIND_FORALL_CONV: not applicable" else
  let val (conj,value) = find_var_value (hd vars) (strip_conj body) 
      handle HOL_ERR _ => failwith "UNWIND_EXISTS_CONV: can't eliminate"
  in (MOVE_EXISTS_RIGHT_CONV 
      THENC LAST_EXISTS_CONV (ELIM_EXISTS_CONV (hd vars,conj))) tm
  end
  end;

(*------------------------------------------------------------------------
 * UNWIND_EXISTS_TAC
 * UNWIND_EXISTS_RULE
 *
 *------------------------------------------------------------------------*)

val UNWIND_EXISTS_TAC = CONV_TAC (TOP_DEPTH_CONV UNWIND_EXISTS_CONV)
val UNWIND_EXISTS_RULE = CONV_RULE UNWIND_EXISTS_CONV

(*-------------------------------------------------------------------
 * UNWIND_FORALL_CONV
 *
 * Like ELIM_FORALL_CONV but does variable reordering as well to
 * work on any existential in a grouping of existentials.
 * 
 *------------------------------------------------------------------------*)

fun UNWIND_FORALL_CONV tm =
  let val (vars, body) = strip_forall tm 
  in if length vars = 0 then failwith "UNWIND_FORALL_CONV: not applicable" else
  let val (ant,value) = find_var_value (hd vars) (fst(strip_imp' body)) 
      handle HOL_ERR _ => failwith "UNWIND_FORALL_CONV: no value to eliminate"
  in (MOVE_FORALL_RIGHT_CONV 
      THENC LAST_FORALL_CONV (ELIM_FORALL_CONV (hd vars,ant))) tm
  end
  end;

(*------------------------------------------------------------------------
 * UNWIND_FORALL_TAC
 * UNWIND_FORALL_RULE
 *
 *------------------------------------------------------------------------*)

val UNWIND_FORALL_TAC = CONV_TAC (TOP_DEPTH_CONV UNWIND_FORALL_CONV)
val UNWIND_FORALL_RULE = CONV_RULE UNWIND_FORALL_CONV

end (* struct *)
