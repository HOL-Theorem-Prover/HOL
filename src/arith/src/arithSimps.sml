(* ---------------------------------------------------------------------*
 * A symbolic calculator for the HOL "num" arithmetic.  Does no proof   *
 * - it relies on some other tool to do the proof.  See arith_ss.sml.   *
 *                                                                      *
 * When using this with natural arithmetic, note that the fact that     *
 * m-n=0 for n>m is not taken into account.  It assumes that            *
 * subtraction is always being used in a "well behaved" way.            (
 * ---------------------------------------------------------------------*)
structure arithSimps :> arithSimps =
struct
  open Arbint
  val << = String.<


open arithLib reduceLib;
open HolKernel Parse Drule Conv Psyntax
open liteLib Arith_cons Arith simpLib Traverse Cache Trace;

type conv = Abbrev.conv;

(* ---------------------------------------------------------------------*
 * LIN: Linear arithmetic expressions                                   *
 * ---------------------------------------------------------------------*)

val mk_numeral = term_of_int;
val dest_numeral = int_of_term;

datatype lin = LIN of ((term * int) list * int);

fun term_ord (t1,t2) =
    if is_var t1 then
	if is_var t2 then String.compare (fst(dest_var t1),fst(dest_var t2))
	else LESS
    else if is_const t1
         then if is_var t2 then GREATER
	      else if is_const t2
                   then String.compare (fst(dest_const t1),fst(dest_const t2))
	           else LESS
    else if is_comb t1 then
        if is_var t2 orelse is_const t2 then GREATER
        else if is_comb t2 then
           case term_ord (rator t1,rator t2) of
	       EQUAL => term_ord (rand t1,rand t2)
	     | x => x
	else LESS
    else if is_abs t1 then
        if is_var t2 orelse is_const t2 orelse is_comb t2 then GREATER
        else if is_comb t2 then
           case term_ord (bvar t1,bvar t2) of
	       EQUAL => term_ord (body t1,body t2)
	     | x => x
	else LESS
    else failwith "term_ord";

val zero_tm = (--`0`--);

fun dest_SUC tm =
    if (fst(dest_const(rator tm)) = "SUC") then rand tm else fail();

val num_ty = Type`:num`;

val mk_lin =
  let fun tmord ((term1,n1:int),(term2,n2)) =
            case term_ord (term1,term2)
             of EQUAL => Arbint.compare(n1,n2)
              | x => x
      val tmlt = lt_of_ord tmord;
      fun shrink_likes ((tm1,k1)::(tm2,k2)::rest) =
        if (tm1 = tm2) then
          if (k1+k2 = zero) then shrink_likes rest
          else shrink_likes ((tm1,k1+k2)::rest)
        else (tm1,k1)::shrink_likes((tm2,k2)::rest)
        | shrink_likes x = x
      val canon_tms = shrink_likes o sort (curry tmlt)
      fun mk_tm (tm, k) = if k = zero then failwith "mk_tm: zero term"
                          else (tm, k)
  in fn (k,x) => LIN (canon_tms (mapfilter mk_tm k),x)
  end;

fun dest_lin (LIN p) = p;

(* ---------------------------------------------------------------------
 * LIN <--> HOL
 * --------------------------------------------------------------------*)

fun is_pos_tm (tm,n) = n > zero
fun is_neg_tm (tm,n) = n < zero

fun term_of_tm (tm,n) =
   if (abs n = one) then tm
   else mk_mult (mk_numeral (abs n),tm);


val list_mk_plus = end_foldr mk_plus;
val list_mk_mult = end_foldr mk_mult;

fun term_of_lin (LIN (tms,k)) =
  let val pos_terms = map term_of_tm (filter is_pos_tm tms)
      val neg_terms =
        (map term_of_tm (filter is_neg_tm tms))@
        (if k < zero then [mk_numeral (~k)] else [])
      val const_term = if k > zero then SOME (mk_numeral k) else NONE
  in
      case const_term of
	  SOME x =>
	      if (null pos_terms) then
		  if (null neg_terms) then x
		  else mk_minus(x,list_mk_plus neg_terms)
	      else if (null neg_terms) then list_mk_plus(pos_terms@[x])
		   else mk_minus(list_mk_plus (pos_terms@[x]),
                                 list_mk_plus neg_terms)
	| NONE =>
	      if (null pos_terms) then
		  if (null neg_terms) then zero_tm
		  else failwith "no positive terms"
	      else if (null neg_terms) then list_mk_plus pos_terms
		   else mk_minus(list_mk_plus pos_terms,list_mk_plus neg_terms)
  end;

fun negate (x,y:int) = (x,~y);

fun lin_of_term tm =
  let val (t1,t2) = dest_plus tm
      val (l1,k1) = dest_lin(lin_of_term t1)
      val (l2,k2) = dest_lin(lin_of_term t2)
  in mk_lin(l1@l2,k1+k2)
  end
  handle HOL_ERR _ =>
  let val (t1,t2) = dest_minus tm
      val (l1,k1) = dest_lin(lin_of_term t1)
      val (l2,k2) = dest_lin(lin_of_term t2)
  in mk_lin(l1@map negate l2,k1 - k2)
  end
(*
  handle HOL_ERR _ =>
  let val (l1,k1) = dest_lin(lin_of_term (dest_SUC tm))
  in LIN(l1,k1+1)
  end
*)
  handle HOL_ERR _ =>
  mk_lin([], dest_numeral tm)
  handle HOL_ERR _ =>
  mk_lin([(tm,one)], zero);


val linear_reduction = term_of_lin o lin_of_term;

(* ---------------------------------------------------------------------
 * is_arith
 *
 * Decide whether something looks like something which may be
 * either decideable by ARITH_CONV or useful for ARITH_CONV.
 *
 * EXAMPLES
 * is_arith (--`~(1 = 2)`--);                      (* true *)
 * is_arith (--`~(LENGTH [1] = 0)`--);             (* true *)
 * is_arith (--`~(x:'a = y)`--);                   (* false *)
 * is_arith (--`!z:num. ~(x:'a = y)`--);           (* false *)
 * is_arith (--`!z:num. ~(z = y)`--);              (* true *)
 * is_arith (--`!P. !z:num. ~(z = y) /\ P`--);     (* false *)
 * is_arith (--`(!i. i < 1 + n' ==> (f i = f' i)) ==> 1 + n > 0`--);
                                                   (* false *)
 * --------------------------------------------------------------------*)
(* there might still be bugs in this.... DRS 5 Aug 96 *)

fun cond_has_arith_components tm =
  if is_cond tm then let
    val {cond,rarm,larm} = Dsyntax.dest_cond tm
  in
    List.all is_arith [cond, rarm, larm]
  end
  else true
and
  is_arith tm =
  is_presburger tm orelse
  List.all (fn t => type_of t = num_ty andalso cond_has_arith_components t)
  (non_presburger_subterms tm)

(*
   if (is_forall tm) then
       (type_of (bvar (rand tm)) = num_ty andalso is_presburger(body(rand tm)))
   else if is_exists tm then
	(type_of (bvar (rand tm)) = num_ty andalso is_arith (body (rand tm)))
   else if (is_abs tm) then false
   else if (is_geq tm) orelse (is_less tm) orelse
           (is_leq tm) orelse (is_great tm) then  true
   else if (is_conj tm) orelse (is_disj tm) orelse (is_imp tm)
     orelse (is_eq tm andalso type_of (rhs tm) = Type.bool) then
     is_arith (lhand tm) andalso is_arith (rand tm)
   else if (is_neg tm) then is_arith (dest_neg tm)
   else if (is_eq tm) then (type_of (rhs tm) = num_ty andalso
                            no_bool_vars_in (lhs tm) andalso
                            no_bool_vars_in (rhs tm))
   else false;
*)

(* This function determines whether or not to add something as context to
   the arithmetic decision procedure.  Because arithLib.ARITH_CONV can't
   handle implications with nested foralls on the left hand side, we
   eliminate those here.  *)
fun is_arith_thm thm =
  not (null (hyp thm)) andalso is_arith (concl thm) andalso
   (not (is_forall (concl thm)));

type ctxt = thm list;

val ARITH = EQT_ELIM o ARITH_CONV;

fun CTXT_ARITH thms tm =
  if (type_of tm = Type.bool) andalso (is_arith tm) then
     let val context = map concl thms
         fun try gl =
           let val gl' = list_mk_imp(context,gl)
	   in rev_itlist (C MP) thms (ARITH gl')
           end
	 val thm = EQT_INTRO (try tm)
	     handle HOL_ERR _ => EQF_INTRO (try(mk_neg tm))
     in trace(1,PRODUCE(tm,"ARITH",thm)); thm
     end
   else if (type_of tm = num_ty) then
     let val reduction = linear_reduction tm
     in if (reduction = tm)
        then failwith "CTXT_ARITH: no reduction possible"
        else
          let val context = map concl thms
              val gl = list_mk_imp(context,mk_eq(tm,reduction))
	      val thm = rev_itlist (C MP) thms (ARITH gl)
          in trace(1,PRODUCE(tm,"ARITH",thm)); thm
          end
     end
   else failwith "CTXT_ARITH: not applicable";

val (CACHED_ARITH,arith_cache) =
  let fun check tm =
      let val ty = type_of tm
      in (ty = num_ty orelse (ty=Type.bool andalso is_arith tm))
      end;
  in  CACHE (check,CTXT_ARITH)
  end;

(* This needs to be done more systematically! *)
local open arithmeticTheory
      val sym_lhs = CONV_RULE ((BINDER_CONV o BINDER_CONV
                                o RATOR_CONV o RAND_CONV) SYM_CONV)
      val one_suc = Rewrite.PURE_REWRITE_RULE [Num_conv.num_CONV (Term`1`)]
      val add_sym = Rewrite.ONCE_REWRITE_RULE [ADD_SYM]
in
val arithmetic_rewrites = [LESS_EQ_0,
MULT_EQ_0, sym_lhs MULT_EQ_0, ADD_EQ_0, sym_lhs ADD_EQ_0,
   MULT_EQ_1, sym_lhs MULT_EQ_1,
   one_suc MULT_EQ_1, one_suc (sym_lhs MULT_EQ_1),
   MULT_RIGHT_1, MULT_LEFT_1,
   ARITH(Term `!x. ((SUC x = 1) = (x=0)) /\ ((1 = SUC x) = (x = 0))`),
   ARITH(Term`!x. ((SUC x = 2) = (x=1)) /\ ((2 = SUC x) = (x=1))`),
   ADD_INV_0_EQ, add_sym ADD_INV_0_EQ,
   (* subtraction *)
   SUB_EQUAL_0, SUC_SUB1, SUB_0, ADD_SUB, SUB_EQ_0, sym_lhs SUB_EQ_0,
   SUB_LESS_EQ, SUB_MONO_EQ, SUB_RIGHT_GREATER, SUB_RIGHT_LESS,
   SUB_RIGHT_GREATER_EQ, SUB_RIGHT_LESS_EQ,

   (* order relations and arith. ops *)
   LESS_MONO_ADD_EQ, add_sym LESS_MONO_ADD_EQ,
   ADD_MONO_LESS_EQ, add_sym ADD_MONO_LESS_EQ,
   EQ_MONO_ADD_EQ, add_sym EQ_MONO_ADD_EQ,
   ARITH (Term `!x y w. x + y < w + x = y < w`),
   add_sym (ARITH (Term `!x y w. x + y < w + x = y < w`)),
   prim_recTheory.INV_SUC_EQ, LESS_MONO_EQ, LESS_EQ_MONO,
   LESS_MULT_MONO, MULT_SUC_EQ, MULT_MONO_EQ,
   NOT_SUC_LESS_EQ,
   MULT_EXP_MONO,
  (* falsities *)
   NOT_EXP_0, NOT_ODD_EQ_EVEN, NOT_SUC_ADD_LESS_EQ,
   NOT_SUC_LESS_EQ_0, prim_recTheory.NOT_LESS_0
   ]
end;


val ARITH_REDUCER = let
  exception CTXT of thm list;
  fun get_ctxt e = (raise e) handle CTXT c => c
  fun add_ctxt(ctxt, newthms) = let
    val addthese = filter is_arith_thm (flatten (map CONJUNCTS newthms))
  in
    CTXT (addthese @ get_ctxt ctxt)
  end
in
  REDUCER {addcontext = add_ctxt,
           apply = fn args => CACHED_ARITH (get_ctxt (#context args)),
           initial = CTXT []}
end;

val a_v = --`NUMERAL a`--
val b_v = --`NUMERAL b`--
val zero = --`0`--
val SUC = --`SUC`--
val x = Psyntax.mk_var("x", ==`:num`==)
val y = Psyntax.mk_var("y", ==`:num`==)

fun reducer t = let
  open Psyntax
  val (_, args) = strip_comb t
  fun is_suc t = is_comb t andalso fst (dest_comb t) = SUC
  fun reducible t =
    Term.is_numeral t orelse (is_suc t andalso reducible (snd (dest_comb t)))
in
  if List.all reducible args then reduceLib.REDUCE_CONV t else NO_CONV t
end

fun mk_redconv0 pat = {name = "REDUCE_CONV (arithmetic reduction)", trace = 2,
                       key = SOME([], pat), conv = K (K reducer)}
fun mk_redconv op_t = mk_redconv0 (list_mk_comb(op_t, [x, y]))

val ARITH_ss = simpLib.SIMPSET
    {convs = [], rewrs = arithmetic_rewrites, congs = [],
     filter = NONE, ac = [], dprocs = [ARITH_REDUCER]};

val REDUCE_ss = simpLib.SIMPSET
  {convs = map mk_redconv [--`$*`--, --`$+`--, --`$-`--,
                           --`$DIV`--, --`$MOD`--, --`$EXP`--,
                           --`$<`--, --`$<=`--, --`$>`--,
                           --`$>=`--, --`$= : num -> num -> bool`--],
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

fun clear_arith_caches() = clear_cache arith_cache;


end (* struct *)
