(*---------------------------------------------------------------------------
    Raising basic lambda calculus conversions to handle pairs
 ---------------------------------------------------------------------------*)

structure PairedLambda :> PairedLambda =
struct

open HolKernel boolLib pairTheory pairSyntax;

val ERR = mk_HOL_ERR "PairedLambda";

fun is_uncurry_tm c = same_const uncurry_tm c;
fun is_uncurry x = is_uncurry_tm (rator x) handle HOL_ERR _ => false;

(* ---------------------------------------------------------------------*)
(* PAIRED_BETA_CONV: Generalized beta conversions for tupled lambda     *)
(*                  abstractions applied to tuples (i.e. redexes)       *)
(*                                                                      *)
(* Given the term:                                                      *)
(*                                                                      *)
(*   "(\(x1, ... ,xn).t) (t1, ... ,tn)"                                 *)
(*                                                                      *)
(* PAIRED_BETA_CONV proves that:                                        *)
(*                                                                      *)
(*   |- (\(x1, ... ,xn).t) (t1, ... ,tn) = t[t1, ... ,tn/x1, ... ,xn]   *)
(*                                                                      *)
(* where t[t1,...,tn/x1,...,xn] is the result of substituting ti for xi *)
(* in parallel in t, with suitable renaming of variables to prevent     *)
(* free variables in t1,...,tn becoming bound in the result.            *)
(*                                                                      *)
(* The conversion works for arbitrarily nested tuples.  For example:    *)
(*                                                                      *)
(*   PAIRED_BETA_CONV "(\((a,b),(c,d)).t) ((1,2),(3,4))"                *)
(*                                                                      *)
(* gives:                                                               *)
(*                                                                      *)
(*  |- (\((a,b),(c,d)).t) ((1,2),(3,4)) = t[1,2,3,4/a,b,c,d]            *)
(*                                                                      *)
(* Bugfix: INST used instead of SPEC to avoid priming.    [TFM 91.04.17]*)
(* ---------------------------------------------------------------------*)


val PAIRED_BETA_CONV = pairTheory.PAIRED_BETA_CONV;


(*-------------------------------------------------------*)
(* PAIRED_ETA_CONV "\(x1,.(..).,xn). P (x1,.(..).,xn)" = *)
(*       |- \(x1,.(..).,xn). P (x1,.(..).,xn) = P        *)
(* [JRH 91.07.17]                                        *)
(*-------------------------------------------------------*)

local val pthm = GEN_ALL (SYM (SPEC_ALL pairTheory.PAIR))
      fun pairify tm =
        let val step = ISPEC tm pthm
            val (Rator,r) = dest_comb (rhs (concl step))
            val (pop,l) = dest_comb Rator
        in
          TRANS step (MK_COMB(AP_TERM pop (pairify l), pairify r))
        end
        handle HOL_ERR _ => REFL tm
in
fun PAIRED_ETA_CONV tm =
   let val (varstruct,body) = dest_pabs tm
       val (f,Rand) = dest_comb body
       val _ = assert (aconv varstruct) Rand
       val xv = mk_var("x", type_of varstruct)
       val peq = pairify xv
       val par = rhs (concl peq)
       val bth = PAIRED_BETA_CONV (mk_comb(tm, par))
   in
     EXT (GEN xv (SUBS [SYM peq] bth))
   end
   handle HOL_ERR {message, ...} => raise ERR "PAIRED_ETA_CONV" message
end;

(*--------------------------------------------------------------------*)
(* GEN_BETA_CONV - reduces single or paired abstractions, introducing *)
(* arbitrarily nested "FST" and "SND" if the rand is not sufficiently *)
(* paired. Example:                                                   *)
(*                                                                    *)
(*   #GEN_BETA_CONV "(\(x,y). x + y) numpair";                        *)
(*   |- (\(x,y). x + y)numpair = (FST numpair) + (SND numpair)        *)
(* [JRH 91.07.17]                                                     *)
(*--------------------------------------------------------------------*)

local val pair = CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) pairTheory.PAIR
      val uncth = SPEC_ALL pairTheory.UNCURRY_DEF
in
val GEN_BETA_CONV =
 let fun gbc tm =
   let val (abst,arg) = dest_comb tm
   in if Term.is_abs abst
      then BETA_CONV tm
      else let val _ = assert is_uncurry abst
               val eqv = if can dest_pair arg then REFL arg else ISPEC arg pair
               val _ = dest_pair (rhs (concl eqv))
               val res = AP_TERM abst eqv
               val rt0 = TRANS res (PART_MATCH lhs uncth (rhs (concl res)))
               val (tm1a,tm1b) = dest_comb (rhs (concl rt0))
               val rt1 = AP_THM (gbc tm1a) tm1b
               val rt2 = gbc (rhs (concl rt1))
           in
              TRANS rt0 (TRANS rt1 rt2)
           end
   end
 in
   fn tm => gbc tm handle HOL_ERR _ => raise ERR "GEN_BETA_CONV" ""
 end
end;


val GEN_BETA_RULE = CONV_RULE (DEPTH_CONV GEN_BETA_CONV)
val GEN_BETA_TAC  = CONV_TAC (DEPTH_CONV GEN_BETA_CONV)


(*---------------------------------------------------------------------------
        Let reduction
 ---------------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Internal function: ITER_BETA_CONV (iterated, tupled beta-conversion).*)
(*                                                                      *)
(* The conversion ITER_BETA_CONV reduces terms of the form:             *)
(*                                                                      *)
(*     (\v1 v2...vn.tm) x1 x2 ... xn xn+1 ... xn+i                      *)
(*                                                                      *)
(* where the v's can be varstructs. The behaviour is similar to         *)
(* LIST_BETA_CONV, but this function also does paired abstractions.     *)
(* ---------------------------------------------------------------------*)

fun ITER_BETA_CONV tm =
   let
      val (Rator, Rand) = dest_comb tm
      val thm = AP_THM (ITER_BETA_CONV Rator) Rand
      val redex = rand (concl thm)
      val red = TRY_CONV (BETA_CONV ORELSEC PAIRED_BETA_CONV) redex
   in
      TRANS thm red
   end
   handle HOL_ERR _ => REFL tm

(* ---------------------------------------------------------------------*)
(* Internal function: ARGS_CONV (apply a list of conversions to the     *)
(* arguments of a curried function application).                        *)
(*                                                                      *)
(* ARGS_CONV [conv1;...;convn] "f a1 ... an" applies convi to ai.       *)
(* ---------------------------------------------------------------------*)

local
    fun appl [] [] = []
      | appl (f :: frst) (a :: arest) = f a :: appl frst arest
      | appl _ _ = raise ERR "ARGS_CONV" "appl"
in
   fun ARGS_CONV cs tm =
      let
         val (f,ths) = (I ## appl cs) (strip_comb tm)
      in
         rev_itlist (C (curry MK_COMB)) ths (REFL f)
      end
end

(* ---------------------------------------------------------------------*)
(* Internal function RED_WHERE.                                         *)
(*                                                                      *)
(* Given the arguments "f" and "tm[f]", this function produces a        *)
(* conversion that will apply ITER_BETA_CONV to its argument at all     *)
(* subterms that correspond to occurrences of f (bottom-up).            *)
(* ---------------------------------------------------------------------*)

fun RED_WHERE fnn body =
   if is_var body orelse is_const body
      then REFL
   else let
           val (_, Body) = Term.dest_abs body
        in
           ABS_CONV (RED_WHERE fnn Body)
        end
   handle HOL_ERR _ =>
     let
        val (f, args) = strip_comb body
     in
        if aconv f fnn then
          ARGS_CONV (map (RED_WHERE fnn) args) THENC ITER_BETA_CONV
        else let
                val (Rator,Rand) = dest_comb body
             in
                RAND_CONV (RED_WHERE fnn Rand)
                THENC RATOR_CONV (RED_WHERE fnn Rator)
             end
     end

(* ---------------------------------------------------------------------*)
(* Internal function: REDUCE                                            *)
(*                                                                      *)
(* This function does the appropriate beta-reductions in the result of  *)
(* expanding a let-term.  For terms of the form:                        *)
(*                                                                      *)
(*      "let f x1 ... xn = t in tm[f]"                                  *)
(*                                                                      *)
(* we have that:                                                        *)
(*                                                                      *)
(*      th |- <let term> = tm[\x1 ... xn. t/f]                          *)
(*                                                                      *)
(* And the arguments x and f will be:                                   *)
(*                                                                      *)
(*       x = \x1 ... xn. t                                              *)
(*       f = \f. tm[f]                                                  *)
(*                                                                      *)
(* REDUCE searches in tm[f] for places in which f occurs, and then does *)
(* an iterated beta-reduction (possibly of varstruct-abstractions) in   *)
(* the right-hand side of the input theorem th, at the places that      *)
(* correspond to occurrences of f in tm[f].                             *)
(* ---------------------------------------------------------------------*)

fun REDUCE f x th =
   if not (is_abs x orelse pairSyntax.is_uncurry x) then th
   else let
           val (Bvar, Body) = Term.dest_abs f
        in
           CONV_RULE (RAND_CONV (RED_WHERE Bvar Body)) th
        end

(* ---------------------------------------------------------------------*)
(* let_CONV: conversion for reducing "let" terms.                       *)
(*                                                                      *)
(* Given a term:                                                        *)
(*                                                                      *)
(*   "let v1 = x1 and ... and vn = xn in tm[v1,...,vn]"                 *)
(*                                                                      *)
(* let_CONV proves that:                                                *)
(*                                                                      *)
(*   |- let v1 = x1 and ... and vn = xn in tm[v1,...,vn]                *)
(*      =                                                               *)
(*      tm[x1,...,xn/v1,...,vn]                                         *)
(*                                                                      *)
(* where t[t1,...,tn/x1,...,xn] is the result of "substituting" the     *)
(* value xi for vi  in parallel in tm (see below).                      *)
(*                                                                      *)
(* Note that the vi's can take any one of the following forms:          *)
(*                                                                      *)
(*    Variables:    "x" etc.                                            *)
(*    Tuples:       "(x,y)" "(a,b,c)" "((a,b),(c,d))" etc.              *)
(*    Applications: "f (x,y) z" "f x" etc.                              *)
(*                                                                      *)
(* Variables are just substituted for. With tuples, the substitution is *)
(* done component-wise, and function applications are effectively       *)
(* rewritten in the body of the let-term.                               *)
(* ---------------------------------------------------------------------*)

local
   fun conv bconv =
      fn tm =>
         let
            val (func, arg) = boolSyntax.dest_let tm
            val (ty1, ty2) = Type.dom_rng (Term.type_of func)
            val defn = Thm.INST_TYPE [alpha |-> ty1, beta |-> ty2] LET_DEF
            val thm = RIGHT_BETA (AP_THM (RIGHT_BETA (AP_THM defn func)) arg)
         in
            if Term.is_abs func
               then REDUCE func arg (RIGHT_BETA thm)
            else if pairSyntax.is_uncurry func
                    then CONV_RULE (RAND_CONV bconv) thm
                 else CONV_RULE
                         (RAND_CONV (conv bconv))
                         (AP_THM
                            (AP_TERM (rator (rator tm)) (conv bconv func)) arg)
         end
         handle HOL_ERR _ => raise ERR "let_CONV" "cannot reduce the let"
in
   val let_CONV = conv PAIRED_BETA_CONV
   val GEN_LET_CONV = conv GEN_BETA_CONV
end

(* ---------------------------------------------------------------------*)
(* LET_SIMP_CONV: conversion for eliminating unused lets                *)
(*                                                                      *)
(* Given a term:                                                        *)
(*                                                                      *)
(*   "let (v1, v2) = (x1,x2) in tm[v1]"                                 *)
(*                                                                      *)
(* LET_SIMP_CONV gen                                                    *)
(*                                                                      *)
(*   |- let (v1, v2) = (x1,x2) in tm[v1]                                *)
(*      =                                                               *)
(*      let v1 = x1 in tm[v1]                                           *)
(*                                                                      *)
(* Pairs of arbitrary nestings can be handled and more than one         *)
(* variable might be removed. If all variables are unused, the let      *)
(* is eliminated completely.                                            *)
(*                                                                      *)
(* The parameter gen determines, whether FST and SND are introduced     *)
(* to handle values that are not explicitly pairs                       *)
(* ---------------------------------------------------------------------*)

fun LET_SIMP_CONV gen tm =
let
   (*destruct the original term ``let vars = v in b vars``,
     ab = \vars. b vars*)
   val (ab, v) = dest_let tm;
   val (vars,b) = dest_pabs ab

   (*check which variables are used / unused. Abort if
     all variables are really needed*)
   val vars_set = FVL [vars] empty_tmset;
   val unused_vars_set = HOLset.difference (vars_set, FVL [b] empty_tmset);
   val _ = if HOLset.isEmpty unused_vars_set then raise UNCHANGED else ();

   val used_vars_list = HOLset.listItems (
        HOLset.difference (vars_set, unused_vars_set));

   val beta_conv = if gen then GEN_BETA_CONV else
       (PAIRED_BETA_CONV ORELSEC BETA_CONV);

   (*generate the new result term
     if no variable is needed just return b*)
   val result_term = if null used_vars_list then b else
       let
          (*otherwise abstract with just the needed variables
            and get the new value of v by using GEN_BETA_CONV*)
          val new_vars = list_mk_pair used_vars_list;
          val new_ab = mk_pabs (new_vars, b);
          val new_v0 = mk_comb (mk_pabs (vars, new_vars), v);
          val new_v_thm = beta_conv new_v0
          val new_v = (rhs o concl) new_v_thm
       in
          mk_let (new_ab, new_v)
       end;

   (*prove equality between the original term and the constructed one by
     removing LET and simplifying using GEN_BETA_CONV. if LET was removed,
     an error will occur, so use reflexivity in that case*)
   fun my_let_CONV t =
       (REWR_CONV LET_THM THENC beta_conv) t handle HOL_ERR _ =>
       REFL t

   val tm_thm = my_let_CONV tm
   val result_thm = my_let_CONV result_term
in
   TRANS tm_thm (GSYM result_thm)
end handle HOL_ERR _ => raise UNCHANGED;


end
