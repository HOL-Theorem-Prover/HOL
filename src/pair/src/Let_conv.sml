(* ===================================================================== *)
(* FILE          : let_conv.sml                                          *)
(* DESCRIPTION   : Provides a conversion for paired beta-redexes, e.g.,  *)
(*                                                                       *)
(*                     PAIRED_BETA_CONV (--`(\(x,y). x+y) (1,2)`--)      *)
(*                                                                       *)
(*                 gives   |- (\(x,y). x+y) (1,2) = 1+2                  *)
(*                                                                       *)
(*                 and provides a conversion for "let" terms, e.g.,      *)
(*                                                                       *)
(*                                                                       *)
(*                     let_CONV (--`let x = 1 in x+1`--)                 *)
(*                                                                       *)
(*                 gives   |- (let x = 1 in x+1) = 1 + 1                 *)
(*                                                                       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c)  Tom Melham, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


structure Let_conv :> Let_conv =
struct

open HolKernel Parse Drule Conv boolTheory;

infix ORELSEC THENC;
infix 3 ##;
infix 5 |->;

fun LET_CONV_ERR function message = 
    HOL_ERR{origin_structure ="Let_conv",
            origin_function = function,
            message = message}

fun is_uncurry tm = 
  (#Name(dest_const(rator tm)) = "UNCURRY") handle HOL_ERR _ => false;

(* ---------------------------------------------------------------------*)
(* PAIRED_BETA_CONV: Generalized beta conversions for tupled lambda	*)
(*		    abstractions applied to tuples (i.e. redexes)	*)
(*									*)
(* Given the term:                                    			*)
(*                                                                      *)
(*   "(\(x1, ... ,xn).t) (t1, ... ,tn)"                                	*)
(*                                                                      *)
(* PAIRED_BETA_CONV proves that:					*)
(*                                                                      *)
(*   |- (\(x1, ... ,xn).t) (t1, ... ,tn) = t[t1, ... ,tn/x1, ... ,xn]   *)
(*                                                                      *)
(* where t[t1,...,tn/x1,...,xn] is the result of substituting ti for xi	*)
(* in parallel in t, with suitable renaming of variables to prevent	*)
(* free variables in t1,...,tn becoming bound in the result.     	*)
(*                                                                      *)
(* The conversion works for arbitrarily nested tuples.  For example:	*)
(*									*)
(*   PAIRED_BETA_CONV "(\((a,b),(c,d)).t) ((1,2),(3,4))"		*)
(*									*)
(* gives:								*)
(*									*)
(*  |- (\((a,b),(c,d)).t) ((1,2),(3,4)) = t[1,2,3,4/a,b,c,d]     	*)
(*									*)
(* Bugfix: INST used instead of SPEC to avoid priming.    [TFM 91.04.17]*)
(* ---------------------------------------------------------------------*)

local val vs = map genvar [Type`:'a -> ('b -> 'c)`, Type.alpha, Type.beta]
      val (atyv,btyv,ctyv) =  (Type.alpha,Type.beta, Type`:'c`)
      val DEF = SPECL vs pairTheory.UNCURRY_DEF
      val check = assert (fn t => (#Name(dest_const t) = "UNCURRY"))
      val RBCONV = RATOR_CONV BETA_CONV THENC BETA_CONV
      fun conv tm = 
       let val {Rator,Rand} = dest_comb tm
           val {fst,snd} = dest_pair Rand
           val {Rator,Rand = f} = dest_comb Rator
           val _ = check Rator
           val [t1,ty'] = #Args(dest_type (type_of f))
           val [t2,t3] = #Args(dest_type ty')
           val inst = INST_TYPE [atyv |-> t1, btyv |-> t2,  ctyv |-> t3] DEF
           val (fv,[xv,yv]) = strip_comb(rand(concl inst))
           val def = INST [yv |-> snd, xv |-> fst, fv |-> f] inst
       in
         TRANS def 
          (if is_abs f 
           then if is_abs (#Body(dest_abs f)) then RBCONV (rhs(concl def))
                else CONV_RULE (RAND_CONV conv)
                      (AP_THM(BETA_CONV(mk_comb{Rator=f, Rand=fst})) snd)
           else let val recc = conv (rator(rand(concl def)))
                in if is_abs (rhs(concl recc))
                   then RIGHT_BETA (AP_THM recc snd)
                   else TRANS (AP_THM recc snd) 
                           (conv(mk_comb{Rator=rhs(concl recc), Rand=snd}))
                end)
       end
in
fun PAIRED_BETA_CONV tm 
  = conv tm handle HOL_ERR _ => raise LET_CONV_ERR "PAIRED_BETA_CONV" ""
end;


(* ---------------------------------------------------------------------*)
(* Internal function: ITER_BETA_CONV (iterated, tupled beta-conversion).*)
(*									*)
(* The conversion ITER_BETA_CONV reduces terms of the form:		*)
(*									*)
(*     (\v1 v2...vn.tm) x1 x2 ... xn xn+1 ... xn+i			*)
(*									*)
(* where the v's can be varstructs. The behaviour is similar to		*)
(* LIST_BETA_CONV, but this function also does paired abstractions.	*)
(* ---------------------------------------------------------------------*)

fun ITER_BETA_CONV tm = 
  let val {Rator,Rand} = dest_comb tm 
      val thm = AP_THM (ITER_BETA_CONV Rator) Rand
      val redex = rand(concl thm)
      val red = TRY_CONV(BETA_CONV ORELSEC PAIRED_BETA_CONV) redex
  in
    TRANS thm red
  end
  handle HOL_ERR _ => REFL tm;


(* ---------------------------------------------------------------------*)
(* Internal function: ARGS_CONV (apply a list of conversions to the 	*)
(* arguments of a curried function application).			*)
(*									*)
(* ARGS_CONV [conv1;...;convn] "f a1 ... an" applies convi to ai.	*)
(* ---------------------------------------------------------------------*)

local fun appl [] [] = []
        | appl (f::frst) (a::arest) = f a::appl frst arest
        | appl _ _ = raise LET_CONV_ERR "ARGS_CONV" "appl"
in
fun ARGS_CONV cs tm =
  let val (f,ths) = (I ## appl cs) (strip_comb tm)
  in 
    rev_itlist (C (curry MK_COMB)) ths (REFL f) 
  end
end;

(* ---------------------------------------------------------------------*)
(* Internal function RED_WHERE.						*)
(*									*)
(* Given the arguments "f" and "tm[f]", this function produces a 	*)
(* conversion that will apply ITER_BETA_CONV to its argument at all	*)
(* subterms that correspond to occurrences of f (bottom-up).		*)
(* ---------------------------------------------------------------------*)

fun RED_WHERE fnn body = 
   if (is_var body orelse is_const body) then REFL 
   else let val {Body,...} = dest_abs body 
        in 
          ABS_CONV (RED_WHERE fnn Body)
        end
        handle HOL_ERR _ => 
          let val (f,args) = strip_comb body 
          in
          if (f=fnn) 
          then ARGS_CONV (map(RED_WHERE fnn)args) THENC ITER_BETA_CONV
          else let val {Rator,Rand} = dest_comb body 
               in 
                RAND_CONV(RED_WHERE fnn Rand)
                  THENC 
                RATOR_CONV (RED_WHERE fnn Rator)
               end
          end;

(* ---------------------------------------------------------------------*)
(* Internal function: REDUCE						*)
(* 									*)
(* This function does the appropriate beta-reductions in the result of	*)
(* expanding a let-term.  For terms of the form:			*)
(*									*)
(*      "let f x1 ... xn = t in tm[f]"					*)
(*									*)
(* we have that:							*)
(*									*)
(*      th |- <let term> = tm[\x1 ... xn. t/f]				*)
(*									*)
(* And the arguments x and f will be:					*)
(*									*)
(*       x = \x1 ... xn. t						*)
(*       f = \f. tm[f]							*)
(*									*)
(* REDUCE searches in tm[f] for places in which f occurs, and then does	*)
(* an iterated beta-reduction (possibly of varstruct-abstractions) in	*)
(* the right-hand side of the input theorem th, at the places that	*)
(* correspond to occurrences of f in tm[f].				*)
(* ---------------------------------------------------------------------*)

fun REDUCE f x th =
   if not(is_abs x orelse is_uncurry x)
   then th 
   else let val {Bvar,Body} = dest_abs f 
        in
          CONV_RULE (RAND_CONV (RED_WHERE Bvar Body)) th
        end;

(* ---------------------------------------------------------------------*)
(* let_CONV: conversion for reducing "let" terms.			*)
(*									*)
(* Given a term:                                    			*)
(*                                                                      *)
(*   "let v1 = x1 and ... and vn = xn in tm[v1,...,vn]"			*)
(*                                                                      *)
(* let_CONV proves that:						*)
(*                                                                      *)
(*   |- let v1 = x1 and ... and vn = xn in tm[v1,...,vn] 		*)
(*	=								*)
(*      tm[x1,...,xn/v1,...,vn]						*)
(*                                                                      *)
(* where t[t1,...,tn/x1,...,xn] is the result of "substituting" the 	*)
(* value xi for vi  in parallel in tm (see below).			*)
(*									*)
(* Note that the vi's can take any one of the following forms:  	*)
(*									*)
(*    Variables:    "x" etc.    					*)
(*    Tuples:       "(x,y)" "(a,b,c)" "((a,b),(c,d))" etc.		*)
(*    Applications: "f (x,y) z" "f x" etc.				*)
(*									*)
(* Variables are just substituted for. With tuples, the substitution is	*)
(* done component-wise, and function applications are effectively	*)
(* rewritten in the body of the let-term.				*)
(* ---------------------------------------------------------------------*)

local
fun conv tm = 
   let val {func,arg} = dest_let tm
       val {Args=[ty1,ty2],...} = dest_type(type_of func)
       val defn = INST_TYPE [Type.alpha |-> ty1, Type.beta |-> ty2] LET_DEF
       val thm = RIGHT_BETA(AP_THM(RIGHT_BETA(AP_THM defn func))arg)
   in 
   if is_abs func
   then REDUCE func arg (RIGHT_BETA thm) 
   else if is_uncurry func
        then CONV_RULE (RAND_CONV PAIRED_BETA_CONV) thm 
        else CONV_RULE (RAND_CONV conv) 
                       (AP_THM(AP_TERM (rator(rator tm)) (conv func)) arg)
   end
in
fun let_CONV tm = conv tm 
 handle HOL_ERR _ => raise LET_CONV_ERR "let_CONV" "cannot reduce the let"
end;


(*-------------------------------------------------------*)
(* PAIRED_ETA_CONV "\(x1,.(..).,xn). P (x1,.(..).,xn)" = *)
(*       |- \(x1,.(..).,xn). P (x1,.(..).,xn) = P        *)
(* [JRH 91.07.17]                                        *)
(*-------------------------------------------------------*)

local val pthm = GEN_ALL (SYM (SPEC_ALL pairTheory.PAIR))
      fun pairify tm =
        let val step = ISPEC tm pthm
            val {Rator, Rand=r} = dest_comb (rhs (concl step))
            val {Rator=pop, Rand=l} = dest_comb Rator
        in
          TRANS step (MK_COMB(AP_TERM pop (pairify l), pairify r))
        end
        handle HOL_ERR _ => REFL tm
in
fun PAIRED_ETA_CONV tm =
   let val {varstruct,body} = dest_pabs tm
       val {Rator=f,Rand} = dest_comb body
       val _ = assert (fn tm => varstruct = tm) Rand
       val xv = mk_var{Name="x", Ty=type_of varstruct}
       val peq = pairify xv
       val par = rhs (concl peq)
       val bth = PAIRED_BETA_CONV (mk_comb{Rator=tm, Rand=par})
   in
     EXT (GEN xv (SUBS [SYM peq] bth))
   end
   handle HOL_ERR _ => raise LET_CONV_ERR "PAIRED_ETA_CONV" ""
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
      and uncth = SPEC_ALL pairTheory.UNCURRY_DEF
fun gbc tm =
   let val {Rator=abst, Rand=arg} = dest_comb tm
   in if (is_abs abst) then BETA_CONV tm 
      else let val _ = assert is_uncurry abst
               val eqv = if is_pair arg then REFL arg else ISPEC arg pair
               val _ = dest_pair (rhs (concl eqv))
               val res = AP_TERM abst eqv
               val rt0 = TRANS res (PART_MATCH lhs uncth (rhs (concl res)))
               val {Rator = tm1a,Rand = tm1b} = dest_comb (rhs (concl rt0))
               val rt1 = AP_THM (gbc tm1a) tm1b
               val tm2 = rhs (concl rt1) 
               val rt2 = gbc tm2
           in
             TRANS rt0 (TRANS rt1 rt2) 
           end
   end
in
fun GEN_BETA_CONV tm = 
    gbc tm handle HOL_ERR _ => raise LET_CONV_ERR "GEN_BETA_CONV" ""
end;

end; (* Let_conv *)
