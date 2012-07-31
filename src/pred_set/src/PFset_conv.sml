(* =====================================================================*)
(* FILE		: fset_conv.ml						*)
(* DESCRIPTION  : Conversions for taking unions and intersections of 	*)
(*		  finite sets, for deciding membership of finite sets,  *)
(*		  and so on.						*)
(*								        *)
(* REWRITTEN    : T Melham						*)
(* DATE		: 90.10.16 (adapted for pred_set: January 1992)	        *)
(* TRANSLATED to hol90 February 1993 by kls                             *)
(* =====================================================================*)

structure PFset_conv :> PFset_conv =
struct

open HolKernel boolLib pred_setSyntax pred_setTheory;

structure Parse =
struct
  open Parse
  val (Type,Term) = parse_from_grammars pred_setTheory.pred_set_grammars
end
open Parse

val ERR = mk_HOL_ERR "PFset_conv"

fun check_const cnst = assert (same_const cnst);

(* =====================================================================*)
(* FINITE_CONV: prove that a normal-form finite set is finite.  The set *)
(* in question must have the standard form:				*)
(*									*)
(*	INSERT x1 (INSERT x2 ...(INSERT xn EMPTY)... ))	 		*)
(*									*)
(* A call to:								*)
(*									*)
(*	FINITE_CONV `FINITE {x1;...;xn}`                                *)
(*									*)
(* returns:								*)
(*									*)
(*       |- FINITE {x1;...;xn} = T					*)
(*									*)
(* The conversion fails on sets of the wrong form.			*)
(* ---------------------------------------------------------------------*)

local val finI =
        let val th =
             snd(EQ_IMP_RULE
                  (SPECL[``x:'a``,``s:'a->bool``] FINITE_INSERT))
        in GEN ``s:'a->bool`` (DISCH_ALL (GEN ``x:'a`` (UNDISCH th)))
        end
      fun itfn ith x th = SPEC x (MP (SPEC (rand(concl th)) ith) th)
in
fun FINITE_CONV tm =
   let val s = dest_finite tm
       val els = strip_set s
       val (ty,_) = dom_rng(type_of s)
       val theta = [alpha |-> ty]
       val eth = INST_TYPE theta pred_setTheory.FINITE_EMPTY
       val ith = INST_TYPE theta finI
   in EQT_INTRO (itlist (itfn ith) els eth)
   end
   handle e => raise wrap_exn "PFset_conv" "FINITE_CONV" e
end;

(* =====================================================================*)
(* IN_CONV: decide membership for finite sets.				*)
(*									*)
(* A call to:								*)
(*									*)
(*	IN_CONV conv `x IN {x1;...;xn}`                                 *)
(*									*)
(* returns:								*)
(*									*)
(*	|- x IN {x1;...;xn} = T						*)
(*									*)
(* if x is syntactically identical to xi for some i, where 1<=i<=n, or	*)
(* if conv proves |- (x=xi)=T for some i, where 1<=i<=n, or it returns:	*)
(*									*)
(*	|- x IN {x1;...;xn} = F						*)
(*									*)
(* if conv proves |- (x=xi)=F for all 1<=i<=n.				*)
(*									*)
(* A call to                                                            *)
(*									*)
(*	IN_CONV conv `x IN UNIV`                                        *)
(*									*)
(* returns:								*)
(*									*)
(*	|- x IN UNIV = T						*)
(*									*)
(* =====================================================================*)

local val inI = pred_setTheory.IN_INSERT
      val inE = GEN ``x:'a``
                 (EQF_INTRO (SPEC ``x:'a`` pred_setTheory.NOT_IN_EMPTY))
      val inUNIV = pred_setTheory.IN_UNIV
      val gv = genvar bool
      val DISJ = AP_TERM boolSyntax.disjunction
      val F_OR = el 3 (CONJUNCTS (SPEC gv OR_CLAUSES))
      val OR_T = el 2 (CONJUNCTS (SPEC gv OR_CLAUSES))
      fun in_conv conv (eth,ith) x S =
        let val (y,S') = dest_insert S
            val thm = SPEC S' (SPEC y ith)
            val rectm = rand(rand(concl thm))
        in if aconv x y
           then EQT_INTRO (EQ_MP (SYM thm) (DISJ1 (ALPHA x y) rectm))
           else
             let val eql = conv (mk_eq(x, y))
                 val res = rand(concl eql)
             in
             if res=T
               then EQT_INTRO (EQ_MP (SYM thm) (DISJ1 (EQT_ELIM eql) rectm))
             else
             if res=F
             then let val rthm = in_conv conv (eth,ith) x S'
                      val thm2 = MK_COMB (DISJ eql,rthm)
                      val thm3 = INST[gv |-> rand(concl rthm)] F_OR
                  in TRANS thm (TRANS thm2 thm3)
                  end
              else raise ERR "IN_CONV" ""
             end
             handle HOL_ERR _ =>
              let val rthm = in_conv conv (eth,ith) x S'
              in if rand(concl rthm) = T
                 then let val eqn = mk_eq(x,y)
                          val thm2 = MK_COMB(DISJ (REFL eqn), rthm)
                          val thm3 = TRANS thm2 (INST [gv |-> eqn] OR_T)
                      in TRANS thm thm3
                      end
                 else raise ERR "IN_CONV" ""
              end
        end
        handle HOL_ERR _ => let val _ = check_const empty_tm S in eth end
in
fun IN_CONV conv tm =
 let val (x,S) = dest_in tm
 in if same_const pred_setSyntax.univ_tm S
    then EQT_INTRO (ISPEC x inUNIV)
    else
     let val ith = ISPEC x inI
         val eth = ISPEC x inE
     in in_conv conv (eth,ith) x S
     end
 end
 handle e => raise wrap_exn "PFset_conv" "IN_CONV" e
end;

(* =====================================================================*)
(* DELETE_CONV: delete an element from a finite set.			*)
(*									*)
(* A call to:								*)
(*									*)
(*	DELETE_CONV conv `{x1;...;xn} DELETE x`                         *)
(*									*)
(* returns:								*)
(*									*)
(*	|-{x1;...;xn} DELETE x = {xi;...;xk}				*)
(*									*)
(* where for all xj in {xi,...,xk}, either conv proves |- xj=x or xj is *)
(* syntactically identical to x and for all xj in {x1;...;xn} and NOT in*)
(* {xi;...;xj}, conv proves |- (xj=x)=F.				*)
(* =====================================================================*)

local val bv = genvar bool
      val Dins = GENL [``y:'a``,``x:'a``]
                   (SPECL [``x:'a``,``y:'a``] DELETE_INSERT)
      fun del_conv conv (eth,ith) x S =
        let val (y,S') = dest_insert S
            val thm = SPEC S' (SPEC y ith)
            val eql = if aconv x y
                      then EQT_INTRO (ALPHA y x) else conv (mk_eq(y,x))
            val rthm = del_conv conv (eth,ith) x S'
            val v = genvar (type_of S)
            val pat = mk_eq(lhs(concl thm),mk_cond(bv,v,mk_comb(rator S,v)))
            val thm2 = SUBST [v |-> rthm, bv |-> eql] pat thm
       in TRANS thm2 (COND_CONV (rand(concl thm2)))
       end
       handle HOL_ERR _
        => let val _ = check_const empty_tm S in eth end
in
fun DELETE_CONV conv tm =
  let val (S,x) = dest_delete tm
      val ith = ISPEC x Dins
      and eth = ISPEC x pred_setTheory.EMPTY_DELETE
  in del_conv conv (eth,ith) x S
  end
  handle e => raise wrap_exn "PFset_conv" "DELETE_CONV" e
end;


(* =====================================================================*)
(* UNION_CONV: compute the union of two sets.				*)
(*									*)
(* A call to:								*)
(*									*)
(*	UNION_CONV conv `{x1;...;xn} UNION S`                           *)
(*									*)
(* returns:								*)
(*									*)
(*	|-{x1;...;xn} UNION S = xi INSERT ... (xk INSERT S)		*)
(*									*)
(* where for all xj in {x1;...;xn} but NOT in {xi;...;xk}, IN_CONV conv *)
(* proves that |- xj IN S = T						*)
(* =====================================================================*)

local val Eu = CONJUNCT1 pred_setTheory.UNION_EMPTY
      val bv = genvar bool
      fun itfn conv (ith,iith) x th =
        let val (_,alist) = strip_comb(lhs(concl th))
            val (S,T) = (case alist of [a,b] => (a,b)
                         | otherwise => raise Match)
        in let val eql = IN_CONV conv (mk_in (x,T))
               val thm = SPEC T (SPEC S (SPEC x ith))
               val (lhs,rhs) = dest_eq(concl thm)
               val ins = (rator o rand) rhs
               val v = genvar (type_of S)
               val pat = mk_eq(lhs,mk_cond(bv,v,mk_comb(ins,v)))
               val thm2 = SUBST [v |-> th, bv |-> eql] pat thm
           in
             TRANS thm2 (COND_CONV (rand(concl thm2)))
           end
           handle HOL_ERR _ =>
           let val v = genvar (type_of S)
               val thm = SPEC T (SPEC S (SPEC x iith))
               val (lhs,rhs) = dest_eq(concl thm)
               val r = rator rhs
           in SUBST [v |-> th] (mk_eq(lhs, mk_comb(r,v))) thm
           end
        end
in
fun UNION_CONV conv tm =
 let val (S1,S2) = dest_union tm
     val els = strip_set S1
     val (ty,_) = dom_rng(type_of S1)
     val ith = INST_TYPE [alpha |-> ty] pred_setTheory.INSERT_UNION
     val iith = INST_TYPE [alpha |-> ty] pred_setTheory.INSERT_UNION_EQ
 in
   itlist (itfn conv (ith,iith)) els (ISPEC S2 Eu)
 end
 handle e => raise wrap_exn "PFset_conv" "UNION_CONV" e
end;


(* =====================================================================*)
(* INSERT_CONV: non-redundantly insert a value into a set.		*)
(*									*)
(* A call to:								*)
(*									*)
(*	INSERT_CONV conv `x INSERT S`                                   *)
(*									*)
(* returns:								*)
(*									*)
(*	|- x INSERT S = S						*)
(*									*)
(* if IN_CONV conv proves that |- x IN s = T, otherwise fail.		*)
(*									*)
(* Note that DEPTH_CONV (INSERT_CONV conv) can be used to remove 	*)
(* duplicate elements from a set, but the following conversion is 	*)
(* faster:								*)
(*									*)
(* fun REDUCE_CONV conv tm =						*)
(*    (SUB_CONV (REDUCE_CONV conv) THENC (TRY_CONV (INSERT_CONV conv))) *)
(*    tm;								*)
(* =====================================================================*)

local val absth =
        let val th = pred_setTheory.ABSORPTION
            val th1 = fst(EQ_IMP_RULE
                           (SPECL[``x:'a``,``s:'a->bool``] th))
        in GENL [``x:'a``,``s:'a->bool``] th1
        end
in
fun INSERT_CONV conv tm =
  let val (x,s) = dest_insert tm
      val thm = IN_CONV conv (mk_in (x,s))
  in if rand(concl thm) = boolSyntax.T
       then MP (SPEC s (ISPEC x absth)) (EQT_ELIM thm)
       else raise ERR "INSERT_CONV" "failed"
  end
  handle e => raise wrap_exn "PFset_conv" "INSERT_CONV" e
end;


(* =====================================================================*)
(* IMAGE_CONV: compute the image of a function on a finite set.		*)
(*									*)
(* A call to:								*)
(*									*)
(*	IMAGE_CONV conv iconv `IMAGE f {x1;...;xn}`                     *)
(*									*)
(* returns:								*)
(*									*)
(*	|- IMAGE f {x1;...;xn} = {y1;...;yn}				*)
(*									*)
(* where conv proves |- f xi = yi for all 1<=i<=n.  The conversion also *)
(* trys to use INSERT_CONV iconv to simplify insertion of the results 	*)
(* into the set {y1;...;yn}.						*)
(*									*)
(* =====================================================================*)

local val Ith = pred_setTheory.IMAGE_INSERT
      and Eth = pred_setTheory.IMAGE_EMPTY
      fun iconv IN cnv1 cnv2 ith eth s =
         let val (x,t) = dest_insert s
             val thm1 = SPEC t (SPEC x ith)
             val el = rand(rator(rand(concl thm1)))
             val cth = MK_COMB(AP_TERM IN (cnv1 el),
                               iconv IN cnv1 cnv2 ith eth t)
             val thm2 = QCONV (TRY_CONV (INSERT_CONV cnv2)) (rand(concl cth))
         in TRANS thm1 (TRANS cth thm2)
         end handle HOL_ERR _
             => if same_const empty_tm s then eth
                else raise ERR "IMAGE_CONV.iconv" ""
in
fun IMAGE_CONV conv1 conv2 tm =
  let val (f,s) = dest_image tm
      val (_,ty) = dom_rng(type_of f)
  in
     iconv (inst [alpha |-> ty] insert_tm)
           conv1 conv2 (ISPEC f Ith) (ISPEC f Eth) s
  end
  handle e => raise wrap_exn "PFset_conv" "IMAGE_CONV" e
end;


(*---------------------------------------------------------------------------*)
(* Evaluates terms of the form                                               *)
(*                                                                           *)
(*     CARD {e1; ...; en}                                                    *)
(*---------------------------------------------------------------------------*)

fun CARD_CONV tm =
 let val s = dest_card tm
     val ty = eltype s
     val items = strip_set s
     val CARD_EMPTY' = INST_TYPE [alpha |-> ty] CARD_EMPTY
     val CARD_INSERT' = INST_TYPE [alpha |-> ty] CARD_INSERT
     val FINITE_EMPTY' = INST_TYPE [alpha |-> ty] FINITE_EMPTY
     val FINITE_INSERT' = INST_TYPE [alpha |-> ty] FINITE_INSERT
     fun step x (finthm,cardthm) =
      let val s = dest_finite (concl finthm)
          val finthm' = EQ_MP (SYM (SPEC s (SPEC x FINITE_INSERT'))) finthm
          val cardthm1 = SPEC x (MP (SPEC s CARD_INSERT') finthm)
          val inthm = IN_CONV computeLib.EVAL_CONV (mk_in(x,s))
          val cardthm2 = CONV_RULE (RHS_CONV
             (REWRITE_CONV [inthm,cardthm] THENC reduceLib.SUC_CONV)) cardthm1
      in (finthm', cardthm2)
      end
     val (fin,card) = itlist step items (FINITE_EMPTY',CARD_EMPTY')
 in
  card
 end;


(*---------------------------------------------------------------------------*)
(* Evaluates terms of the form                                               *)
(*                                                                           *)
(*     MAX_SET {n1; ...; nk}                                                 *)
(*---------------------------------------------------------------------------*)

local open numSyntax
      val MAX_SET_SING = CONJUNCT1 MAX_SET_THM
      val MAX_SET_THM' = CONJUNCT2 MAX_SET_THM
      val FINITE_EMPTY' = INST_TYPE [alpha |-> num] FINITE_EMPTY
      val FINITE_INSERT' = INST_TYPE [alpha |-> num] FINITE_INSERT
in
fun MAX_SET_CONV tm  =
 let open numSyntax
     val s = dest_max_set tm
     val items = strip_set s
     val (front,b) = front_last items
     val FINITE_SING = EQ_MP(SYM(SPEC (mk_empty num) (SPEC b FINITE_INSERT')))
                            (INST_TYPE [alpha |-> num] FINITE_EMPTY)
     fun step x (finthm,maxthm) =
      let val ys = dest_max_set (lhs (concl maxthm))
          val (y,s) = dest_insert ys
          val finthm' = EQ_MP (SYM (SPEC s (SPEC y FINITE_INSERT'))) finthm
          val maxthm1 = SPEC y (SPEC x (MP (SPEC s MAX_SET_THM') finthm))
          val maxthm2 = CONV_RULE (RHS_CONV
                (RAND_CONV (REWR_CONV maxthm) THENC computeLib.EVAL_CONV)) maxthm1
      in (finthm', maxthm2)
      end
     val (fin,maxthm) = itlist step front (FINITE_EMPTY',SPEC b MAX_SET_SING)
 in
  maxthm
 end
 handle e => raise wrap_exn "MAX_SET_CONV" "" e
end;


(*---------------------------------------------------------------------------*)
(* Evaluates terms of the form                                               *)
(*                                                                           *)
(*     SUM_IMAGE f {e1; ...; ek}                                             *)
(*---------------------------------------------------------------------------*)

local val SIGMA_EMPTY = CONJUNCT1 (SPEC_ALL SUM_IMAGE_THM)
      val SIGMA_INSERT =
          SUM_IMAGE_THM
              |> SPEC_ALL
              |> CONJUNCT2
              |> SPEC_ALL
              |> UNDISCH_ALL
              |> REWRITE_RULE [SUM_IMAGE_DELETE |> SPEC_ALL |> UNDISCH_ALL]
              |> DISCH_ALL
              |> GEN (mk_var("e", alpha))
              |> GEN (mk_var("s", alpha --> bool))
              |> GEN (mk_var("f", alpha --> numSyntax.num))
in
fun SUM_IMAGE_CONV tm =
 let open numSyntax
     val (f,s) = dest_sum_image tm
     val ty = eltype s
     val items = strip_set s
     val FINITE_EMPTY' = INST_TYPE [alpha |-> ty] FINITE_EMPTY
     val FINITE_INSERT' = INST_TYPE [alpha |-> ty] FINITE_INSERT
     val SIGMA_EMPTY' = INST_TYPE [alpha |-> ty] SIGMA_EMPTY
     val SIGMA_INSERT' = ISPEC f SIGMA_INSERT
     fun step x (finthm,sumthm) =
      let val s = dest_finite (concl finthm)
          val finthm' = EQ_MP (SYM (SPEC s (SPEC x FINITE_INSERT'))) finthm
          val sumthm1 = MP (SPEC x (SPEC s SIGMA_INSERT')) finthm
          val inthm = IN_CONV computeLib.EVAL_CONV (mk_in(x,s))
          val sumthm2 = CONV_RULE (RHS_CONV
              (RAND_CONV (REWRITE_CONV [inthm,sumthm])
                          THENC computeLib.EVAL_CONV)) sumthm1
      in (finthm', sumthm2)
      end
     val (fin,sum) = itlist step items (FINITE_EMPTY',SIGMA_EMPTY')
 in
  sum
 end
end;

end (* PFset_conv *)
