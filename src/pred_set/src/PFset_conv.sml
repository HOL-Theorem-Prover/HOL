(* =====================================================================*)
(* FILE		: fset_conv.ml						*)
(* DESCRIPTION   : Conversions for taking unions and intersections of 	*)
(*		  finite sets, for deciding membership of finite sets,  *)
(*		  and so on.						*)
(*								        *)
(* REWRITTEN     : T Melham						*)
(* DATE		: 90.10.16 (adapted for pred_set: January 1992)	*)
(* TRANSLATED to hol90 February 1993 by kls                             *)
(* =====================================================================*)

structure PFset_conv :> PFset_conv =
struct

type conv = Abbrev.conv;
open HolKernel Parse boolTheory boolSyntax Drule Conv;
infix ## |->;

fun FSET_CONV_ERR{function,message} =
          HOL_ERR{origin_structure = "Fset_conv",
                  origin_function = function,
                  message = message};

fun check st = assert (fn c => #Name(dest_const c) = st)

(* =====================================================================*)
(* FINITE_CONV: prove that a normal-form finite set is finite.  The set *)
(* in question must have the standard form:				*)
(*									*)
(*	INSERT x1 (INSERT x2 ...(INSERT xn EMPTY)... ))	 		*)
(*									*)
(* A call to:								*)
(*									*)
(*	FINITE_CONV (--`{x1,...,xn}`--) 				*)
(*									*)
(* returns:								*)
(*									*)
(*       |- FINITE {x1,...,xn} = T					*)
(*									*)
(* The conversion fails on sets of the wrong form.			*)
(* ---------------------------------------------------------------------*)

local exception FAIL
      val finE = pred_setTheory.FINITE_EMPTY
val finI =
   let val th1 =  pred_setTheory.FINITE_INSERT
       val th2 = snd(EQ_IMP_RULE(SPECL[(--`x:'a`--),(--`s:'a->bool`--)] th1))
   in GEN (--`s:'a->bool`--)
          (DISCH_ALL (GEN (--`x:'a`--) (UNDISCH th2)))
   end
fun strip_set tm =
   let val (_,[h,t]) = (check "INSERT" ## I)(strip_comb tm)
   in (h::strip_set t)
   end handle _ => if (#Name(dest_const tm) = "EMPTY")
                   then []
                   else raise FAIL
fun itfn ith x th = SPEC x (MP (SPEC (rand(concl th)) ith) th)
in
fun FINITE_CONV tm =
   let val {Rator,Rand} = dest_comb tm
       val _ = check "FINITE" Rator
       val els = strip_set Rand
       val {Args = [ty,_],...} = dest_type (type_of(rand tm))
       val theta = [{redex = Type.alpha, residue = ty}]
       val eth = INST_TYPE theta finE
       val ith = INST_TYPE theta finI
   in EQT_INTRO (itlist (itfn ith) els eth)
   end handle  _ => raise FSET_CONV_ERR{function = "FINITE_CONV",message = ""}
end;

(* =====================================================================*)
(* IN_CONV: decide membership for finite sets.				*)
(*									*)
(* A call to:								*)
(*									*)
(*	IN_CONV conv (--`x IN {x1,...,xn}`--)				*)
(*									*)
(* returns:								*)
(*									*)
(*	|- x IN {x1,...,xn} = T						*)
(*									*)
(* if x is syntactically identical to xi for some i, where 1<=i<=n, or	*)
(* if conv proves |- (x=xi)=T for some i, where 1<=i<=n, or it returns:	*)
(*									*)
(*	|- x IN {x1,...,xn} = F						*)
(*									*)
(* if conv proves |- (x=xi)=F for all 1<=i<=n.				*)
(* =====================================================================*)

local
val inI = pred_setTheory.IN_INSERT
val inE = GEN (--`x:'a`--)
              (EQF_INTRO (SPEC (--`x:'a`--)
                               (pred_setTheory.NOT_IN_EMPTY)))
val T = (--`T`--)
and F = (--`F`--)
and gv = genvar Type.bool
val DISJ = AP_TERM (--`$\/`--)
val F_OR = el 3 (CONJUNCTS (SPEC gv OR_CLAUSES))
val OR_T = el 2 (CONJUNCTS (SPEC gv OR_CLAUSES))
fun in_conv conv (eth,ith) x S =
   let val (_,[y,S']) = (check "INSERT" ## I) (strip_comb S)
       val thm = SPEC S' (SPEC y ith)
       val rectm = rand(rand(concl thm))
   in
   if (aconv x y)
   then EQT_INTRO (EQ_MP (SYM thm) (DISJ1 (ALPHA x y) rectm))
   else let val eql = conv (mk_eq {lhs=x, rhs=y})
            val res = rand(concl eql)
        in
        if (res=T)
        then EQT_INTRO (EQ_MP (SYM thm) (DISJ1 (EQT_ELIM eql) rectm))
        else if (res=F)
             then let val rthm = in_conv conv (eth,ith) x S'
                      val thm2 = MK_COMB (DISJ eql,rthm)
	              val thm3 = INST[{redex=gv,residue=rand(concl rthm)}]F_OR
                  in TRANS thm (TRANS thm2 thm3)
                  end
             else raise FSET_CONV_ERR{function = "in_conv",message=""}
        end
        handle _ => let val rthm = in_conv conv (eth,ith) x S'
                    in if (rand(concl rthm)=T)
                       then let val eqn = mk_eq{lhs=x,rhs=y}
                                val thm2 = MK_COMB(DISJ (REFL eqn), rthm)
                                val thm3 = TRANS thm2
                                                 (INST [{redex=gv,residue=eqn}]
                                                       OR_T)
                            in TRANS thm thm3
                            end
                       else raise FSET_CONV_ERR{function="in_conv",message=""}
                    end
   end handle _ => let val e = check "EMPTY" S
                   in eth
                   end
in
fun IN_CONV conv tm =
   let val (_,[x,S]) = (check "IN" ## I) (strip_comb tm)
       val ith = ISPEC x inI
       and eth = ISPEC x inE
   in in_conv conv (eth,ith) x S
   end handle _ => raise FSET_CONV_ERR{function="IN_CONV",message=""}
end;

(* =====================================================================*)
(* DELETE_CONV: delete an element from a finite set.			*)
(*									*)
(* A call to:								*)
(*									*)
(*	DELETE_CONV conv (--`{x1,...,xn} DELETE x`--)			*)
(*									*)
(* returns:								*)
(*									*)
(*	|-{x1,...,xn} DELETE x = {xi,...,xk}				*)
(*									*)
(* where for all xj in {xi,...,xk}, either conv proves |- xj=x or xj is *)
(* syntactically identical to x and for all xj in {x1,...,xn} and NOT in*)
(* {xi,...,xj}, conv proves |- (xj=x)=F.				*)
(* =====================================================================*)

local val bv = genvar Type.bool
      val Edel = pred_setTheory.EMPTY_DELETE
       val Dins = GENL [(--`y:'a`--),(--`x:'a`--)]
                 (SPECL [(--`x:'a`--),(--`y:'a`--)]
                       (pred_setTheory.DELETE_INSERT))
fun del_conv conv (eth,ith) x S =
   let val (_,[y,S']) = (check "INSERT" ## I) (strip_comb S)
       val thm = SPEC S' (SPEC y ith)
       val eql = if (aconv x y)
                 then EQT_INTRO (ALPHA y x)
                 else conv (mk_eq{lhs=y,rhs=x})
       val rthm = del_conv conv (eth,ith) x S'
       val v = genvar (type_of S)
       val pat = mk_eq{lhs=lhs(concl thm),
                       rhs=mk_cond{cond=bv,
                                   larm=v,
                                   rarm=mk_comb{Rator=rator S,Rand=v}}}
       val thm2 = SUBST [v |-> rthm, bv |-> eql] pat thm
   in TRANS thm2 (COND_CONV (rand(concl thm2)))
   end handle _ => let val _ = check "EMPTY" S
                   in eth
                   end
in
fun DELETE_CONV conv tm =
   let val (_,[S,x]) = (check "DELETE" ## I) (strip_comb tm)
       val ith = ISPEC x Dins
       and eth = ISPEC x Edel
   in del_conv conv (eth,ith) x S
   end handle _ => raise FSET_CONV_ERR{function="DELETE_CONV",message=""}
end;


(* =====================================================================*)
(* UNION_CONV: compute the union of two sets.				*)
(*									*)
(* A call to:								*)
(*									*)
(*	UNION_CONV conv (--`{x1,...,xn} UNION S`--)			*)
(*									*)
(* returns:								*)
(*									*)
(*	|-{x1,...,xn} UNION S = xi INSERT ... (xk INSERT S)		*)
(*									*)
(* where for all xj in {x1,...,xn} but NOT in {xi,...,xk}, IN_CONV conv *)
(* proves that |- xj IN S = T						*)
(* =====================================================================*)

local
val InU  = pred_setTheory.INSERT_UNION
val InUE = pred_setTheory.INSERT_UNION_EQ
val Eu  = CONJUNCT1 (pred_setTheory.UNION_EMPTY)
fun strip_set tm =
   let val [h,t] = snd ((check "INSERT" ## I) (strip_comb tm))
   in (h::strip_set t)
   end
   handle _ => if (#Name(dest_const tm) = "EMPTY")
               then []
               else raise FSET_CONV_ERR{function="UNION_CONV.strip_set",
                                        message =""}
fun mkIN x s =
   let val ty = type_of x
       fun fun_ty ty1 ty2 = mk_type{Tyop="fun",Args=[ty1,ty2]}
       val sty = fun_ty ty Type.bool
       val INty = fun_ty ty (fun_ty sty Type.bool)
   in mk_comb{Rator=mk_comb{Rator=mk_const{Name="IN",Ty=INty},
                            Rand=x}, Rand=s}
   end
val bv = genvar Type.bool
fun itfn conv (ith,iith) x th =
   let val (_,[S,T]) = strip_comb(lhs(concl th))
       val eql = IN_CONV conv (mkIN x T)
       val thm = SPEC T (SPEC S (SPEC x ith))
       val {lhs,rhs} = dest_eq(concl thm)
       val ins = (rator o rand) rhs
       val v = genvar (type_of S)
       val pat = mk_eq{lhs = lhs,
                       rhs = mk_cond{cond=bv,larm=v,
                                     rarm=mk_comb{Rator=ins,Rand=v}}}
       val thm2 = SUBST [v |->th, bv |-> eql] pat thm
   in
   TRANS thm2 (COND_CONV (rand(concl thm2)))
   handle _
   => let val v = genvar (type_of S)
          val thm = SPEC T (SPEC S (SPEC x iith))
          val {lhs,rhs} = dest_eq(concl thm)
          val r = rator rhs
      in SUBST [v |->th] (mk_eq{lhs=lhs, rhs=mk_comb{Rator=r,Rand=v}}) thm
      end
   end
in
fun UNION_CONV conv tm =
   let val (_,[S1,S2]) = (check "UNION" ## I) (strip_comb tm)
       val els = strip_set S1
       val ty = hd(#Args(dest_type(type_of S1)))
       val ith = INST_TYPE [{redex=Type.alpha,residue=ty}] InU
       val iith = INST_TYPE [{redex=Type.alpha,residue=ty}] InUE
   in
   itlist (itfn conv (ith,iith)) els (ISPEC S2 Eu)
   end
   handle _ => raise FSET_CONV_ERR{function="UNION_CONV",message=""}
end;


(* =====================================================================*)
(* INSERT_CONV: non-redundantly insert a value into a set.		*)
(*									*)
(* A call to:								*)
(*									*)
(*	INSERT_CONV conv (--`x INSERT S`--)				*)
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

local
val absth =
   let val th = pred_setTheory.ABSORPTION
       val th1 = fst(EQ_IMP_RULE(SPECL[(--`x:'a`--),(--`s:'a->bool`--)] th))
   in GENL [(--`x:'a`--),(--`s:'a->bool`--)] th1
   end
fun mkIN x s =
   let val ty = type_of x
       val sty = mk_type{Tyop="fun",Args=[ty,Type.bool]}
       val INty = mk_type{Tyop="fun",
                          Args=[ty,mk_type{Tyop="fun",Args=[sty,Type.bool]}]}
   in mk_comb{Rator=mk_comb{Rator=mk_const{Name="IN",Ty=INty},Rand=x},Rand=s}
   end
val T = (--`T`--)
fun isT thm = rand(concl thm)=T
in
fun INSERT_CONV conv tm =
   let val (_,[x,s]) = (check "INSERT" ## I) (strip_comb tm)
       val thm = IN_CONV conv (mkIN x s)
   in
   if (isT thm)
   then MP (SPEC s (ISPEC x absth))
           (EQT_ELIM thm)
   else raise FSET_CONV_ERR{function="",message=""}
   end
   handle _ => raise FSET_CONV_ERR{function="INSERT_CONV",message=""}
end;


(* =====================================================================*)
(* IMAGE_CONV: compute the image of a function on a finite set.		*)
(*									*)
(* A call to:								*)
(*									*)
(*	IMAGE_CONV conv iconv (--`IMAGE f {x1,...,xn}`--)		*)
(*									*)
(* returns:								*)
(*									*)
(*	|- IMAGE f {x1,...,xn} = {y1,...,yn}				*)
(*									*)
(* where conv proves |- f xi = yi for all 1<=i<=n.  The conversion also *)
(* trys to use INSERT_CONV iconv to simplify insertion of the results 	*)
(* into the set {y1,...,yn}.						*)
(*									*)
(* =====================================================================*)


local
val Ith = pred_setTheory.IMAGE_INSERT
and Eth = pred_setTheory.IMAGE_EMPTY
fun iconv IN cnv1 cnv2 ith eth s =
   let val (_,[x,t]) = (check "INSERT" ## I) (strip_comb s)
       val thm1 = SPEC t (SPEC x ith)
       val el = rand(rator(rand(concl thm1)))
       val cth = MK_COMB(AP_TERM IN (cnv1 el),iconv IN cnv1 cnv2 ith eth t)
       val thm2 = TRY_CONV (INSERT_CONV cnv2) (rand(concl cth))
   in TRANS thm1 (TRANS cth thm2)
   end handle _ => if (#Name(dest_const s) = "EMPTY")
                   then eth
                   else raise FSET_CONV_ERR{function="IMAGE_CONV.iconv",
                                            message=""}
in
fun IMAGE_CONV conv1 conv2 tm =
   let val (_,[f,s]) = (check "IMAGE" ## I) (strip_comb tm)
       val {Args=[_,ty],...} = dest_type(type_of f)
       val sty = mk_type{Tyop="fun",Args=[ty,Type.bool]}
       val INty = mk_type{Tyop="fun",
                          Args=[ty,mk_type{Tyop="fun",Args=[sty,sty]}]}
       val IN = mk_const{Name="INSERT", Ty=INty}
   in
   iconv IN conv1 conv2 (ISPEC f Ith) (ISPEC f Eth) s
   end handle _ => raise FSET_CONV_ERR{function="IMAGE_CONV",message=""}
end;


end; (* Fset_conv *)
