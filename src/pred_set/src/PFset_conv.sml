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

open HolKernel Parse boolLib;
infix ## |->;
infixr -->;

fun FSET_CONV_ERR{function,message} =
          HOL_ERR{origin_structure = "Fset_conv",
                  origin_function = function,
                  message = message};

fun check_const (s,thy) = 
  assert (fn c => 
           let val {Name, Thy, ...} = dest_thy_const c
           in s=Name andalso thy=Thy
           end handle HOL_ERR _ => false);


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
                val th2 = snd(EQ_IMP_RULE
                              (SPECL[(--`x:'a`--),(--`s:'a->bool`--)] th1))
        in GEN (--`s:'a->bool`--)
            (DISCH_ALL (GEN (--`x:'a`--) (UNDISCH th2)))
        end
      fun strip_set tm =
          let val (_,[h,t]) = (check_const ("INSERT","pred_set")##I)
                              (strip_comb tm)
          in (h::strip_set t)
          end handle _ => 
            let val {Name,Thy,...} = dest_thy_const tm
            in if Name= "EMPTY" andalso Thy="pred_set" then [] else raise FAIL
            end
      fun itfn ith x th = SPEC x (MP (SPEC (rand(concl th)) ith) th)
in
fun FINITE_CONV tm =
   let val (Rator,Rand) = dest_comb tm
       val _ = check_const ("FINITE","pred_set") Rator
       val els = strip_set Rand
       val [ty,_] = snd(dest_type (type_of(rand tm)))
       val theta = [alpha |-> ty]
       val eth = INST_TYPE theta finE
       val ith = INST_TYPE theta finI
   in EQT_INTRO (itlist (itfn ith) els eth)
   end 
   handle e => raise (wrap_exn "PFset_conv" "FINITE_CONV" e)
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

local val inI = pred_setTheory.IN_INSERT
      val inE = GEN (--`x:'a`--)
                 (EQF_INTRO (SPEC (--`x:'a`--) pred_setTheory.NOT_IN_EMPTY))
      val gv = genvar bool
      val DISJ = AP_TERM boolSyntax.disjunction
      val F_OR = el 3 (CONJUNCTS (SPEC gv OR_CLAUSES))
      val OR_T = el 2 (CONJUNCTS (SPEC gv OR_CLAUSES))
      fun in_conv conv (eth,ith) x S =
        let val (_,[y,S']) = (check_const ("INSERT","pred_set") ## I) 
                             (strip_comb S)
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
              else raise FSET_CONV_ERR{function = "in_conv",message=""}
             end
             handle HOL_ERR _ => 
              let val rthm = in_conv conv (eth,ith) x S'
              in if rand(concl rthm) = T
                 then let val eqn = mk_eq(x,y)
                          val thm2 = MK_COMB(DISJ (REFL eqn), rthm)
                          val thm3 = TRANS thm2 (INST [gv |-> eqn] OR_T)
                      in TRANS thm thm3
                      end
                 else raise FSET_CONV_ERR{function="in_conv",message=""}
              end
        end 
        handle HOL_ERR _ => 
          let val e = check_const ("EMPTY","pred_set") S
          in eth 
          end
in
fun IN_CONV conv tm =
 let val (_,[x,S]) = (check_const ("IN","pred_set") ## I) (strip_comb tm)
     val ith = ISPEC x inI
     and eth = ISPEC x inE
 in in_conv conv (eth,ith) x S
 end handle e => raise (wrap_exn "PFset_conv" "IN_CONV" e)
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

local val bv = genvar bool
      val Edel = pred_setTheory.EMPTY_DELETE
      val Dins = GENL [(--`y:'a`--),(--`x:'a`--)]
                   (SPECL [(--`x:'a`--),(--`y:'a`--)] 
                          pred_setTheory.DELETE_INSERT)
      fun del_conv conv (eth,ith) x S =
        let val (_,[y,S']) = (check_const ("INSERT","pred_set") ## I)
                             (strip_comb S)
            val thm = SPEC S' (SPEC y ith)
            val eql = if aconv x y
                      then EQT_INTRO (ALPHA y x) else conv (mk_eq(y,x))
            val rthm = del_conv conv (eth,ith) x S'
            val v = genvar (type_of S)
            val pat = mk_eq(lhs(concl thm),mk_cond(bv,v,mk_comb(rator S,v)))
            val thm2 = SUBST [v |-> rthm, bv |-> eql] pat thm
       in TRANS thm2 (COND_CONV (rand(concl thm2)))
       end 
       handle HOL_ERR _ => 
          let val _ = check_const ("EMPTY","pred_set") S 
          in eth end
in
fun DELETE_CONV conv tm =
  let val (_,[S,x]) = (check_const ("DELETE","pred_set") ## I) (strip_comb tm)
      val ith = ISPEC x Dins
      and eth = ISPEC x Edel
  in del_conv conv (eth,ith) x S
  end 
  handle e => raise (wrap_exn "PFset_conv" "DELETE_CONV" e)
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

local val InU  = pred_setTheory.INSERT_UNION
      val InUE = pred_setTheory.INSERT_UNION_EQ
      val Eu  = CONJUNCT1 (pred_setTheory.UNION_EMPTY)
      fun strip_set tm =
        let val [h,t] = snd ((check_const ("INSERT","pred_set") ## I) 
                             (strip_comb tm))
        in (h::strip_set t)
        end handle HOL_ERR _ => 
         let val {Name,Thy,...} = dest_thy_const tm
         in if Name="EMPTY" andalso Thy="pred_set" then []
            else raise FSET_CONV_ERR{function="UNION_CONV.strip_set",
                                     message=""}
         end
      fun mkIN x s =
        let val ty = type_of x
           val INty = ty --> (ty --> bool) --> bool
        in list_mk_comb(mk_thy_const{Name="IN",Thy="pred_set",Ty=INty},[x,s])
        end
      val bv = genvar bool
      fun itfn conv (ith,iith) x th =
        let val (_,[S,T]) = strip_comb(lhs(concl th))
            val eql = IN_CONV conv (mkIN x T)
            val thm = SPEC T (SPEC S (SPEC x ith))
            val (lhs,rhs) = dest_eq(concl thm)
            val ins = (rator o rand) rhs
            val v = genvar (type_of S)
            val pat = mk_eq(lhs,mk_cond(bv,v,mk_comb(ins,v)))
            val thm2 = SUBST [v |->th, bv |-> eql] pat thm
        in TRANS thm2 (COND_CONV (rand(concl thm2)))
           handle HOL_ERR _ =>
               let val v = genvar (type_of S)
                   val thm = SPEC T (SPEC S (SPEC x iith))
                   val (lhs,rhs) = dest_eq(concl thm)
                   val r = rator rhs
               in SUBST [v |->th] (mk_eq(lhs, mk_comb(r,v))) thm
               end
        end
in
fun UNION_CONV conv tm =
 let val (_,[S1,S2]) = (check_const ("UNION","pred_set") ## I) (strip_comb tm)
     val els = strip_set S1
     val ty = hd(snd(dest_type(type_of S1)))
     val ith = INST_TYPE [alpha |-> ty] InU
     val iith = INST_TYPE [alpha |-> ty] InUE
 in
   itlist (itfn conv (ith,iith)) els (ISPEC S2 Eu)
 end
 handle e => raise (wrap_exn "PFset_conv" "UNION_CONV" e)
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

local val absth =
        let val th = pred_setTheory.ABSORPTION
            val th1 = fst(EQ_IMP_RULE
                       (SPECL[(--`x:'a`--),(--`s:'a->bool`--)] th))
        in GENL [(--`x:'a`--),(--`s:'a->bool`--)] th1
        end
      fun mkIN x s =
         let val ty = type_of x
             val sty = ty --> bool
             val INty = ty --> (ty --> bool) --> bool
         in list_mk_comb(mk_thy_const{Name="IN",Thy="pred_set",Ty=INty},[x,s])
         end
in
fun INSERT_CONV conv tm =
  let val (_,[x,s]) = (check_const ("INSERT","pred_set") ## I) (strip_comb tm)
      val thm = IN_CONV conv (mkIN x s)
  in if rand(concl thm)=T
     then MP (SPEC s (ISPEC x absth)) (EQT_ELIM thm)
     else raise FSET_CONV_ERR{function="INSERT_CONV",message="failed"}
  end
  handle e => raise (wrap_exn "PFset_conv" "INSERT_CONV" e)
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


local val Ith = pred_setTheory.IMAGE_INSERT
      and Eth = pred_setTheory.IMAGE_EMPTY
      fun iconv IN cnv1 cnv2 ith eth s =
         let val (_,[x,t]) = (check_const ("INSERT","pred_set") ## I) 
                             (strip_comb s)
             val thm1 = SPEC t (SPEC x ith)
             val el = rand(rator(rand(concl thm1)))
             val cth = MK_COMB(AP_TERM IN (cnv1 el),
                               iconv IN cnv1 cnv2 ith eth t)
             val thm2 = TRY_CONV (INSERT_CONV cnv2) (rand(concl cth))
         in TRANS thm1 (TRANS cth thm2)
         end handle HOL_ERR _ => 
              let val {Name,Thy,...} = dest_thy_const s
              in if Name="EMPTY" andalso Thy="pred_set" then eth
                 else raise FSET_CONV_ERR{function="IMAGE_CONV.iconv",
                                          message=""}
              end
in
fun IMAGE_CONV conv1 conv2 tm =
  let val (_,[f,s]) = (check_const ("IMAGE","pred_set") ## I) (strip_comb tm)
      val [_,ty] = snd(dest_type(type_of f))
      val sty = ty --> bool
      val INty = ty --> sty --> sty
      val IN = mk_thy_const{Name="INSERT", Thy="pred_set", Ty=INty}
  in
     iconv IN conv1 conv2 (ISPEC f Ith) (ISPEC f Eth) s
  end 
  handle e => raise (wrap_exn "PFset_conv" "IMAGE_CONV" e)
end;


end; (* PFset_conv *)
