(* =====================================================================*)
(* FILE          : ConstrProofs.sml                                     *)
(* DESCRIPTION   : Derived rules of inference that are useful for the   *)
(*                 concrete recursive types built by define_type.       *)
(*                 Translated from hol88.                               *)
(*                                                                      *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                  *)
(* DATE          : September 15, 1991                                   *)
(* =====================================================================*)


structure ConstrProofs :> ConstrProofs =
struct


local open numTheory pairTheory in end;

open HolKernel Parse Conv Drule Prim_rec boolTheory;

fun ERR{function,message} =
      HOL_ERR{origin_structure = "ConstrProofs",
	      origin_function = function,
	      message = message}
infix |-> ##;
infixr 3 ==;
infixr 3 ==>;
infixr 3 /\;
infixr 3 \/;

fun (x == y)  = mk_eq{lhs=x,    rhs=y};
fun (x ==> y) = mk_imp{ant=x, conseq=y}
fun (x /\ y)  = mk_conj{conj1=x, conj2=y};
fun (x \/ y)  = mk_disj{disj1=x, disj2=y};

val SUC  = Term`SUC`
(* and zero = Term.mk_numeral arbnum.zero; *)
and zero = Term`ZERO`;
val NOT_SUC  = numTheory.NOT_SUC
and INV_SUC  = numTheory.INV_SUC
val PAIR_EQ' = pairTheory.PAIR_EQ;


(* =====================================================================*)
(* PROOF THAT CONSTRUCTORS OF RECURSIVE TYPES ARE ONE-TO-ONE		*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Internal function: PAIR_EQ_CONV 					*)
(*									*)
(* A call to PAIR_EQ_CONV "(x1,...,xn) = (y1,...,yn)" returns:		*)
(*									*)
(*   |- ((x1,...,xn) = (y1,...,yn)) = (x1 = y1) /\ ... /\ (xn = yn)	*)
(* 									*)
(* ---------------------------------------------------------------------*)
local val PAIR_EQ = GENL (rev(free_vars (concl PAIR_EQ'))) PAIR_EQ'
      val v = genvar (Type.bool)
in
fun PAIR_EQ_CONV tm =
   let val {lhs,rhs} = dest_eq tm
       val {fst=x, snd=xs} = dest_pair lhs
       val {fst=y, snd=ys} = dest_pair rhs
       val thm = INST_TYPE [alpha |-> type_of x, beta |-> type_of xs] PAIR_EQ
       val spec = SPEC ys (SPEC y (SPEC xs (SPEC x thm)))
       val reqn = PAIR_EQ_CONV (xs==ys)
   in SUBST [v |-> reqn] (tm == ((x==y) /\ v)) spec
   end
   handle HOL_ERR _ => (REFL tm)
end;


(* ---------------------------------------------------------------------*)
(* Internal function: list_variant					*)
(*									*)
(* makes variants of the variables in l2 such that they are all not in	*)
(* l1 and are all different.						*)
(* ---------------------------------------------------------------------*)
fun list_variant l1 [] = []
  | list_variant l1 (h::t) =
       let val v = variant l1 h
       in v::(list_variant (v::l1) t)
       end;

fun mk_subst2 [] [] = []
  | mk_subst2 (a::L1) (b::L2) = (b |-> a)::mk_subst2 L1 L2;


(* ----------------------------------------------------------------------*)
(* Internal function: prove_const_one_one.				 *)
(*									 *)
(* This function proves that a single constructor of a recursive type is *)
(* one-to-one (it is called once for each appropriate constructor). The  *)
(* theorem input, th, is the characterizing theorem for the recursive 	 *)
(* type in question.  The term, tm, is the defining equation for the 	 *)
(* constructor in question, taken from the body of the theorem th.	 *)
(*									 *)
(* For example, if:							 *)
(*									 *)
(*  th = |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) *)
(*									 *)
(* and									 *)
(*									 *)
(*  tm = "!h t. fn(CONS h t) = f(fn t)h t"				 *)
(*									 *)
(* then prove_const_one_one th tm yields:				 *)
(*								 	 *)
(*  |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t')	 *)
(*									 *)
(* ----------------------------------------------------------------------*)

fun prove_const_one_one th tm =
   let val (vs,{lhs,...}) = (I ## dest_eq)(strip_forall tm)
       val C = rand lhs
       fun mk_pair_curried p0 p1 = mk_pair{fst = p0, snd = p1}
       val tup = end_itlist mk_pair_curried (snd(strip_comb C))
       val tupty = type_of tup
       val eq = mk_eq{lhs=inst [type_of lhs |-> tupty] lhs, rhs=tup}
       val eqn = prove_rec_fn_exists th eq
       val vvs = list_variant vs vs
       val C' = subst (mk_subst2 vvs vs) C
       val C_eq_C' = (C == C')
       val sndC = snd(strip_comb C)
       val vareqs = list_mk_conj
                      (map2 (fn x => fn y => (x==y)) sndC (snd(strip_comb C')))
       val asms = map2 (fn th => fn v => (v |-> th))
                       (CONJUNCTS (ASSUME vareqs)) sndC
       val imp1 = DISCH vareqs (SUBST_CONV asms C C)
       val {Bvar,Body} = dest_exists(concl eqn)
       val fndef = ASSUME Body
       val r1 = REWR_CONV fndef (mk_comb{Rator=Bvar,Rand=C})
       and r2 = REWR_CONV fndef (mk_comb{Rator=Bvar,Rand=C'})
       and asm = AP_TERM Bvar (ASSUME C_eq_C')
       and v1 = genvar tupty
       and v2 = genvar tupty
       val thm  = SUBST [v1 |-> r1, v2 |-> r2] (v1==v2) asm
       val aimp = DISCH C_eq_C' (CONV_RULE PAIR_EQ_CONV thm)
       val imp2 = CHOOSE (Bvar,eqn) aimp
   in
     GENL vs (GENL vvs (IMP_ANTISYM_RULE imp2 imp1))
   end;

(* ----------------------------------------------------------------------*)
(* prove_constructors_one_one : prove that the constructors of a given	 *)
(* concrete recursive type are one-to-one. The input is a theorem of the *)
(* form returned by define_type.					 *)
(*									 *)
(* EXAMPLE: 								 *)
(*									 *)
(* Input: 								 *)
(* 									 *)
(*    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	 *)
(*									 *)
(* Output:								 *)
(*									 *)
(*    |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t')	 *)
(* ----------------------------------------------------------------------*)

fun prove_constructors_one_one th =
 let val eqns =
        strip_conj (#Body(dest_abs(rand(snd(strip_forall(concl th))))))
     val funs = gather (fn tm => is_comb(rand(lhs(snd(strip_forall tm)))))
                         eqns
   in
      LIST_CONJ (map (prove_const_one_one th) funs)
   end
   handle HOL_ERR _ =>
   raise ERR{function="prove_constructors_one_one",message = ""};


(* =====================================================================*)
(* DISTINCTNESS OF VALUES FOR EACH CONSTRUCTOR				*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* prove_constructors_distinct : prove that the constructors of a given	*)
(* recursive type yield distinct (non-equal) values.			*)
(*									*)
(* EXAMPLE: 								*)
(*									*)
(* Input: 								*)
(* 									*)
(*    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	*)
(* 									*)
(* Output:								*)
(* 									*)
(*    |- !h t. ~([] = CONS h t)						*)
(* ---------------------------------------------------------------------*)

local val lemma = GEN_ALL(NOT_ELIM(NOT_EQ_SYM(SPEC_ALL NOT_SUC)))
      fun geneqs (h::rst) t =
         let val (vars,{lhs,...}) = (I ## dest_eq) (strip_forall h)
             val new_lhs = mk_eq{lhs=lhs, rhs=t}
         in if (null rst) then ([],new_lhs)
            else let val (rl,tm) = geneqs rst (mk_comb{Rator=SUC, Rand=t})
                 in (t::rl, (new_lhs /\ tm))
                 end
         end
      fun step []  = raise ERR{function="step", message="[]"}
        | step [_] = []
        | step (h::rst) =
              let val [l,r] = snd(strip_comb(#ant(dest_imp(concl h))))
                  val th = IMP_TRANS (SPEC r (SPEC l INV_SUC)) h
              in th::step rst
              end
      fun mk_rot [] = []
        | mk_rot ths =  ths::mk_rot (step ths)
      val N = type_of zero
      val gv1 = genvar N
      and gv2 = genvar N
      val pat = (gv1 == gv2) ==> Term`F`
      fun subsfn rul eq eqs [] acc = acc
        | subsfn rul eq (heq::eqrst) (h::t) acc =
            let val vs = free_vars (rand(rhs(concl eq)))
                and nvs = free_vars (rand(rhs(concl heq)))
                val eqn = INST (mk_subst2 (list_variant vs nvs) nvs) heq
                val rnum = rhs(#ant(dest_imp(concl h)))
                val thm = SUBST [gv1 |-> eq, gv2 |-> eqn] pat h
            in
               rul thm::subsfn rul eq eqrst t acc
            end
      fun subs rul _ [] = []
        | subs rul (eq::eqs) (h::t) = subsfn rul eq eqs h (subs rul eqs t)
in
fun prove_constructors_distinct th =
   let val {Bvar,Body} = dest_abs(rand(snd(strip_forall(concl th))))
       val {Args = [_,ty],...} = dest_type(type_of Bvar)
   in
   case strip_conj (inst[ty |-> N] Body)
    of []  => raise ERR{function="", message=""}
     | [_] => raise ERR{function="", message=""}
     | eqns =>
        let val (nums,eqs) = geneqs eqns zero
            val eth = prove_rec_fn_exists th eqs
            val rots = mk_rot (map (C SPEC lemma) nums)
            val {Bvar, Body=asm} = dest_exists(concl eth)
            val fneqs = map (SYM o SPEC_ALL) (CONJUNCTS (ASSUME asm))
            fun rule th =
              let val {lhs,rhs} = dest_eq(#ant(dest_imp(concl th)))
                  val asm = (rand lhs == rand rhs)
                  val imp = IMP_TRANS(DISCH asm (AP_TERM Bvar (ASSUME asm))) th
              in
               GEN_ALL (NOT_INTRO(CHOOSE (Bvar,eth) imp))
              end
        in
          LIST_CONJ (subs rule fneqs rots)
        end
   end
   handle HOL_ERR _ =>
   raise ERR{function="prove_constructors_distinct", message=""}
end;

end; (* ConstrProofs *)
