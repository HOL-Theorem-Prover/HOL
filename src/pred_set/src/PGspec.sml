(* =====================================================================*)
(* FILE		: gspec.ml						*)
(* DESCRIPTION  : Generalized set specification : {tm[xi...xn] | P}	*)
(*								        *)
(* REWRITTEN    : T Melham (adapted for pred_set: January 1992)	        *)
(* DATE		: 90.07.30						*)
(* TRANSLATED   : Feb 20 1992, Konrad Slind                             *)
(*                                                                      *)
(* WARNING      : This code cannot statically depend on pred_setTheory, *)
(*                since it is used in pred_setScript.                   *)
(* =====================================================================*)


structure PGspec :> PGspec =
struct

open HolKernel Parse boolLib pairSyntax PairedLambda

val PAIR = pairTheory.PAIR;

val ERR = mk_HOL_ERR "PGspec";

val dest_in =
  dest_binop (prim_mk_const{Name = "IN", Thy="bool"})
             (ERR "dest_in" "not an IN term");

(* --------------------------------------------------------------------- *)
(* Local function: MK_PAIR						 *)
(*									 *)
(* A call to:								 *)
(* 									 *)
(*     MK_PAIR (``[x1,x2,...,xn]``) (``v:(ty1 # ty2 # ... # tyn)``)	 *)
(*									 *)
(* returns:								 *)
(*									 *)
(*     |- v = FST v, FST(SND v), ..., SND(SND...(SND v))		 *)
(* --------------------------------------------------------------------- *)

fun MK_PAIR vs v =
   if null (tl vs)
   then REFL v else
   let val vty = type_of v
       val alist = snd(dest_type vty)
       val (ty1,ty2) = (case alist of [a,b] => (a,b)
                        | otherwise => raise ERR "MK_PAIR" "")
       val inst = SYM(SPEC v (INST_TYPE [alpha |-> ty1, beta |-> ty2] PAIR))
       val (fst,snd) = dest_pair(rhs(concl inst))
       val gv = genvar ty2
   in SUBST [gv |-> MK_PAIR (tl vs) snd] (mk_eq(v,mk_pair(fst,gv))) inst
   end;

(* ---------------------------------------------------------------------*)
(* Local function: EXISTS_TUPLE_CONV					*)
(*									*)
(* A call to:								*)
(*                                                                      *)
(*  EXISTS_TUPLE_CONV [`x1`,...,`xn`] `?v. tm' = (\(x1,...,xn). tm) v   *)
(*									*)
(* returns:								*)
(*									*)
(*  |- (?v. tm' = (\(x1,...,xn). tm) v ) = ?x1...xn. tm' = tm		*)
(* ---------------------------------------------------------------------*)

local fun EX v tm th = EXISTS (mk_exists(v,subst[tm |-> v] (concl th)),tm) th
      and CH tm th = CHOOSE (tm,ASSUME (mk_exists(tm,hd(hyp th)))) th
      val conv = RAND_CONV (BETA_CONV ORELSEC PAIRED_BETA_CONV)
in
fun EXISTS_TUPLE_CONV vs tm =
   let val tup = end_itlist (curry mk_pair) vs
       val (Bvar,Body) = dest_exists tm
       val tupeq = MK_PAIR vs Bvar
       val asm1 = SUBST [Bvar |-> tupeq] Body (ASSUME Body)
       val comp = pairSyntax.strip_pair (rand(concl tupeq))
       val thm1 = Lib.itlist2 EX vs comp asm1
       val imp1 = DISCH tm (CHOOSE (Bvar,ASSUME tm) thm1)
       val asm2 = ASSUME (subst [Bvar |-> tup] Body)
       val thm2 = itlist CH vs (EXISTS (tm,tup) asm2)
       val imp2 = DISCH (hd(hyp thm2)) thm2
       val eq = IMP_ANTISYM_RULE imp1 imp2
       val beta = conv (snd(strip_exists(rhs(concl eq))))
   in
   TRANS eq (itlist EXISTS_EQ vs beta)
   end
end;

(* --------------------------------------------------------------------- *)
(* Local function: PAIR_EQ_CONV.					 *)
(*									 *)
(* A call to PAIR_EQ_CONV (``?x1...xn. a,b = c,T``) returns:		 *)
(*									 *)
(*    |- (?x1...xn. a,T = b,c) = (?x1...xn. (a = b) /\ c)		 *)
(* --------------------------------------------------------------------- *)

local
  val EQT = el 1 (CONJUNCTS (SPEC (``c:bool``) EQ_CLAUSES))
  val PEQ =
     let val inst = INST_TYPE [beta |-> bool]
                      (GENL[``x:'a``, ``y:'b``,
                            ``a:'a``, ``b:'b``] pairTheory.PAIR_EQ)
         val spec = SPECL [(``a:'a``),boolSyntax.T,
                           (``b:'a``),(``c:bool``)] inst
     in GENL [(``a:'a``),(``b:'a``),(``c:bool``)] (SUBS [EQT] spec)
     end
in
fun PAIR_EQ_CONV tm =
   let val (vs,body) = strip_exists tm
       val (lhs,rhs) = dest_eq body
       val (a,T) = dest_pair lhs
       val (b,c) = dest_pair rhs
       val th = SPECL [a,b,c] (INST_TYPE [alpha |-> type_of a] PEQ)
   in itlist EXISTS_EQ vs th
   end
end;

(* ---------------------------------------------------------------------*)
(* Local function: ELIM_EXISTS_CONV.					*)
(*									*)
(* ELIM_EXISTS_CONV (``?x. (x = tm) /\ P[x]``) returns:                 *)
(*									*)
(*   |- (?x. x = tm /\ P[x]) = P[tm/x]					*)
(* ---------------------------------------------------------------------*)

fun ELIM_EXISTS_CONV tm =
   let val (Bvar,Body) = dest_exists tm
       val (eq,body) = dest_conj Body
       val (asm1,asm2) = (SYM ## I) (CONJ_PAIR (ASSUME Body))
       val imp1 = DISCH tm (CHOOSE(Bvar,ASSUME tm)
                           (SUBST [Bvar |-> asm1] body asm2))
       val r = lhs eq
       val asm = subst [Bvar  |-> r] body
       val imp2 = DISCH asm (EXISTS (tm,r) (CONJ (REFL r) (ASSUME asm)))
   in
     IMP_ANTISYM_RULE imp1 imp2
   end

(* ---------------------------------------------------------------------*)
(* Local function: PROVE_EXISTS.					*)
(*									*)
(* PROVE_EXISTS `?x. tm` (x not free in tm) returns:		        *)
(*									*)
(*   |- ?x.tm = tm							*)
(* ---------------------------------------------------------------------*)

fun PROVE_EXISTS tm =
   let val (Bvar,Body) = dest_exists tm
       val v = genvar (type_of Bvar)
       val imp1 = DISCH tm (CHOOSE (v,ASSUME tm) (ASSUME Body))
       val imp2 = DISCH Body (EXISTS (tm,v) (ASSUME Body))
   in
      IMP_ANTISYM_RULE imp1 imp2
   end;

(* ---------------------------------------------------------------------*)
(* Internal function: list_variant					*)
(*									*)
(* makes variants of the variables in l2 such that they are all not in	*)
(* l1 and are all different.						*)
(* ---------------------------------------------------------------------*)

fun list_variant l1 l2 =
   if null l2 then []
   else let val v = variant l1 (hd l2)
        in v::list_variant (v::l1) (tl l2)
        end;

(* ---------------------------------------------------------------------*)
(* SET_SPEC_CONV: implements the axiom of specification for generalized	*)
(* set specifications.							*)
(*									*)
(* There are two cases:							*)
(*									*)
(*   1) SET_SPEC_CONV `t IN {v | p[v]}`  (v a variable, t a term)	*)
(* 									*)
(*      returns:							*)
(*									*)
(*      |- t IN {v | p[v]} = p[t/v]					*)
(*									*)
(*									*)
(*   2) SET_SPEC_CONV `t IN {tm[x1,...,xn] | p[x1,...xn]}`        	*)
(*									*)
(*      returns:							*)
(*									*)
(*      |- t IN {tm[x1,...,xn] | p[x1,...xn]} 				*)
(*	     =								*)
(*         ?x1...xn. t = tm[x1,...,xn] /\ p[x1,...xn]			*)
(*									*)
(* Note that {t[x1,...,xm] | p[x1,...,xn]} means:			*)
(*									*)
(*   GSPEC (\(x1,...,xn). (t[x1,...,xn], p[x1,...,xn]))		        *)
(* ---------------------------------------------------------------------*)

val checkIN = assert (fn tm =>
            (case dest_thy_const tm
             of {Name="IN", Thy="bool",...} => true
              | other => false) handle HOL_ERR _ => false)

val checkGSPEC = assert (fn tm => (* Dynamic dependence on pred_set *)
            (case dest_thy_const tm
             of {Name="GSPEC", Thy="pred_set",...} => true
              | other => false) handle HOL_ERR _ => false)

local val RAconv = RAND_CONV o ABS_CONV
      val conv = RAND_CONV(RAconv(RAND_CONV BETA_CONV))
      val conv2 = RAND_CONV (PAIR_EQ_CONV THENC PROVE_EXISTS)
      (* Would be simpler with dest_pabs *)
      fun mktup tm =
         let val (Bvar,Body) = dest_abs(rand tm)
             val (xs,res) = mktup Body
         in (Bvar::xs,res)
         end handle HOL_ERR _
             => let val (Bvar,Body) = dest_abs tm
                in ([Bvar], fst(dest_pair Body))
                end
in
fun SET_SPEC_CONV th =
 let val GSPEC = let val vs = fst(strip_forall(concl th))
                 in GENL (rev vs) (SPECL vs th)
                end
 in fn tm =>
  let val (v,set) = dest_in tm
      val (Rator,f) = dest_comb set
      val _ = checkGSPEC Rator
      val vty = type_of v
      val uty = fst(dom_rng(type_of f))
      val inst = SPEC v (INST_TYPE [alpha |-> vty, beta |-> uty] GSPEC)
      val (vs,res) = mktup f
  in
  if all (not o (C free_in res)) vs
  then let val spec = CONV_RULE conv (SPEC f inst)
           val thm1 = CONV_RULE conv2 spec
       in thm1
       end
  else if is_var res
       then let val spec = CONV_RULE conv (SPEC f inst)
                val thm1 = CONV_RULE (RAND_CONV PAIR_EQ_CONV) spec
            in TRANS thm1 (ELIM_EXISTS_CONV (rhs(concl thm1)))
            end
       else let val spec = SPEC f inst
                val exsts = rhs(concl spec)
                val nvs = list_variant (free_vars v) vs
                val thm = EXISTS_TUPLE_CONV nvs exsts
            in TRANS spec (CONV_RULE (RAND_CONV PAIR_EQ_CONV) thm)
            end
  end
  handle e => raise wrap_exn "PGspec" "SET_SPEC_CONV" e
end end;

end (* Gspec *)
