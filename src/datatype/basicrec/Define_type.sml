(* =====================================================================*)
(* FILE		: define_type.sml					*)
(* DESCRIPTION   : recursive type definition package.			*)
(*									*)
(* AUTHOR	: (c) T. F. Melham 1987	1990				*)
(* DATE		: 87.08.23						*)
(* REVISED	: 90.09.03                                              *)
(* TRANSLATED   : Konrad Slind (sometime in 1991)                       *)
(* REVISED      : Konrad Slind. Dec. 1992                               *)
(*                To use system parser for types, and to                *)
(*                provide frag list input, hence allow use of           *)
(*                antiquotes and to split essential input structure from*)
(*                concrete syntax.                                      *)
(* =====================================================================*)


structure Define_type :> Define_type =
struct

open HolKernel Parse Drule Conv Type_def_support oneTheory;

infix THENC ## |->;
val --> = Type.-->; infixr -->

fun ERR function message =
      HOL_ERR{origin_structure = "Define_type",
	      origin_function = function,
	      message = message}


(* =====================================================================*)
(* Code for constructing the type definiton subset predicate		*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* pargs : split the list of argument types for a constructor (returned *)
(* by parse_input) into a list of types (for non-recursve arguments) and*)
(* a numerical constant giving a count of the number of recursive args. *)
(* 									*)
(* For example:								*)
(* 									*)
(* pargs [inl `:ty1`;inl `:ty2`;inr (); inl `:ty3`]			*)
(*									*)
(* yields  1) [`:ty1`;`:ty2`;`:ty3`] (types of non recursive args)	*)
(*	  2) `SUC 0`		    (the no. of recursive arguments)	*)
(*									*)
(* ---------------------------------------------------------------------*)

local val Z = Term`0`
      val S = Term`SUC`
      fun SUC tm = mk_comb{Rator=S, Rand=tm}
      fun argsf n tylist [] = (rev tylist,n)
        | argsf n tylist (NONE::t) = argsf (SUC n) tylist  t
        | argsf n tylist (SOME ty::t) = argsf n (ty::tylist) t
in
fun pargs x = argsf Z [] x
end;

(* ---------------------------------------------------------------------*)
(* mk_tuple_ty : make a tuple type of a list of types.			*)
(*									*)
(* Special case: if the list is empty, then the output is `:one`.	*)
(* ---------------------------------------------------------------------*)
local val onety = Type`:one`
      fun mk_prod ty1 ty2 = mk_type{Tyop="prod", Args=[ty1,ty2]}
in
fun mk_tuple_ty l = end_itlist mk_prod l handle _ => onety
end;

(* ---------------------------------------------------------------------*)
(* mk_tuple : make a tuple of a list of terms.				*)
(*									*)
(* Special case: if the list is empty, then the output is `one:one`.	*)
(* ---------------------------------------------------------------------*)
local val onec = Term`one`
      fun pair tm1 tm2 = mk_pair{fst=tm1, snd=tm2}
in
fun mk_tuple l = end_itlist pair l handle _ => onec
end;

(* ---------------------------------------------------------------------*)
(* mk_sum_ty : make a sum type of a list of types.			*)
(* ---------------------------------------------------------------------*)
local fun mk_sum ty1 ty2 = mk_type{Tyop="sum", Args=[ty1,ty2]}
in
val mk_sum_ty = end_itlist mk_sum
end;

(* ---------------------------------------------------------------------*)
(* inject : make a list of injections of a list of values, given a sum  *)
(* type into which they are to be injected.				*)
(* 									*)
(* For example, if ty = (ty1,(ty2,ty3))sum and vs = [v1;v2;v3] then:	*)
(*									*)
(*     inject ty vs = [INL v1; INL(INR v2); INR(INR v3)]		*)
(* ---------------------------------------------------------------------*)

local
fun combize tm1 tm2 = mk_comb{Rator=tm1, Rand=tm2}
in
fun inject ty [v] = [v]
  | inject ty (v::vs) =
     let val {Args = [lty,rty],...} = dest_type ty
         val res = mk_comb{Rator=mk_const{Name="INL",Ty=lty-->ty}, Rand=v}
         val inr = combize (mk_const{Name="INR", Ty = rty-->ty})
     in
       res::map inr (inject rty vs)
     end
end;

(* ---------------------------------------------------------------------*)
(* mkvars : generate sensible variable names for the arguments to the 	*)
(* non-recursive constructors of a newly-defined type.  A call to mkvars*)
(* takes the form:							*)
(*									*)
(*     mkvars [t1;...;tn]						*)
(*									*)
(* where t1,...,tn are the types required for the variables.		*)
(* ---------------------------------------------------------------------*)

local
fun fch ty = (hd o explode o #Tyop o dest_type) ty
             handle _ => Portable_Char.chr 120 (* "x" *)
fun suff f c l =
   if (f c = "")
   then if (Portable_List.exists (fn x => fch x = c) l)
        then ("0", fn ch => (if (ch=c) then "0" else f ch))
        else ("",f)
   else let val n = int_to_string(string_to_int(f c) + 1)
        in (n, fn ch => if (ch=c) then n else f ch)
        end
fun mkvs f rvs [] = []
  | mkvs f rvs (h::t) =
      let val c = fch h
          val (s,f') = suff f c t
(*           val v = variant rvs (mk_primed_var{Name = c^s, Ty = h}) *)
          val v = variant rvs (mk_var{Name = Portable_String.str c^s, Ty = h})
      in
      v::(mkvs f' (v::rvs) t)
      end
in
fun mkvars l = mkvs (fn x => "") [] l
end;

(* ---------------------------------------------------------------------*)
(* mk_subset_pred : make a subset predicate from the parse of the user's*)
(* input. For a full description of the form of this predicate, see:	*)
(*									*)
(* Melham, T.F.								*)
(* `Automating Recursive Type Definitions in Higher Order Logic`,	*)
(* in: Current Trends in Hardware Verification and Automated 		*)
(* Theorem Proving, edited by G. Birtwistle and P.A. Subrahmanyam,	*)
(* (Springer-Verlag 1989) pp. 341-386.					*)
(* ---------------------------------------------------------------------*)

local
val boolty = ==`:bool`==
val numty = ==`:num`==
and eq = --`$= :num->num->bool`--
and Z = --`0`--
fun zero n = (n = Z)
fun eqize tm1 tm2 = mk_eq{lhs = tm1, rhs = tm2}
fun LEN tl =
   let val lenty = type_of tl --> numty
       val lentl = mk_comb{Rator = eq,
                  Rand=mk_comb{Rator=mk_const{Name="LENGTH",Ty=lenty},Rand=tl}}
   in fn n => mk_comb{Rator = lentl, Rand = n}
   end
in
fun mk_subset_pred tysl =
   let val (tys,rectys) = unzip (map pargs tysl)
   in
   if (not(Portable_List.exists zero rectys))
   then raise ERR "mk_subst_pred" "no non-recursive constructor"
   else let val repty = mk_sum_ty (map mk_tuple_ty tys)
            val tlty = mk_type{Tyop = "list",
                               Args = [mk_type{Tyop = "ltree",Args = [repty]}]}
            val v = mk_var{Name = "v", Ty = repty}
            and tlv = mk_var{Name = "tl", Ty = tlty}
            val lens = map (LEN tlv) rectys
            val cases = if (null(tl tys))
                  then let val vars = mkvars (hd tys)
                       in [list_mk_exists(vars,mk_eq{lhs=v,rhs=mk_tuple vars})]
                       end
                  else let val vsl =  map mkvars tys
                           val tuples = map mk_tuple vsl
                           val injs = inject repty tuples
   	                   val eqs = map (eqize v) injs
                       in
                       map list_mk_exists (zip vsl eqs)
                       end
            val body = list_mk_disj
                        (map2(fn tm1 => fn tm2 => mk_conj{conj1=tm1,conj2=tm2})
                              cases lens)
        in
        mk_abs{Bvar = v, Body = mk_abs{Bvar = tlv, Body = body}}
        end
   end
end;

(* =====================================================================*)
(* existence proof for the subset predicate				*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* splitf : split a list at a value satisfying a given predicate.	*)
(* changed to make it tail recursive. kls.                              *)
(* ---------------------------------------------------------------------*)
local
fun split p prefix (x::suffix) =
   if (p x)
   then (rev prefix,x,suffix)
   else split p (x::prefix) suffix
in
fun splitf p alist = split p [] alist
end;

(* ---------------------------------------------------------------------*)
(* prove_existence_thm : prove the existence theorem required for making*)
(* the type definition.							*)
(* 									*)
(* Given a subset predicate, pred, of the form:				*)
(*									*)
(*    \v tl. (?x1 ... xn. v = INL(x1,...,xn) /\ LENGTH tl = l1) /\      *)
(*	    (?x1 ... xm. v = INL(INR(x1...xm)) /\ LENGTH tl = l2)	*)
(*		  :							*)
(*	         etc							*)
(*									*)
(* this function look for a case where `LENGTH tl = 0` and then proves	*)
(* that |- ?r. TRP pred r  						*)
(*									*)
(* ---------------------------------------------------------------------*)

local
val alpha = ==`:'a`==
val LEN0 = CONJUNCT1 listTheory.LENGTH
val EXTH = rec_typeTheory.exists_TRP
val Z = --`0`--
fun zero tm = (tm = Z)
fun mk_subst vs = itlist (fn v => fn S => (v |-> variant vs v)::S)
                         vs []
fun efn {residue,redex} th =
   let val (vs,{lhs,rhs}) = (I ## dest_eq) (strip_exists (concl th))
       val pat = list_mk_exists(redex::vs,
                                mk_eq{lhs=lhs,rhs=subst[residue |-> redex]rhs})
   in EXISTS (pat,residue) th
   end
in
fun prove_existence_thm pred =
   let val rty = hd(#Args(dest_type(type_of pred)))
       val ([v,tl],cs) = (I ## strip_disj)(strip_abs pred)
       val (b,cl,a) = splitf (zero o rand o rand) cs
       val body = rand(rator cl)
       val (vs,value) = (I ## rand) (strip_exists body)
       val s = mk_subst vs
       val nvs = map (fn v => (variant vs v,v)) vs
       val nval = subst s value
       val veth = itlist efn s (REFL nval)
       val lem = EXISTS (mk_exists{Bvar = v,Body = body},nval) veth
       val ltrty = mk_type{Tyop = "ltree",Args = [rty]}
       val cth = CONJ (ASSUME body) (INST_TYPE [alpha |-> ltrty] LEN0)
       val Nil = mk_const{Name="NIL",Ty=mk_type{Tyop = "list", Args = [ltrty]}}
       val app = mk_comb{Rator=mk_comb{Rator=pred,Rand=v},Rand=Nil}
       val beta = EXISTS_EQ v (SYM(LIST_BETA_CONV app))
       val thm1 = if (null a) then cth else DISJ1 cth (list_mk_disj a)
       val thm2 = INST [tl |-> Nil] (itlist DISJ2 b thm1)
       val eth = CHOOSE (v,lem) (EXISTS (lhs(concl beta),v) thm2)
       val exth = SPEC pred (INST_TYPE [alpha |-> rty] EXTH)
   in
   MP exth (EQ_MP beta eth)
   end
end;

(* =====================================================================*)
(* variant_tyvar: Find the type variable with the least number of stars	*)
(* that doesn't occur in the given list (for instantiating TY_DEF_THM).	*)
(*                                                                      *)
(* Modified for hol90.  kls.                                            *)
(* =====================================================================*)

local
fun variant l1 l2 n =
   let val ty = mk_vartype(Portable_String.concat (l2@[int_to_string n]))
   in
   if (Portable_List.exists (fn t => t=ty) l1)
   then variant l1 l2 (n+1)
   else ty
   end
in
fun variant_tyvar [] l2 = mk_vartype (Portable_String.concat l2)
  | variant_tyvar l1 l2 =
      let val ty = mk_vartype (Portable_String.concat l2)
      in
      if (Portable_List.exists (fn t => t = ty) l1)
      then variant l1 l2 1
      else ty
      end
end;


(* =====================================================================*)
(* Procedures for cleaning up the type axiom after instantiation.	*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* OR_IMP_CONV: eliminate disjuncts in the antecedent of an implication.*)
(*									*)
(* Given a term `(D1 \/ ... \/ Dn) ==> C`, OR_IMP_CONV returns:		*)
(*									*)
(*    |- ((D1 \/ ... \/ Dn) ==> C) = (D1 ==> C /\ ... /\ Dn ==> C)	*)
(* ---------------------------------------------------------------------*)

local
fun proveimp f DS =
   let val {disj1,disj2} = dest_disj DS
       val res = DISCH disj1 (f (DISJ1 (ASSUME disj1) disj2))
   in
   CONJ res (proveimp (f o (DISJ2 disj1)) disj2)
   end
   handle _ => DISCH DS (f (ASSUME DS))
fun disjfn th1 th2 =
   let val D = mk_disj{disj1 = rand(rator(concl th1)),
                       disj2 = rand(rator(concl th2))}
   in
   DISCH D (DISJ_CASES (ASSUME D) (UNDISCH th1) (UNDISCH th2))
   end
in
fun OR_IMP_CONV tm =
   let val {ant,conseq} = dest_imp tm
       val imp1 = DISCH tm (proveimp (MP (ASSUME tm)) ant)
       val rtm = #conseq(dest_imp(concl imp1))
       val imp2 = DISCH rtm (end_itlist disjfn (CONJUNCTS(ASSUME rtm)))
   in
   IMP_ANTISYM_RULE imp1 imp2
   end
end;

(* ---------------------------------------------------------------------*)
(* FORALL_IN_CONV: move two universal quantifiers into a conjunction.	*)
(*									*)
(* Given a term `!x y. C1 /\ ... /\ Cn`, the conversion proves:		*)
(*									*)
(*    |- (!x y. C1 /\ ... /\ Cn) = (!x y. C1) /\ ... /\ (!x y. Cn)	*)
(*									*)
(* Note: this conversion can easily be adapted to deal with more than 	*)
(* two universally quantified variables by using SPECL and GENL.	*)
(* ---------------------------------------------------------------------*)

local
fun mconj f th =
   let val (th1,th2) = (f ## mconj f) (CONJ_PAIR th)
   in CONJ th1 th2
   end
   handle _ => f th
in
fun FORALL_IN_CONV tm =
   let val ([x,y],cs) = (I ## strip_conj) (strip_forall tm)
       val spec = (SPEC y) o (SPEC x)
       and gen = (GEN x) o (GEN y)
       val imp1 = DISCH tm (mconj gen (spec (ASSUME tm)))
       val acs = #conseq(dest_imp(concl imp1))
       val imp2 = DISCH acs (gen (mconj spec (ASSUME acs)))
   in
   IMP_ANTISYM_RULE imp1 imp2
   end
end;

(* ---------------------------------------------------------------------*)
(* CONJS_CONV : apply a given conversion to a sequence of conjuncts	*)
(*									*)
(* CONJS_CONV conv `t1 /\ t2 /\ ... /\ tn` applies conv to each of the  *)
(* n conjuncts t1,t2,...,tn and then rebuilds the conjunction from the  *)
(* results.								*)
(*									*)
(* ---------------------------------------------------------------------*)

local val AND = --`$/\`--
in
fun CONJS_CONV conv tm =
   let val {conj1,conj2} = dest_conj tm
   in
    MK_COMB(AP_TERM AND (conv conj1), CONJS_CONV conv conj2)
   end
   handle _ => conv tm
end;

(* ---------------------------------------------------------------------*)
(* EQN_ELIM_CONV : eliminate antecedent defining equations for the node *)
(* vertices (see below).						*)
(*									*)
(* The terms in question have the form:					*)
(*									*)
(*    `!v tl. ((?x1...xn. v=tm) /\ P) ==> Q`				*)
(*									*)
(* This conversion transforms this term as follows:			*)
(*									*)
(*    |- (!v tl. ((?x1...xn. v=tm) /\ P) ==> Q)				*)
(*         = 								*)
(*       !tl. P ==> !x1...xn. Q[tm/v]					*)
(* 									*)
(* ---------------------------------------------------------------------*)
local
fun efn nv ov th =
   let val (vs,{lhs,rhs}) = (I ## dest_eq) (strip_exists(concl th))
       val pat = list_mk_exists((nv::vs),
                                mk_eq{lhs=lhs, rhs = subst[ov |-> nv] rhs})
   in EXISTS (pat,ov) th
   end
fun chfn f v th =
   let val asm = ASSUME (mk_exists{Bvar = v, Body = first f (hyp th)})
   in CHOOSE (v,asm) th
   end
in
fun EQN_ELIM_CONV tm =
   let val ([v,tl],{ant,conseq}) = (I ## dest_imp) (strip_forall tm)
       val {conj1,conj2} = dest_conj ant
       val (vs,def) = strip_exists conj1
       val thm1 = SPEC tl (SPEC (rand def) (ASSUME tm))
       val goal = #conj1(dest_conj(#ant(dest_imp(concl thm1))))
       val nvs = fst(strip_exists goal)
       val thm2 = itlist2 efn nvs vs (REFL (rand def))
       val thm3 = DISCH conj2 (GENL vs (MP thm1 (CONJ thm2 (ASSUME conj2))))
       val imp1 = DISCH tm (GEN tl thm3)
       val res = #conseq(dest_imp(concl imp1))
       val (a1,a2) = CONJ_PAIR(ASSUME ant)
       val asm = MP (SPEC tl (ASSUME res)) a2
       val thm4 = SUBST[v |-> SYM (ASSUME def)] conseq (SPECL vs asm)
       fun f tm = (lhs(snd(strip_exists tm)) = v) handle _ => false
       val thm5 = PROVE_HYP a1 (itlist (chfn f) vs thm4)
       val imp2 = DISCH res (GEN v (GEN tl (DISCH ant thm5)))
   in
   IMP_ANTISYM_RULE imp1 imp2
   end
end;

(* ---------------------------------------------------------------------*)
(* LENGTH_MAP_CONV : eliminate the `LENGTH (MAP REP tl) = n` terms in	*)
(* favour of `LENGTH tl = n`.						*)
(*									*)
(* The terms in question have the form:					*)
(*									*)
(*    `!tl. (LENGTH (MAP REP tl) = n) ==> Q`				*)
(*									*)
(* The conversion is supplied with the theorem:				*)
(*									*)
(*    |- $= LENGTH (MAP REP tl) = $= LENGTH tl				*)
(*									*)
(* and transforms the input term as follows:				*)
(*									*)
(*    |- !tl. (LENGTH (MAP REP tl) = n) ==> Q				*)
(*         = 								*)
(*       !tl. (LENGTH tl = n) ==> Q					*)
(* 									*)
(* ---------------------------------------------------------------------*)

local
val IMP = --`$==>`--
in
fun LENGTH_MAP_CONV eq tm =
   let val {Bvar,Body} = dest_forall tm
       val {ant,conseq} = dest_imp Body
   in
   FORALL_EQ Bvar (AP_THM (AP_TERM IMP (AP_THM eq (rand ant))) conseq)
   end
end;


(* ---------------------------------------------------------------------*)
(* LENGTH_ELIM_CONV : Eliminate `LENGTH` expressions.                   *)
(*                                                                      *)
(* If n is a number in successor notation (e.g. `0`, `SUC 0`, etc) then:*)
(*                                                                      *)
(*    LENGTH_ELIM_CONV `:ty` `!l:(ty)list. (LENGTH l = n) ==> tm[l]`    *)
(*                                                                      *)
(* returns:                                                             *)
(*                                                                      *)
(*    |- (!l. (LENGTH l = n) ==> tm[l]) = !x0...xi. tm[[x0;...;xi]/l]   *)
(*                                                                      *)
(* where i = n-1, and the "x"'s have sensibly-chosen names.		*)
(* ---------------------------------------------------------------------*)

local
val ZERO = --`0`--
val ONE = --`SUC 0`--
and N = --`n:num`--
val bty = ==`:bool`==
val alpha = ==`:'a`==
val lcons = listTheory.LENGTH_EQ_CONS
val lnil  = listTheory.LENGTH_EQ_NIL
fun mkvar ty st i = mk_primed_var{Name = st^int_to_string i, Ty = ty}
fun gvs bvs ty st n i =
   if (n=ZERO)
   then []
   else let val v = variant bvs (mkvar ty st i)
        in  v::(gvs (v::bvs) ty st (rand n) (i+1))
        end
fun genvs bvs ty st n =
   if (n=ONE)
   then let val v = mk_primed_var{Name = st, Ty = ty}
        in [variant bvs v]
        end
   else gvs bvs ty st n 1
fun pred_ty ty = ty --> bty
fun bconv tm =
   let val {Rator,Rand} = dest_comb tm
       val {Bvar = l,Body} = dest_abs Rator
       val {Bvar = v,Body} = dest_forall Body
       val th = FORALL_EQ v (bconv Body)
   in
   RIGHT_BETA (AP_THM (ABS l th) Rand)
   end
   handle _ => BETA_CONV tm
fun conv (cth,nth) Pv P n vs =
   if (n=ZERO)
   then INST [Pv |-> P] nth
   else let val (h::t) = vs
            val pre = rand n
            val th1 = INST [Pv |-> P](INST [N |-> pre] cth)
            val {Body,...} = dest_forall(rand(concl th1))
            val {Bvar,Body} = dest_abs(rator(rand Body))
            val {Bvar = x, Body} = dest_forall Body
            val P' = mk_abs{Bvar = Bvar,
                            Body = mk_forall{Bvar=h,Body=subst[x |-> h] Body}}
        in
        TRANS th1 (conv (cth,nth) Pv P' pre t)
        end
in
fun LENGTH_ELIM_CONV tm =
   let val {Bvar,Body} = dest_forall tm
       val {Rator,Rand} = dest_comb Body
       val bv_ty = type_of Bvar
       val n = rand(rand Rator)
       val [ty] = #Args(dest_type bv_ty)
       val ty_subst = INST_TYPE[alpha |-> ty]
       val st = Portable_String.str(hd(explode(#Tyop(dest_type ty))))
       val bvs = fst(strip_forall Rand)
       val vs = genvs bvs ty st n
       val lam = mk_abs{Bvar = Bvar, Body = Rand}
       val bth = AP_TERM Rator (SYM(BETA_CONV (mk_comb{Rator=lam,Rand=Bvar})))
       val Pv = genvar (pred_ty bv_ty)
       val cth = SPEC N (SPEC Pv (ty_subst lcons))
       val nth = SPEC Pv (ty_subst lnil)
       val thm1 = conv (cth,nth) Pv lam n vs
       val thm2 = TRANS (FORALL_EQ Bvar bth) thm1
   in
   CONV_RULE (RAND_CONV bconv) thm2
   end
end;

(* ---------------------------------------------------------------------*)
(* MAP_CONV : expand `MAP f [...]` with the definition of `MAP`		*)
(* ---------------------------------------------------------------------*)

local
val (mnil,mcons) = CONJ_PAIR listTheory.MAP
fun conv (nth,cth) tm =
   let val(_,[h,t]) = strip_comb tm
       val thm = SPEC t (SPEC h cth)
       val cfn = rator(rand(concl thm))
   in TRANS thm (AP_TERM cfn (conv (nth,cth) t))
   end
   handle _ => nth
in
fun MAP_CONV tm =
   let val (_,[f,l]) = strip_comb tm
   in conv (ISPEC f mnil, ISPEC f mcons) l
   end
end;

(* ---------------------------------------------------------------------*)
(* ELIM_MAP_CONV : use MAP_CONV where appropriate.			*)
(* ---------------------------------------------------------------------*)

fun ELIM_MAP_CONV tm =
   let val (vs,(EQ,[l,r])) = (I ## strip_comb) (strip_forall tm)
       val {Rator = fnn,Rand} = dest_comb l
       val {Rator = A,Rand} = dest_comb Rand
       val {Rator = Na,Rand = arg} = dest_comb Rand
       val thm1 = AP_TERM fnn (AP_TERM A (AP_TERM Na (MAP_CONV arg)))
       val (f,[a1,a2,a3]) = strip_comb r
       val thm2 = AP_THM (AP_THM (AP_TERM f (MAP_CONV a1)) a2) a3
       val thm = MK_COMB (AP_TERM EQ thm1, thm2)
   in
   itlist FORALL_EQ vs thm
   end;

(* ---------------------------------------------------------------------*)
(* TRANSFORM : transform the type axiom towards its final form:		*)
(*									*)
(*       |- !f. ?!fn. !v tl. <term>					*)
(*   ---------------------------------					*)
(*     |- ?!fn.  <transformed term>					*)
(* 									*)
(* The transformations are:						*)
(*									*)
(*  (1) two beta conversions:						*)
(*									*)
(*       `(\v tl. tm) t1 t2`      --->    `tm[t1/v,t2/tl]`		*)
(*									*)
(*  (2) eliminate the antecedent disjunction:				*)
(*									*)
(*       `D1 \/ .. \/ Dn ==> Q`   --->    `D1 ==> Q /\ .. /\ Dn ==> Q`	*)
(*									*)
(*  (3) move universally quantified vars into resulting conjunction:	*)
(*									*)
(*       `!v tl. i1 /\ .. /\ in   --->    `!v tl. i1 /\ .. /\ !v tl. in`*)
(*									*)
(*  (4) apply the transfomation given by EQN_ELIM_CONV to each conjunct.*)
(*									*)
(*  (5) transform LENGTH(MAP REP tl) into LENGTH tl (as described above)*)
(*									*)
(*  (6) eliminate `LENGTH tl = n ==> P` using LENGTH_ELIM_CONV.		*)
(* 									*)
(*  (7) expand `MAP f [...]` using the definition of MAP.		*)
(* 									*)
(* 									*)
(* NB: the function drops the `f`, and returns it.			*)
(* ---------------------------------------------------------------------*)

local
val EQ = --`$= :num->num->bool`--
val lmap = listTheory.LENGTH_MAP
fun cconv lm = EVERY_CONV [EQN_ELIM_CONV,		  (* (4) *)
                           LENGTH_MAP_CONV lm,		  (* (5) *)
	                   LENGTH_ELIM_CONV,		  (* (6) *)
	                   ELIM_MAP_CONV]	          (* (7) *)
in
fun TRANSFORM REP th =
   let val {Bvar = f,Body} = dest_forall (concl th)
       val {Rator = EU,Rand} = dest_comb Body
       val {Bvar = fnn, Body} = dest_abs Rand
       val ([v,tl],imp) = strip_forall Body
       val {Rator,Rand = cncl} = dest_comb imp
       val {Rator = IMP, Rand = hy} = dest_comb Rator
       val beta = (RATOR_CONV BETA_CONV THENC BETA_CONV) hy     (* (1) *)
       val thm1 = AP_THM (AP_TERM IMP beta) cncl
       val red  = rand (concl thm1)
       val thm2 = TRANS thm1 (OR_IMP_CONV red)                   (* (2) *)
       val thm3 = FORALL_EQ v (FORALL_EQ tl thm2)
       val gen  = rand (concl thm3)
       val thm4 = TRANS thm3 (FORALL_IN_CONV gen)                (* (3) *)
       val cs   = rand (concl thm4)
       val lmth = AP_TERM EQ (ISPECL [tl,REP] lmap)
       val thm5 = TRANS thm4 (CONJS_CONV (cconv lmth) cs)
       val thm6 = AP_TERM EU (ABS fnn thm5)
   in
   (f,EQ_MP thm6 (SPEC f th))
   end
end;



(* =====================================================================*)
(* Define the constructors of the recursive type.			*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* part : split a list into two parts: a list of the first n elements, 	*)
(* and a list of the remaining elements.				*)
(* fun part n l = (n=0 => [],l | (curry $. (hd l) ## I)                 *)
(*                               (part (n-1) (tl l)));                  *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

local
fun p 0 prefix suffix = (rev prefix,suffix)
  | p n prefix (h::t) = p (n-1) (h::prefix) t
in
fun part n alist = p n [] alist
end;

(* ---------------------------------------------------------------------*)
(* define_const : define one of the constructors for the concrete 	*)
(* recursive type specified by the user.  The arguments are:		*)
(*									*)
(*      c   : the constructor name 					*)
(*      tys : its types, as returned by parse_input			*)
(*      fix : its fixity (Prefix, Infix of int, Binder)                 *)
(*	tm  : the equation for that constructor, in its current state.	*)
(* ---------------------------------------------------------------------*)

local
fun cfn (SOME _) n = n
  | cfn NONE n = n+1
fun combin evs rvs [] = []
  | combin evs rvs (SOME _::t) = hd evs::combin (tl evs) rvs t
  | combin evs rvs (NONE::t)   = hd rvs::combin evs (tl rvs) t
fun mkfnty v ty = type_of v --> ty
fun geneq uovs odvs tm =
   let val imp1 = GENL odvs (SPECL uovs (ASSUME tm))
       val body = concl imp1
       val imp2 = DISCH body (GENL uovs (SPECL odvs (ASSUME body)))
   in
   IMP_ANTISYM_RULE (DISCH tm imp1) imp2
   end
in
fun define_const (c, tys, fix, tm) =
   let val (vs,(EQ,[l,r])) = (I ## strip_comb) (strip_forall tm)
       val f = fst(strip_comb r)
       val count = itlist cfn tys 0
       val (rvs,evs) = (rev ## I) (part count vs)
       val vars = combin evs rvs tys
       val cty = itlist mkfnty vars (type_of (rand l))
       val Ccomb = list_mk_comb(mk_var{Name=c, Ty=cty},vars)
(*
       val c' = if (c = "\"\"") (* string hack, kls Nov.92 *)
                then "eps"
                else c
       val name = c'^"_DEF"
*)
       val name = c^"_DEF"
       val eqn = mk_eq{lhs = Ccomb, rhs = rand l}
       val def = new_gen_definition(name, eqn, fix)
       val dvs = fst(strip_forall(concl def))
       val thm1 = AP_TERM EQ (AP_TERM (rator l) (SPECL dvs def))
       val thm2 = itlist FORALL_EQ dvs (SYM (AP_THM thm1 r))
   in
   TRANS (geneq vs vars tm) thm2
   end
end;

(* ---------------------------------------------------------------------*)
(* DEFINE_CONSTRUCTORS : defines the constructors for the concrete 	*)
(* recursive type specified by the user.  This function just maps 	*)
(* define_const over the conjuncts of the current theorem.		*)
(* Changed to allow fixities to be specified (kls. Dec 31, 1992)        *)
(* ---------------------------------------------------------------------*)

local val AND = Term`$/\`
      fun mkconj t1 t2 = MK_COMB(AP_TERM AND t1,t2)
      fun map4 f ([],[],[],[]) = []
        | map4 f ((a::rst1),(b::rst2),(c::rst3),(d::rst4)) =
                f(a,b,c,d)::map4 f (rst1,rst2,rst3,rst4)
in
fun DEFINE_CONSTRUCTORS cs atys fixities th =
   let val {Rator = EU,Rand} = dest_comb (concl th)
       val {Bvar,Body} = dest_abs Rand
       val dcs = map4 define_const(cs,atys,fixities, strip_conj Body)
       val thm = end_itlist mkconj dcs
   in EQ_MP (AP_TERM EU (ABS Bvar thm)) th
   end
end;

(* =====================================================================*)
(* Construct the function which applies a separate function variable to *)
(* the values present on the right-hand side of each defining equation	*)
(* in the recursive function definition.				*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* mk_tests : make the discriminator tests for each clause of the type  *)
(* definition theorem.  A call to:					*)
(*									*)
(*   mk_tests [x1,x2...,xn] `:ty1 + ty2 + ... + tyn`			*)
(*									*)
(* returns a variable v, and a list of tests:				*)
(*									*)
(*   [ISL v; ISL (OUTR v); ... ; ISL (OUTR ... (OUTR v)..)]		*)
(*									*)
(* where v is a genvar of type `:ty1 + ty2 + ... + tyn`			*)
(*									*)
(* ---------------------------------------------------------------------*)

local
val boolty = ==`:bool`==
fun make     [c] _ _ = []
  | make (c::cs) v ty =
    let val {Args = [_,outty],...} = dest_type ty
        val Isl = mk_const{Name="ISL",Ty = ty-->boolty}
        val Outr = mk_const{Name="OUTR",Ty = ty-->outty}
        val test = mk_comb{Rator = Isl, Rand = v}
        and out = mk_comb{Rator = Outr, Rand = v}
    in
    test::(make cs out outty)
    end
in
fun mk_tests cs ty =
   let val v = genvar ty
   in (v, make cs v ty)
   end
end;

(* ---------------------------------------------------------------------*)
(* mk_proj : make the projections for each clause of the type definition*)
(* theorem.  A call to:							*)
(*									*)
(*   mk_proj v [x1,x2...,xn] `:ty1 + ty2 + ... + tyn`			*)
(*									*)
(* returns a list of projections:			                *)
(*									*)
(*   [OUTL v; OUTL(OUTR v); ... ; OUTR (OUTR ... (OUTR v)..)]		*)
(*									*)
(* where v is a supplied genvar of type `:ty1 + ty2 + ... + tyn`	*)
(*									*)
(* ---------------------------------------------------------------------*)

fun mk_proj v [c] _ = [v]
  | mk_proj v (c::cs) ty =
      let val {Args = [ty1,ty2],...} = dest_type ty
          val Outr = mk_const{Name="OUTR",Ty = ty --> ty2}
          val Outl = mk_const{Name="OUTL",Ty = ty --> ty1}
          val ltm = mk_comb{Rator=Outl,Rand=v}
          and rtm = mk_comb{Rator=Outr,Rand=v}
      in
      ltm::(mk_proj rtm cs ty2)
      end;

(* ---------------------------------------------------------------------*)
(* extract_list : generate expressions that extract the components of an*)
(* object-language list.  A call to:					*)
(*									*)
(*   extract_list `(ty)list` `v:ty list` `[x1:ty;...,xn]`		*)
(*									*)
(* returns a list of terms:						*)
(*									*)
(*   [`HD v`; `HD(TL v)`; ... ; `HD(TL ... (TL v)..)`]			*)
(*									*)
(* Note: the list can be empty.						*)
(* ---------------------------------------------------------------------*)

fun extract_list ty =
   let val {Args=[ety],...} = dest_type ty
       val H = mk_const{Name="HD",Ty = ty --> ety}
       val T = mk_const{Name="TL",Ty = ty --> ty}
       fun extr H T v tm =
          let val (_,[h,t]) = strip_comb tm
              val hval = mk_comb{Rator = H, Rand = v}
              val tval = mk_comb{Rator = T, Rand = v}
          in hval::(extr H T tval t)
          end handle _ => []
   in
   extr H T
   end;

(* ---------------------------------------------------------------------*)
(* strip_inj : strip an arbitrary number of injections off a term.  A	*)
(* typical call to strip_inj looks like:				*)
(*   									*)
(*   strip_inj `INR(INR(INR....(INL <val>)..)				*)
(*									*)
(* and returns <val>.							*)
(* ---------------------------------------------------------------------*)

fun strip_inj tm =
   let val {Rator,Rand} = dest_comb tm
       val opp = (#Name o dest_const) Rator
   in if (opp = "INR" orelse opp = "INL")
      then strip_inj Rand
      else tm
   end handle _ => tm;

(* ---------------------------------------------------------------------*)
(* extract_tuple : generate expressions that extract the components of	*)
(* an object-language tuple.  A call to:				*)
(*									*)
(*   extract_tuple `ty` `v:ty` `(x1,...,xn)ty`				*)
(*									*)
(* returns a list of terms:						*)
(*									*)
(*   [`FST v`; `FST(SND v)`; ... ; `FST(SND ... (SND v)..)`]		*)
(*									*)
(* Note: the list will not be empty.					*)
(* ---------------------------------------------------------------------*)

fun extract_tuple ty v tm =
   let val (_,[c1,c2]) = strip_comb tm
       val {Args = [ty1,ty2],...} = dest_type ty
       val Fst = mk_const{Name="FST",Ty = ty --> ty1}
       val Snd = mk_const{Name="SND",Ty = ty --> ty2}
       val fval = mk_comb{Rator = Fst, Rand = v}
       val sval = mk_comb{Rator = Snd, Rand = v}
   in
   fval::(extract_tuple ty2 sval c2)
   end
   handle _ => [v];


(* ---------------------------------------------------------------------*)
(* gen_names : generate reasonable names for the function variables on	*)
(* the right-hand sides of the equations in the type axiom.  There are  *)
(* two kinds of names: 							*)
(*									*)
(*     "e<suffix>"    and     "f<suffix>"				*)
(*									*)
(* A name has the e-form if the corresponding `function` is just a 	*)
(* constant (this information is obtained from the `cs` list). Otherwise*)
(* the name has the f-form.  Suffixes are numerical, and are generated	*)
(* in the order: 0,1,2...etc.  When ef is true, however, there will be  *)
(* only one e-type name, for which the suffix will be empty.  Likewise	*)
(* for functions proper when the ff flag is true.			*)
(* ---------------------------------------------------------------------*)

local
fun gen (ef,ff) (n,m) [] = []
  | gen (ef,ff) (n,m) ([]::t) =
       let val ename = ("e" ^ (if ef then int_to_string n else ""))
       in ename::(gen (ef,ff) (n+1,m) t)
       end
  | gen (ef,ff) (n,m) (_::t) =
       let val fname = ("f" ^ (if ff then int_to_string m else ""))
       in fname::(gen (ef,ff) (n,m+1) t)
       end
in
fun gen_names (ef,ff) cs =  gen (ef,ff) (0,0) cs
end;


(* ---------------------------------------------------------------------*)
(* mk_fun_ty : construct a function type, given a term and the type of  *)
(* the expected result.							*)
(*									*)
(*   mk_fun_ty `tm:ty1` `:ty2`  =  `:ty1 -> ty2`			*)
(* ---------------------------------------------------------------------*)

fun mk_fun_ty tm ty = (type_of tm --> ty);

(* ---------------------------------------------------------------------*)
(* make_rhs : make the right-hand side for one clause of the type axiom.*)
(* The ty argument is the resulting type of the right-hand side. The 	*)
(* variables rv and tv are genvars, standing for the list of results of *)
(* recursive applications of the recursive function and the subtrees,	*)
(* respectively. The variable pv is the result of projecting out the 	*)
(* tuple of non-recursive values, and the flag fl indicates if any such *)
(* values are actually present (this distinguishes between a constructor*)
(* with a single argument of the user-specified type :one and the use of*)
(* `:one` to represent constant constructors).  The terms rl, val, and 	*)
(* tl are the right-hand side values to be extracted. The string "name"	*)
(* gives the function name for this right-hand side.			*)
(* ---------------------------------------------------------------------*)

fun make_rhs ty rv tv (fl,(pv,(name,[rl,value,tl]))) =
   let val exrl = extract_list (type_of rl) rv rl
       val extl = extract_list (type_of tl) tv tl
       val svl = strip_inj value
       val extu = if fl then [] else extract_tuple (type_of pv) pv svl
       val args = exrl @ extu @ extl
       val v = mk_var{Name = name, Ty = itlist mk_fun_ty args ty}
   in
   (v,list_mk_comb(v,args))
   end;

(* ---------------------------------------------------------------------*)
(* make_conditional : make an iterated conditional. A call to:		*)
(*									*)
(*    make_conditional [`t1`;...;`tn`] [`x1`;...;`xn+1`]		*)
(*									*)
(* returns:								*)
(*									*)
(*    `(t1 => x1 | (t2 => x2 | ... | xn+1))]`				*)
(*									*)
(* Note that n can be zero, in which case the result is `x1`.		*)
(* ---------------------------------------------------------------------*)
fun make_conditional [] (h::_) = h
  | make_conditional (h1::t1) (h2::t2) =
        mk_cond {cond = h1, larm = h2, rarm = make_conditional t1 t2};

(* ---------------------------------------------------------------------*)
(* make_function : Make the function that extracts the values present on*)
(* the right-hand sides of each clause, and introduces separate function*)
(* variables for each clause.						*)
(* ---------------------------------------------------------------------*)

local fun isl (SOME _) = true
        | isl NONE = false
      fun mkflag l = (length l <> 1)
      fun nonrec l = not(Portable_List.exists isl l)
in
fun make_function atys th =
   let val cs = strip_conj(#Body(dest_abs(rand(concl th))))
       val (ef,ff) = (mkflag ## mkflag) (partition null atys)
       val names = gen_names (ef,ff) atys
       val (f,[rl,value,ts]) = strip_comb (rand(snd(strip_forall(hd cs))))
       val {Args = [resty],...} = dest_type(type_of rl)
       val rv = genvar (type_of rl)
       and tv = genvar (type_of ts)
       val (vv,tests) = mk_tests names (type_of value)
       val proj = mk_proj vv names (type_of value)
       val (vs,rs) = (flatten ## I)
                     (unzip(map ((I ## rand) o strip_forall) cs))
       val rhss = map (snd o strip_comb) rs
       val arg = zip (map nonrec atys) (zip proj (zip names rhss))
       val (vs,res) = unzip(map (make_rhs resty rv tv) arg)
   in
     (vs, list_mk_abs ([rv,vv,tv],make_conditional tests res))
   end
end;

(* =====================================================================*)
(* Procedures for simplifying the type axiom into its final form.	*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* PROJ_CONV : simplify right-projections of right-injections.		*)
(*									*)
(* A call to: PROJ_CONV `OUTR(OUTR ... (INR(INR x)))` returns:		*)
(*									*)
(*   |-  OUTR(OUTR ... (INR(INR x))) = x				*)
(* ---------------------------------------------------------------------*)

local val thm = sumTheory.OUTR
      fun rew tm =  REWR_CONV thm tm handle _ => (REFL tm)
in
fun PROJ_CONV tm =
   let val {Rator,Rand} = dest_comb tm
   in if #Name(dest_const Rator) = "OUTR"
      then let val th = AP_TERM Rator (PROJ_CONV Rand)
           in TRANS th (rew (rand(concl th)))
           end
      else REFL tm
   end handle _ => REFL tm
end;

(* ---------------------------------------------------------------------*)
(* TEST_SIMP_CONV : repeatedly simplify conditionals as follows:	*)
(*									*)
(*   (1)  TEST_SIMP_CONV `(ISL...(INL x)) => a | b` returns:		*)
(*									*)
(*	   |- (ISL...(INL x) => a | b) = a				*)
(* 									*)
(*   (2)  TEST_SIMP_CONV `(ISL...(INR x)) => a | b` returns:		*)
(*									*)
(*	   |- (ISL...(INR x) => a | b) = b				*)
(*									*)
(* where the dots `...` stand for any number of intermediate right	*)
(* projections of left injections as simplified by PROJ_CONV.		*)
(* ---------------------------------------------------------------------*)

local val thm = sumTheory.ISL
      val (th1,th2) = (SPEC (--`x:'a`--) ## SPEC (--`y:'b`--)) (CONJ_PAIR thm)
      val Tth = EQT_INTRO th1
      and Fth = EQF_INTRO th2
      val rewconv = FIRST_CONV [REWR_CONV Fth,REWR_CONV Tth]
in
fun TEST_SIMP_CONV cond =
   let val (C,[test,a,b]) = strip_comb cond
       val simp = ((RAND_CONV PROJ_CONV) THENC rewconv) test
       val thm2 = MK_COMB(AP_THM (AP_TERM C simp) a, TEST_SIMP_CONV b)
   in
   CONV_RULE (RAND_CONV COND_CONV) thm2
   end handle _ => REFL cond
end;


(* ---------------------------------------------------------------------*)
(* LIST_ELS : extract the elements of a list.				*)
(*									*)
(* Given `[x1;x2;...;xn]`, LIST_ELS produces a list of theorems:	*)
(*									*)
(* [|- HD [x1;x2;...;xn]      =     x1;					*)
(*     HD (TL [x1;x2;...;xn]) =     x2;					*)
(*     ... etc ...            = xn]					*)
(* ---------------------------------------------------------------------*)

local val alpha = mk_vartype "'a"
      val H = GENL [--`h:'a`--, --`t:'a list`-- ] (SPEC_ALL listTheory.HD)
      and T = GENL [--`h:'a`--, --`t:'a list`-- ] (SPEC_ALL listTheory.TL)
fun genels (hth,tth) (hf,tf) th =
   let val (_,[h,t]) = strip_comb(rand(concl th))
       val thm = TRANS (hf th) (SPEC t (SPEC h hth))
       val tthm = TRANS (tf th) (SPEC t (SPEC h tth))
   in
     thm::genels (hth,tth) (hf,tf) tthm
   end handle _ => []
in
fun LIST_ELS tm =
   let val lty = type_of tm
       val {Args = [ty],...} = dest_type lty
       val instf = INST_TYPE [alpha |-> ty]
       val hth = instf H
       and tth = instf T
       val hf = AP_TERM(mk_const{Name="HD",Ty = lty --> ty})
       val tf = AP_TERM(mk_const{Name="TL",Ty = lty --> lty})
   in
     genels (hth,tth) (hf,tf) (REFL tm)
   end
end;


(* ---------------------------------------------------------------------*)
(* GEN_PROJ_CONV : generate projections of sum-injections.		*)
(*									*)
(* A call to GEN_PROJ_CONV generates a theorem that projects a value	*)
(* which has been injected into a sum.  For example:			*)
(*									*)
(*   PROJ_CONV `INL x`     =  |- OUTL(INL x) = x			*)
(*   PROJ_CONV `INR(INL x)` = |- OUTL(OUTR(INR(INL x))) = x 		*)
(*   ... etc.								*)
(* ---------------------------------------------------------------------*)

local
val orth = sumTheory.OUTR
val olth = sumTheory.OUTL
val (v1,v2) = (==`:'a`==, ==`:'b`==)
fun inst t1 t2 = INST_TYPE[v1 |-> t1, v2 |-> t2]
fun conv th =
   let val inj = rand(concl th)
       val {Rator,Rand} = dest_comb inj
       val injty = type_of inj
       val {Args = [lty,rty],...} = dest_type injty
   in
   case (#Name(dest_const Rator))
     of "INR" => let val proj = mk_const{Name = "OUTR",Ty = injty --> rty}
                     val thm1 = AP_TERM proj th
                     val thm2 = SPEC Rand (inst lty rty orth)
                 in
                 conv (TRANS thm1 thm2)
                 end
      | "INL" => let val proj = mk_const{Name = "OUTL", Ty = injty --> lty}
                     val thm1 = AP_TERM proj th
                     val thm2 = SPEC Rand (inst lty rty olth)
                 in
                 conv (TRANS thm1 thm2)
                 end
      | _ => th
   end handle _ => th
in
fun GEN_PROJ_CONV tm = conv (REFL tm)
end;

(* ---------------------------------------------------------------------*)
(* TUPLE_COMPS : extract the components of a tuple.			*)
(*									*)
(* Given a theorem of the form:						*)
(*									*)
(*   |- tm = (x1,x2,...,xn)						*)
(*									*)
(* TUPLE_COMPS produces a list of theorems:				*)
(*									*)
(* [|- FST tm = x1;							*)
(*     FST(SND tm) = x2;						*)
(*      .								*)
(*      .								*)
(*     SND(...(SND tm)...) = xn]					*)
(*									*)
(* There are two special cases:						*)
(*									*)
(*  1) when given a theorem of the form |- tm = v, where v is a variable*)
(*     the function returns [|- tm = v].				*)
(* 									*)
(*  2) when given a theorem of the form |- tm = one, where one is the 	*)
(*     constant value of type one, the function returns [].		*)
(* ---------------------------------------------------------------------*)

local val onec = Term`one:one`
      val FST = pairTheory.FST
      val SND = pairTheory.SND
fun generate th =
   let val (_,[f,s]) = strip_comb(rand(concl th))
       val thm1 = ISPECL [f,s] FST
       val thm = TRANS (AP_TERM (rator(lhs(concl thm1))) th) thm1
       val thm2 = ISPECL [f,s] SND
       val tthm = TRANS (AP_TERM (rator(lhs(concl thm2))) th) thm2
   in
     thm::generate tthm
   end
   handle _ => [th]
in
fun TUPLE_COMPS th = if (rand(concl th) = onec) then [] else generate th
end;


(* ---------------------------------------------------------------------*)
(* SIMP_CONV : simplifies the conditional expression on the right-hand  *)
(* side of an equation.							*)
(* ---------------------------------------------------------------------*)

local fun itfn th1 th2 = MK_COMB(th2,th1)
in
fun SIMP_CONV tm =
   let val (vs,{Rator,Rand}) = (I ## dest_comb) (strip_forall tm)
       val thm1 = LIST_BETA_CONV Rand
       val cond = rand(concl thm1)
       val thm2 = TRANS thm1 (TEST_SIMP_CONV cond)
       val [l1,lab,l2] = snd(strip_comb Rand)
       val eqs1 = LIST_ELS l1 and eqs3 = LIST_ELS l2
       val eqs2 = TUPLE_COMPS (GEN_PROJ_CONV lab)
       val f = fst(strip_comb(rand(concl thm2)))
       val thm3 = rev_itlist itfn (eqs1 @ eqs2 @ eqs3) (REFL f)
       val thm = TRANS thm2 thm3
   in
   itlist FORALL_EQ vs (AP_TERM Rator thm)
   end
end;

(* ---------------------------------------------------------------------*)
(* SIMPLIFY : simplifies the type axiom into its final form.		*)
(* ---------------------------------------------------------------------*)

local val AND = --`$/\`--
      fun mkconj t1 t2 = MK_COMB(AP_TERM AND t1,t2)
in
fun SIMPLIFY th =
   let val {Rator,Rand} = dest_comb(concl th)
       val {Bvar,Body} = dest_abs Rand
       val thm = CONJS_CONV SIMP_CONV Body
   in
   EQ_MP (AP_TERM Rator (ABS Bvar thm)) th
   end
end;

(* =====================================================================*)
(* Now, the main program						*)
(* =====================================================================*)

local val TYDEFTHM = rec_typeTheory.TY_DEF_THM
      val alpha = mk_vartype "'a"
      and beta  = mk_vartype "'b"
      and delta = mk_vartype "'c"
in
fun dtype{save_name,ty_name,clauses} =
 let val (cs,atys,fixities) =
        itlist (fn {constructor,args,fixity} => fn (C,A,F) =>
                           (constructor::C, args::A, fixity::F))
                            clauses ([],[],[])
     val isodef = ty_name^"_ISO_DEF"
     val ABS = "ABS_"^ty_name
     and REP = "REP_"^ty_name
     val pred = mk_subset_pred atys
     val eth = prove_existence_thm pred
     val predtm = rator(#Body(dest_exists(concl eth)))
     val tyax = new_type_definition{name=ty_name,pred=predtm,inhab_thm=eth}
     val ARth = define_new_type_bijections
                  {name=isodef,ABS=ABS,REP=REP,tyax=tyax}
     val rty = hd(#Args(dest_type(type_of pred)))
     val newty = hd(#Args(dest_type(type_of(#Bvar(dest_exists(concl tyax))))))
     val resty = variant_tyvar (type_vars rty) ["'a"]
     val Pthm = INST_TYPE[alpha|->rty, beta|->newty, delta|->resty] TYDEFTHM
     val {Rator,Rand} =
            dest_comb(lhs(#Body(dest_forall(rand(rator(concl ARth))))))
     val R = rator Rand
     val Sthm = MP (SPEC pred (SPEC Rator (SPEC R Pthm))) ARth
     val (f,trans) = TRANSFORM R Sthm
     val defns = DEFINE_CONSTRUCTORS cs atys fixities trans
     val (fs,funct) = make_function atys defns
     val newfs = INST [f |-> funct] defns
     val abstax = GENL fs (SIMPLIFY newfs)
 in
   save_thm(save_name,abstax)
 end
end;

(* ---------------------------------------------------------------------*)
(* define_type: construct a user-specified concrete recursive type and  *)
(* derive an abstract characterization of it.				*)
(*									*)
(* E.g. define_type name `ty = C1 of 'a                                 *)
(*                           | C2 of ty => 'a                           *)
(*                           | C3 of ty => ty` defines:                 *)
(*									*)
(*	1) a type operator ('a)ty					*)
(*	2) constants C1:'a->('a)ty, 					*)
(*		     C2:('a)ty->'a->('a)ty,				*)
(*		     C3:('a)ty->('a)ty->('a)ty				*)
(*									*)
(* and proves that ty has the following property:			*)
(*									*)
(*	|- !f0 f1 f2. ?!fn.						*)
(*               (!x. fn(C1 x) = f0 x) /\				*)
(*             (!x t. fn(C2 t x) = f1(fn t)x t) /\              	*)
(*	      (!t t'. fn(C3 t t') = f2(fn t)(fn t')t t')		*)
(*									*)
(* the axiom is stored under `name` and is returned.			*)
(* ---------------------------------------------------------------------*)

fun enumerate L =
  rev(snd(rev_itlist (fn x => fn (n,A) => (n+1, (n,x)::A)) L (1,[])));

fun map_enum f l = map f (enumerate l)

fun ERR1 i s =
  let val clstr = String.concat
       ["parse_tyspec.make_type_clause ",
        "(clause ", int_to_string i, ")"]
  in
   raise (ERR clstr s)
  end;

fun info {origin_structure, origin_function,message}
  = String.concat [origin_function,": ",message];

local open Pretype
in
fun make_type i pty = SOME (pretype2type name_of pty)
   handle Exception.HOL_ERR triple => ERR1 i (info triple)
end;

(* Does a name occur in a pretype or a type *)
local open Pretype
in
fun tyocc n ty =
  if is_vartype ty then (dest_vartype ty=n)
  else let val {Tyop,Args} = dest_type ty
       in Tyop=n orelse exists (tyocc n) Args
       end
fun occurs name_of n (tyVar s) = (n=name_of s)
  | occurs name_of n (tyAntiq ty) = tyocc n ty
  | occurs name_of n (tyApp(x,l)) =
      (n=name_of x) orelse exists (occurs name_of n) l
end;

fun make_type_clause tyname (i,(constructor, args)) =
 let open Pretype
     fun munge (pty as tyApp(gr,args)) =
            if name_of gr=tyname
            then if null args then NONE  (* found OK occ. of tyname *)
                 else ERR1 i "explicit argument(s) to proposed type"
            else if occurs name_of tyname pty
                 then ERR1 i ("nested occurrence of "^Lib.quote tyname)
                 else make_type i pty
        | munge pty = make_type i pty  (* type vars and antiquotes *)
 in
    {constructor=constructor, args = map munge args}
 end;

fun parse_tyspec q =
   case ParseDatatype.parse q
    of [(name,clauses)] =>
           {ty_name=name, clauses=map_enum (make_type_clause name) clauses}
     | [] => raise ERR "parse_tyspec" "empty type specification"
     | _ => raise ERR "parse_tyspec" "more than one type specified";

fun define_type {name=save_name, type_spec, fixities} =
   let val {ty_name,clauses} = parse_tyspec type_spec
   in
      dtype{save_name=save_name, ty_name=ty_name,
            clauses = map2 (fn {constructor,args} => fn f =>
                                 {constructor=constructor,args=args,fixity=f})
                           clauses fixities}
   end;

fun string_define_type s1 s2 fixities =
      define_type{name=s1, type_spec=[QUOTE s2], fixities = fixities};

(* =====================================================================
   TESTS:

new_theory "temp";

val void_Axiom = define_type{name="void_Axiom" ,
                             type_spec= `void = Void`,
                             fixities = [Prefix]};

val pair = define_type{name="pair",
                       type_spec= `pair = CONST of 'a#'b`,
                       fixities = [Prefix]};

val onetest = define_type{name="onetest",
                          type_spec=`onetest = OOOO of one`,
                          fixities = [Prefix]};

val tri_Axiom =  define_type{name="tri_Axiom",
                            type_spec=`tri = Hi | Lo | Fl`,
                            fixities = [Prefix,Prefix,Prefix]};

val iso_Axiom =  define_type{name="iso_Axiom",
                             type_spec=`iso = ISO of 'a`,
                             fixities = [Prefix]};

val List_Axiom = define_type{name="List_Axiom",
                             type_spec=`List = Nil | :: of 'a => List`,
                             fixities = [Prefix,Infix 40]};

val ty_Axiom = define_type{name="ty_Axiom",
        type_spec = `ty = C1 of 'a
                        | C2
                        | C3 of 'a => 'b => ty
                        | C4 of ty => 'c => ty => 'a => 'b
                        | C5 of ty => ty`,
        fixities = [Prefix, Prefix, Prefix, Prefix, Prefix]};

define_type{name="bintree",
            type_spec=`bintree = LEAF of 'a
                               | TREE of bintree => bintree`,
            fixities = [Prefix,Prefix]};

define_type{name="seven",
            type_spec= `typ = C of one
                                   => (one#one)
                                   => (one -> one -> 'a list)
                                   => ('a,one#one,'a list) ty`,
            fixities = [Prefix]};

define_type{name="seven'",
            type_spec= `Typ = D of one # (one#one) # (one -> one -> 'a list)
                                   # ('a,one#one,'a list) ty`,
            fixities = [Prefix]};

===================================================================== *)

end; (* Define_type *)
