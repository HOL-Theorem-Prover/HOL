(* ===================================================================== *)
(* FILE          : Type_def_support.sml                                  *)
(* DESCRIPTION   : Routines supporting the definition of types.          *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Type_def_support :> Type_def_support =
struct

open HolKernel Parse Drule boolTheory;

infix |->;

fun TYPE_DEF_SUPPORT_ERR function message =
    Exception.HOL_ERR{origin_structure = "Type_def_support",
		      origin_function = function,
		      message = message}

(* --------------------------------------------------------------------- *)
(* NAME: define_new_type_bijections 					*)
(*									*)
(* DESCRIPTION: define isomorphism constants based on a type definition.*)
(*									*)
(* USAGE: define_new_type_bijections name ABS REP tyax                  *)
(*									*)
(* ARGUMENTS: tyax -- a type-defining axiom of the form returned by	*)
(*		     new_type_definition. For example:			*)
(*									*)
(* 			?rep. TYPE_DEFINITION P rep			*)
(*									*)
(*            ABS  --- the name of the required abstraction function    *)
(*									*)
(*            REP  --- the name of the required representation function *)
(*									*)
(*            name --- the name under which the definition is stored    *)
(*									*)
(* SIDE EFFECTS:    Introduces a definition for two constants `ABS` and *)
(*                  (--`REP`--) by the constant specification:          *)
(*									*)
(*  		   |- ?ABS REP. (!a. ABS(REP a) = a) /\                 *)
(*                              (!r. P r = (REP(ABS r) = r)             *)
(*									*)
(*                 The resulting constant specification is stored under *)
(*                 the name given as the first argument.                *)
(*									*)
(* FAILURE: if    1) ABS or REP are already constants.                  *)
(*                2) not in draft mode.                                 *)
(*                3) input theorem of wrong form.			*)
(*									*)
(* RETURNS: The defining property of the representation and abstraction *)
(*          functions, given by:                                        *)
(*             								*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(* ---------------------------------------------------------------------*)

local val alpha = ==`:'a`==
      val beta = ==`:'b`==
      fun ty_subst ty1 ty2 = [{redex = beta, residue = ty1},
                              {redex = alpha, residue = ty2}]
in
fun define_new_type_bijections{name,ABS,REP,tyax} =
  if not(null (hyp tyax))
  then raise TYPE_DEF_SUPPORT_ERR
                 "define_new_type_bijections"
                 "input theorem must have no assumptions"
  else let val (_,[P,rep]) = strip_comb(#Body(dest_exists(concl tyax)))
           val {Args=[a,r],...} = Type.dest_type (type_of rep)
           val eth = MP (SPEC P (INST_TYPE (ty_subst a r) ABS_REP_THM)) tyax
       in
        Parse.new_specification
                {name=name, sat_thm=eth,
                 consts = [{const_name = REP, fixity = Prefix},
                           {const_name = ABS, fixity = Prefix}]}
      end
 handle HOL_ERR _ => raise TYPE_DEF_SUPPORT_ERR "define_new_type_bijections" ""
end;

(* ---------------------------------------------------------------------*)
(* NAME: prove_rep_fn_one_one	 					*)
(*									*)
(* DESCRIPTION: prove that a type representation function is one-to-one.*)
(*									*)
(* USAGE: if th is a theorem of the kind returned by the ML function	*)
(*        define_new_type_bijections:					*)
(*									*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(*									*)
(*	 then prove_rep_fn_one_one th will prove and return a theorem	*)
(*	 stating that the representation function REP is one-to-one:	*)
(*									*)
(*	    |- !a a'. (REP a = REP a') = (a = a')			*)
(*									*)
(* ---------------------------------------------------------------------*)

fun prove_rep_fn_one_one th =
   let val thm = CONJUNCT1 th
       val {Body, ...} = dest_forall(concl thm)
       val {Rator = A, Rand} = dest_comb(lhs Body)
       val {Rator = R, ...} = dest_comb Rand
       val {Args = [aty,rty],...} = Type.dest_type (type_of R)
       val a = mk_primed_var{Name = "a", Ty = aty}
       val a' = variant [a] a
       val a_eq_a' = mk_eq{lhs = a, rhs = a'}
       and Ra_eq_Ra' = mk_eq{lhs = mk_comb{Rator = R, Rand = a},
                             rhs = mk_comb{Rator = R, Rand = a'}}
       val th1 = AP_TERM A (ASSUME Ra_eq_Ra')
       val ga1 = genvar aty
       and ga2 = genvar aty
       val th2 = SUBST [ga1 |-> SPEC a thm, ga2 |-> SPEC a' thm]
                       (mk_eq{lhs = ga1, rhs = ga2}) th1
       val th3 = DISCH a_eq_a' (AP_TERM R (ASSUME a_eq_a'))
   in
   GEN a (GEN a' (IMP_ANTISYM_RULE (DISCH Ra_eq_Ra' th2) th3))
   end
   handle HOL_ERR _ => raise TYPE_DEF_SUPPORT_ERR "prove_rep_fn_one_one"  "";

(* --------------------------------------------------------------------- *)
(* NAME: prove_rep_fn_onto	 					*)
(*									*)
(* DESCRIPTION: prove that a type representation function is onto. 	*)
(*									*)
(* USAGE: if th is a theorem of the kind returned by the ML function	*)
(*        define_new_type_bijections:					*)
(*									*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(*									*)
(*	 then prove_rep_fn_onto th will prove and return a theorem	*)
(*	 stating that the representation function REP is onto:		*)
(*									*)
(*	    |- !r. P r = (?a. r = REP a)				*)
(*									*)
(* --------------------------------------------------------------------- *)

fun prove_rep_fn_onto th =
   let val [th1,th2] = CONJUNCTS th
       val {Bvar,Body} = dest_forall(concl th2)
       val {rhs = eq, ...} = dest_eq Body
       val {Rator = RE, Rand = ar} = dest_comb(lhs eq)
       val a = mk_primed_var {Name = "a", Ty = type_of ar}
       val sra = mk_eq{lhs = Bvar, rhs = mk_comb{Rator = RE, Rand = a}}
       val ex = mk_exists{Bvar = a, Body = sra}
       val imp1 = EXISTS (ex,ar) (SYM(ASSUME eq))
       val v = genvar (type_of Bvar)
       and A = rator ar
       and ass = AP_TERM RE (SPEC a th1)
       val th = SUBST[v |-> SYM(ASSUME sra)]
                     (mk_eq{lhs = mk_comb{Rator = RE,
                                          Rand = mk_comb{Rator = A, Rand = v}},
                            rhs = v})
                     ass
       val imp2 = CHOOSE (a,ASSUME ex) th
       val swap = IMP_ANTISYM_RULE (DISCH eq imp1) (DISCH ex imp2)
   in
   GEN Bvar (TRANS (SPEC Bvar th2) swap)
   end
   handle HOL_ERR _ => raise TYPE_DEF_SUPPORT_ERR "prove_rep_fn_onto" "";

(* ---------------------------------------------------------------------*)
(* NAME: prove_abs_fn_onto	 					*)
(*									*)
(* DESCRIPTION: prove that a type abstraction function is onto. 	*)
(*									*)
(* USAGE: if th is a theorem of the kind returned by the ML function	*)
(*        define_new_type_bijections:					*)
(*									*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(*									*)
(*	 then prove_abs_fn_onto th will prove and return a theorem	*)
(*	 stating that the abstraction function ABS is onto:		*)
(*									*)
(*	    |- !a. ?r. (a = ABS r) /\ P r				*)
(*									*)
(* ---------------------------------------------------------------------*)

fun prove_abs_fn_onto th =
   let val [th1,th2] = CONJUNCTS th
       val {Bvar = bv_th1,Body} = dest_forall(concl th1)
       val {Rator = A,Rand} = dest_comb(lhs Body)
       val {Rator = R,...} = dest_comb Rand
       val rb = mk_comb{Rator = R, Rand = bv_th1}
       val bth1 = SPEC bv_th1 th1
       val thm1 = EQT_ELIM(TRANS (SPEC rb th2) (EQT_INTRO (AP_TERM R bth1)))
       val thm2 = SYM bth1
       val {Bvar = r, Body} = dest_forall(concl th2)
       val P = rator(lhs Body)
       val ex = mk_exists{Bvar = r,
                          Body=mk_conj{conj1=mk_eq{lhs = bv_th1,
                                                   rhs = mk_comb{Rator = A,
                                                                 Rand = r}},
                                       conj2 = mk_comb{Rator = P, Rand = r}}}
   in
   GEN bv_th1 (EXISTS(ex,rb) (CONJ thm2 thm1))
   end
   handle HOL_ERR _ => raise TYPE_DEF_SUPPORT_ERR "prove_abs_fn_onto" "";


(* ---------------------------------------------------------------------*)
(* NAME: prove_abs_fn_one_one	 					*)
(*									*)
(* DESCRIPTION: prove that a type abstraction function is one-to-one. 	*)
(*									*)
(* USAGE: if th is a theorem of the kind returned by the ML function	*)
(*        define_new_type_bijections:					*)
(*									*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(*									*)
(*	 then prove_abs_fn_one_one th will prove and return a theorem	*)
(*	 stating that the abstraction function ABS is one-to-one:	*)
(*									*)
(*	    |- !r r'. P r ==>						*)
(*		      P r' ==>						*)
(*		      (ABS r = ABS r') ==> (r = r')			*)
(*									*)
(* ---------------------------------------------------------------------*)

fun prove_abs_fn_one_one th =
   let val [th1,th2] = CONJUNCTS th
       val {Bvar = r, Body} = dest_forall(concl th2)
       val P = rator(lhs Body)
       val {Rator = A,Rand} = dest_comb(lhs(#Body(dest_forall(concl th1))))
       val R = rator Rand
       val r' = variant [r] r
       val r_eq_r' = mk_eq {lhs = r, rhs = r'}
       val Pr = mk_comb{Rator = P, Rand = r}
       val Pr' = mk_comb{Rator = P, Rand = r'}
       val as1 = ASSUME Pr
       and as2 = ASSUME Pr'
       val t1 = EQ_MP (SPEC r th2) as1
       and t2 = EQ_MP (SPEC r' th2) as2
       val eq = mk_eq{lhs = mk_comb{Rator = A, Rand = r},
                      rhs = mk_comb{Rator = A, Rand = r'}}
       val v1 = genvar(type_of r)
       and v2 = genvar(type_of r)
       val i1 = DISCH eq
                  (SUBST [v1 |-> t1, v2 |-> t2] (mk_eq{lhs=v1, rhs=v2})
                       (AP_TERM R (ASSUME eq)))
       and i2    = DISCH r_eq_r' (AP_TERM A (ASSUME r_eq_r'))
       val thm   = IMP_ANTISYM_RULE i1 i2
       val disch = DISCH Pr (DISCH Pr' thm)
   in
     GEN r (GEN r' disch)
   end
   handle HOL_ERR _ => raise TYPE_DEF_SUPPORT_ERR "prove_abs_fn_one_one"  "";

end; (* Type_def_support *)
