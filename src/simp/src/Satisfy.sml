structure Satisfy :> Satisfy =
struct

open HolKernel boolLib Sequence liteLib Unify Trace;

(*-----------------------------------------------------------------
 * satisfy_in_envs
 *
 * return all the unifications of a single term against a sequence of terms,
 * over a sequence of environments.
 * Do not return instantiations local to the terms from the sequence
 * This corresponds to matching a goal against a series of facts, where
 * some of the facts are universally quantified.
 *
 * satisfyl_in_envs
 *
 * This correpsonds to unifying a set of subgoals with unknowns
 * against a set of facts.
 *
 * satisfyl
 *
 * Satisfy a list of goals via a set of facts.
 *----------------------------------------------------------------*)

fun satisfy_in_envs consts tms (tm1,envs) =
  let fun f env tm2 =
      let val new_env = simp_unify_terms_in_env consts tm1 tm2 env
      in restrict_tmenv (not o C (op_mem eq) (free_vars tm2)) new_env
      end
  in seq_flat (seq_map (fn env => seq_mapfilter (f env) tms) envs)
  end;

fun satisfyl_in_envs consts tms1 tms2 envs =
    seq_iterate (satisfy_in_envs consts (seq_of_list tms2))
    (seq_of_list tms1,envs);

fun satisfy consts tms1 tms2 =
    seq_hd (satisfyl_in_envs consts tms1 tms2 (seq_single []))
    handle HOL_ERR _ => failwith "satisfy: could not satisfy goals";

(*==================================================================
 * Existential Satisfaction
 *
 * These are reasoning tools based on satisfaction via unification,
 * designed to find suitable instantiations of existential variables
 * for trivial cases.
 *
 * SATISFY_CHOOSE_TAC
 *  constructs a tactics which will choose
 *  values for existentials iff all conjuncts can be satisfied
 *  by the given facts
 *================================================================*)

local
   fun firsttys ({redex=inL redex, residue=inL residue} :: rs) =
         let val (tyS,rs') = firsttys rs
         in ((redex |-> residue) :: tyS, rs')
         end
     | firsttys rs = ([], rs)
   fun firsttms ({redex=inR redex, residue=inR residue} :: rs) =
         let val (tmS,rs') = firsttms rs
         in ((redex |-> residue) :: tmS, rs')
         end
     | firsttms rs = ([], rs)
in
fun ty_tm_subst [] tm = tm
  | ty_tm_subst S tm =
      let val (tyS,S1) = firsttys S
          val (tmS,S2) = firsttms S1
          val tm' = ty_tm_subst S2 tm
      in inst tyS (subst tmS tm')
      end
end

type factdb = (term list * thm list)  (* this may change *)

fun satisfy1 (consts,facts) gl =
  let val (vars,g) = strip_all_exists gl
      val _ = if null vars then failwith "satisfy1" else ()
      val _ = trace(3,REDUCE("trying SATISFY on",g))
      val S = map (fn inR v => inR v |-> inR (genvar (type_of v))
                    | inL a => inL a |-> inL (gen_var_type (kind_of a))
                  ) vars  (* rename to avoid clashes *)
(*
      val tmvars = mapfilter outR vars
      val tyvars = mapfilter outL vars
      val gvars = map (genvar o type_of) tmvars
      val gtyvars = map (fn a => gen_var_type (kind_of a, rank_of a)) tyvars
      val g' = subst (map2 (curry op |->) vars gvars) g
*)
      val g' = ty_tm_subst S g
      val tmvars = mapfilter outR vars
      val tyvars = mapfilter outL vars
      val gtyvars = mapfilter (outL o #residue) S
      val tyS = map (op |->) (zip tyvars gtyvars)
      val gvars = mapfilter (inst tyS o outR o #residue) S
      val goals = strip_conj g'
      fun get_body t = snd (dest_forall t) handle HOL_ERR _ => snd (dest_tyforall t)
      val facts' = map (repeat get_body) facts
   (* val facts' = map (snd o strip_all_forall) facts *)
      fun choose choices v =
        deref_tmenv choices v handle HOL_ERR _ => mk_select(v,T)
      val choices = satisfy (op_union eq consts (free_vars gl)) goals facts'
  in map (choose choices) gvars
  end;

fun SATISFY (consts,facts) gl =
    let val choices = satisfy1 (consts,map concl facts) gl
    in TAC_PROOF ((op_U eq (map hyp facts),gl),EVERY (map EXISTS_TAC choices) THEN
                  REPEAT CONJ_TAC THEN FIRST (map MATCH_ACCEPT_TAC facts))
    end;


fun SATISFY_CONV factdb tm =
    let val thm = EQT_INTRO (SATISFY factdb tm)
    in trace(1,PRODUCE(tm,"SATISFY",thm)); thm
    end;

fun SATISFY_TAC (asms,gl) =
  CONV_TAC (SATISFY_CONV (free_varsl asms,map ASSUME asms)) (asms,gl);

fun GSPEC thm = SPEC(genvar(type_of(bvar(rand(concl thm))))) thm;
fun TY_GSPEC thm = let val a = btyvar(rand(concl thm))
                   in TY_SPEC(gen_var_type (kind_of a)) thm
                   end;
fun FACT_CANON thm =
  if (is_conj (concl thm)) then flatten (map FACT_CANON (CONJUNCTS thm))
  else if (is_forall (concl thm)) then FACT_CANON(GSPEC thm)
       else if (is_tyforall (concl thm)) then FACT_CANON(TY_GSPEC thm)
       else [thm];;


fun add_facts (consts,facts) thms =
  (op_union eq consts (op_U eq (map (free_varsl o hyp) thms)),
   flatten (map FACT_CANON thms)@facts);

end (* struct *)



(*

TESTS:

Assumption usage problems: (corrected)

SIMP_QCONV tspec_ss [] (--`!c'.
    T_SPEC(p,c,q) /\ T_SPEC(q,c',r) ==> T_SPEC(p,MK_SEQ(c,c'),r)`--);
SIMP_CONV tspec_ss [] (--`
    T_SPEC(p,c,q) /\ T_SPEC(q,c',r) ==> T_SPEC(p,MK_SEQ(c,c'),r)`--);

fun mk_facts tms = concat (map (FACT_CANON o ASSUME) tms);
val facts = mk_facts
val facts = mk_facts [`!x:'a. P x (b:'a)`, `!x y:'a. Q x y`, `!z:'a. R x z`];
fun S f =
  let val facts = mk_facts f
      in satisfy1 (U (map (freesl o hyp) facts)) (map concl facts)
        end;
S [`!x:'a. P x (b:'a)`]  `?a b:'a. P a b`;
S [`P (a:'a) (b:'a):bool`]  `?a b:'a. P a b`;
S [`!x:'a. P x (a:'a):bool`]  `?b:'a. P a b`;
S [`!x:'a. P x (a:'a):bool`,`Q (a:'a):bool`]  `?b:'a. P a b /\ Q b`;
S [`!x:'a. P x (a:'a):bool`,`Q (b:'a):bool`]  `?b:'a. P a b /\ Q b`; (* NO *)
S [`!z:'a. R (x:'a) z`] `R (x:'a) z`;
S [`!x:'a. P x (b:'a)`, `!z:'a. R (x:'a) z`] `?a b:'a. P a b`;
S [`!x:'a. P x (b:'a)`, `Q (a:'a) (b:'a):bool`, `!z:'a. R (x:'a) z`] `?a b:'a. P a b /\ R (x:'a) (z:'a) /\ Q a b`;


open Satisfy;
val a = `a:'a`;
val b = `b:'a`;
val c = `c:'a`;
val e = `e:'a`;
val g = `g:'a`;
val m = `m:num`;
val n = `n:num`;
val x = `x:'a`;
val y = `y:'a`;
val z = `z:'a`;
val P = `(P:'a->'a->'a->bool)`;

list_of_s (satisfyl [`^(P) a b c`--,([a,b,c],[]))] [`^(P) g e f`--,([],[]))]);
list_of_s (satisfyl [`^(P) a b c`--,([a,b],[]))] [`^(P) g e f`--,([],[]))]);
list_of_s (satisfyl
            [`^(P) a b c`--,([a,b,c],[]))]
            [`^(P) g e f`--,([],[])),
             `^(P) x y z`--,([],[]))]);
list_of_s (satisfyl
            [`^(P) a b a`--,([a,b],[]))]
            [`^(P) g e g`--,([],[])),
             `^(P) x y z`--,([],[]))]);
list_of_s (satisfyl
            [`^(P) a b a`--,([a,b],[]))]
            [`^(P) g e g`--,([],[])),
             `^(P) x y z`--,([z],[]))]);

(* this one's a bit odd - the substitutions returned are empty because
neither a nor b need get bound.
*)
list_of_s (satisfyl
            [`^(P) a b a`--,([a,b],[]))]
            [`^(P) g e g`--,([g,e,g],[])),
             `^(P) x y z`--,([x,y,z],[]))]);
list_of_s (satisfyl
            [`^(P) a b a`--,([a,b],[])),
             `^(Pnum) 1 2 n`--,([n],[]))]
            [`^(P) g e g`--,([g,e,g],[])),
             `^(P) x y z`--,([x,y,z],[]))]);

list_of_s (satisfyl
            [`^(P) a b a`--,([a,b],[])),
             `^(Pnum) 1 2 n`--,([n],[]))]
            [`^(P) g e g`--,([],[])),
             `^(Pnum) 1 2 m`--,([],[]))]);



*)
