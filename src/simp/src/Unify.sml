(*------------------------------------------------------------------------
 *  First order unification restricted to specified "scheme" variables.
 *
 *----------------------------------------------------------------------*)

structure Unify :> Unify = struct

open HolKernel Psyntax liteLib Abbrev;
infix 5 |->;

val ERR = mk_HOL_ERR "Unify";

fun lookup x [] = raise ERR "lookup" "not found"
  | lookup x ({redex,residue}::t) =
      if aconv redex x then residue else lookup x t;

fun deref_tmenv env tm =
  if is_var tm then lookup tm env handle HOL_ERR _ => tm
               else tm;

fun restrict_tmenv P E =
 mapfilter (fn {redex,residue} =>
              if P redex then redex |-> deref_tmenv E redex else fail()) E;

fun occ env v =
    let fun f t =
	exists (fn fv => aconv fv v orelse f (lookup fv env)
		handle HOL_ERR _ => false) (free_vars t)
	handle HOL_ERR _ => false
    in f
    end;

fun bind env v t = if occ env v t then failwith "occurs" else
   let
     val new_sub = v |-> subst env t;
     val env' = map (fn {redex,residue} => (redex |-> (subst [new_sub] residue))) env
   in  new_sub::env' end

(*---------------------------------------------------------------------------
   The following code assumes things have been renamed.
 ---------------------------------------------------------------------------*)

fun simp_unify_terms_in_env consts tm1 tm2 env =
 let val tm1' = deref_tmenv env tm1
     val tm2' = deref_tmenv env tm2
 in
   if is_var tm1' andalso not (op_mem aconv tm1' consts)
   then if is_var tm2' andalso not (op_mem aconv tm2' consts)
        then if aconv tm1' tm2' then env else bind env tm1' tm2'
        else bind env tm1' tm2'
   else
   if is_var tm2' andalso not (op_mem aconv tm2' consts)
   then bind env tm2' tm1'
   else
   case (dest_term tm1',dest_term tm2')
    of (VAR x, VAR y) => if aconv tm1' tm2' then env
                         else failwith "unify_terms"
     | (COMB p1,COMB p2) =>
         simp_unify_terms_in_env consts (fst p1) (fst p2)
           (simp_unify_terms_in_env consts (snd p1) (snd p2) env)
     | (LAMB p1,LAMB p2) =>
        let fun filt v = not (aconv v (fst p1)) andalso not (aconv v (fst p2))
        in restrict_tmenv filt
             (simp_unify_terms_in_env
                (op_set_diff aconv consts [fst p1, fst p2]) (snd p1) (snd p2)
                (restrict_tmenv filt env))
	    end
     | otherwise => if aconv tm1' tm2' then env else failwith "simp_unify_terms"
    end;


fun simp_unify_terms consts tm1 tm2 =
   simp_unify_terms_in_env consts tm1 tm2 [];

end (* struct *)


(*
simp_unify_terms [] ``2 <= x`` ``m <= m``
SATISFY_CONV ([], [arithmeticTheory.LESS_EQ_REFL]) ``?x. 2 <= x``

simp_unify_terms [] ``f(X) /\ g(Y+2)`` ``f(2+2) /\ g(2 + Y)``

simp_unify_terms [`b:'a`] `P (x:'a) (b:'a):bool` `P (a:'a) (b:'a):bool`;;
, `!x y:'a. Q x y`, `!z:'a. R x z`];
fun S facts = satisfy1 (U (map (freesl o hyp) facts)) (map concl facts);
S facts `?a b:'a. P a b /\ R a b`;


occ [(--`x:num`--) |-> (--`1 + 1`--)] (--`z:num`--) (--`z + x`--);
occ [(--`x:num`--) |-> (--`z + 1`--)] (--`z:num`--) (--`x + x`--);
occ [(--`x:num`--) |-> (--`z + 1`--)] (--`z:num`--) (--`y + y`--);
occ [(--`x:num`--) |-> (--`z + 1`--)] (--`z:num`--) (--`\z. z = 1`--);


*)
