(*------------------------------------------------------------------------
 *  First order unification restricted to specified "scheme" variables.
 *
 *----------------------------------------------------------------------*)

structure Unify :> Unify = struct

open HolKernel Psyntax liteLib;
infix 5 |->;

type term = Term.term

fun deref_tmenv env tm =
  if is_var tm then rev_assoc tm env handle HOL_ERR _ => tm
  else tm;

fun restrict_tmenv f E =
    mapfilter (fn (y,x) => if f x then (x |-> deref_tmenv E x) else fail()) E;

fun occ env v =
    let fun f t =
	exists (fn fv => (fv = v) orelse f (rev_assoc fv env)
		handle HOL_ERR _ => false) (free_vars t)
	handle HOL_ERR _ => false
    in f
    end;

fun bind env v t = if occ env v t then failwith "occurs" else (v |-> t)::env;

(* assumes things have been renamed *)
fun simp_unify_terms_in_env consts tm1 tm2 env =
    let val tm1' = deref_tmenv env tm1
        val tm2' = deref_tmenv env tm2
    in 
      if (is_var tm1') andalso not (mem tm1' consts) then
        if (is_var tm2') andalso not (mem tm2' consts) then
          if (tm1' = tm2') then env else bind env tm1' tm2'
        else bind env tm1' tm2'
      else if (is_var tm2') andalso not (mem tm2' consts) then 
        bind env tm2' tm1'
      else case (dest_term tm1',dest_term tm2') of
        (VAR x, VAR y) => if (tm1'=tm2') then env else  failwith "unify_terms"
      | (COMB p1,COMB p2) =>
            simp_unify_terms_in_env consts (#Rator p1) (#Rator p2)
            (simp_unify_terms_in_env consts (#Rand p1) (#Rand p2) env)
      | (LAMB p1,LAMB p2) =>
	    let fun filt v = v <> (#Bvar p1) andalso v <> (#Bvar p2)
            in restrict_tmenv filt
		(simp_unify_terms_in_env 
		 (subtract consts [#Bvar p1,#Bvar p2]) (#Body p1) (#Body p2) 
		 (restrict_tmenv filt env))
	    end

      | _ => if (tm1'=tm2') then env else failwith "simp_unify_terms"
    end;



fun simp_unify_terms consts tm1 tm2 = 
   simp_unify_terms_in_env consts tm1 tm2 [];

end (* struct *)


(*
simp_unify_terms [`b:'a`] `P (x:'a) (b:'a):bool` `P (a:'a) (b:'a):bool`;;
, `!x y:'a. Q x y`, `!z:'a. R x z`];
fun S facts = satisfy1 (U (map (freesl o hyp) facts)) (map concl facts);
S facts `?a b:'a. P a b /\ R a b`;


occ [(--`x:num`--) |-> (--`1 + 1`--)] (--`z:num`--) (--`z + x`--);
occ [(--`x:num`--) |-> (--`z + 1`--)] (--`z:num`--) (--`x + x`--);
occ [(--`x:num`--) |-> (--`z + 1`--)] (--`z:num`--) (--`y + y`--);
occ [(--`x:num`--) |-> (--`z + 1`--)] (--`z:num`--) (--`\z. z = 1`--);


*)


