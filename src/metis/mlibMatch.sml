(* ========================================================================= *)
(* MATCHING AND UNIFICATION                                                  *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "Mosml", "mlibTerm"];
*)

(*
*)
structure mlibMatch :> mlibMatch =
struct

open mlibUseful mlibTerm;

infixr |-> ::>;

type subst        = mlibSubst.subst;
val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun raw_match env x tm =
  (case mlibSubst.find_redex x env of NONE => (x |-> tm) ::> env
   | SOME tm' =>
     if tm = tm' then env
     else raise ERR "match" "one var trying to match two different terms");

fun matchl env [] = env
  | matchl env ((Var x, tm) :: rest) = matchl (raw_match env x tm) rest
  | matchl env ((Fn (f, args), Fn (f', args')) :: rest) =
  if f = f' andalso length args = length args' then
    matchl env (zip args args' @ rest)
  else raise ERR "match" "can't match two different functions"
  | matchl _ _ = raise ERR "match" "different structure";

fun match tm tm' = mlibSubst.norm (matchl |<>| [(tm, tm')]);

local
  fun conv (Atom (r, args), Atom (r', args')) =
    SOME (Fn (r, args), Fn (r', args'))
    | conv (Not p, Not q) = conv (p, q)
    | conv (True, True) = NONE
    | conv (False, False) = NONE
    | conv _ = raise ERR "match_literals" "incompatible";
in
  fun matchl_literals sub work = matchl sub (List.mapPartial conv work);
end;

fun match_literals lit lit' = mlibSubst.norm (matchl_literals |<>| [(lit, lit')]);

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun occurs v tm = mem v (FVT tm);

  fun solve env [] = env
    | solve env ((tm1, tm2) :: rest) =
    solve' env (term_subst env tm1) (term_subst env tm2) rest
  and solve' env (Var x) tm rest =
    if Var x = tm then solve env rest
    else if occurs x tm then raise ERR "unify" "occurs check"
    else
      (case mlibSubst.find_redex x env of NONE
         => solve (mlibSubst.refine env ((x |-> tm) ::> |<>|)) rest
       | SOME tm' => solve' env tm' tm rest)
    | solve' env tm (tm' as Var _) rest = solve' env tm' tm rest
    | solve' env (Fn (f, args)) (Fn (f', args')) rest =
    if f = f' andalso length args = length args' then
      solve env (zip args args' @ rest)
    else raise ERR "unify" "different structure";
in
  val unifyl = solve;
end;

fun unify env tm tm' = unifyl env [(tm, tm')];

fun unify_and_apply tm tm' = term_subst (unify |<>| tm tm') tm;

local
  fun conv (Atom (r, args), Atom (r', args')) =
    SOME (Fn (r, args), Fn (r', args'))
    | conv (Not p, Not q) = conv (p, q)
    | conv (True, True) = NONE
    | conv (False, False) = NONE
    | conv _ = raise ERR "unify_literals" "incompatible";
in
  fun unifyl_literals env = unifyl env o List.mapPartial conv;
end;

fun unify_literals env lit lit' = unifyl_literals env [(lit, lit')];

end