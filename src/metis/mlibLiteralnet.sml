(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF LITERALS                             *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "Mosml", "mlibTerm"];
*)

(*
*)
structure mlibLiteralnet :> mlibLiteralnet =
struct

open mlibUseful mlibTerm;

infixr |-> ::> oo;

structure S = mlibStream; local open mlibStream in end;
structure T = mlibTermnet; local open mlibTermnet in end;

type 'a stream = 'a S.stream;
type subst = mlibSubst.subst;

val |<>| = mlibSubst.|<>|;

(* ------------------------------------------------------------------------- *)
(* Literal nets.                                                             *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool};

type 'a literalnet =
  ('a T.termnet * 'a T.termnet) * ((int * 'a list) * (int * 'a list));

fun empty p = ((T.empty p, T.empty p), ((0,[]),(0,[])));

fun insert (Atom a |-> b) ((p,n),tf)       = ((T.insert (a |-> b) p, n), tf)
  | insert (Not (Atom a) |-> b) ((p,n),tf) = ((p, T.insert (a |-> b) n), tf)
  | insert (True |-> b) (pn,((n,l),f))     = (pn, ((n + 1, b :: l), f))
  | insert (False |-> b) (pn,(t,(n,l)))    = (pn, (t, (n + 1, b :: l)))
  | insert (f |-> _) _ = raise Bug ("insert: not a lit: "^formula_to_string f);

local
  fun pos     ((pos, _  ), _               ) = T.size pos;
  fun neg     ((_,   neg), _               ) = T.size neg;
  fun truth   (_,          ((n, _), _     )) = n;
  fun falsity (_,          (_,      (n, _))) = n;
in
  fun size l         = truth l + falsity l + pos l + neg l;
  fun size_profile l = {t = truth l, f = falsity l, p = pos l, n = neg l};
end;

fun match ((pos,_),_) (Atom a) = T.match pos a
  | match ((_,neg),_) (Not (Atom a)) = T.match neg a
  | match (_,((_,t),_)) True = t
  | match (_,(_,(_,f))) False = f
  | match _ _ = raise Bug "match: not a literal";

fun matched ((pos,_),_) (Atom a) = T.matched pos a
  | matched ((_,neg),_) (Not (Atom a)) = T.matched neg a
  | matched (_,((_,t),_)) True = t
  | matched (_,(_,(_,f))) False = f
  | matched _ _ = raise Bug "matched: not a literal";

fun unify ((pos,_),_) (Atom a) = T.unify pos a
  | unify ((_,neg),_) (Not (Atom a)) = T.unify neg a
  | unify (_,((_,t),_)) True = t
  | unify (_,(_,(_,f))) False = f
  | unify _ _ = raise Bug "unify: not a literal";

fun filter pred =
  let
    fun filt (_,l) = let val l = List.filter pred l in (length l, l) end
  in
    fn ((pos,neg),(t,f)) =>
    ((T.filter pred pos, T.filter pred neg), (filt t, filt f))
  end;

fun from_maplets p l = foldl (uncurry insert) (empty p) l;

fun to_maplets ((pos,neg),((_,t),(_,f))) =
  map (fn x => True |-> x) t @
  map (fn x => False |-> x) f @
  map (fn t |-> x => Atom t |-> x) (T.to_maplets pos) @
  map (fn t |-> x => Not (Atom t) |-> x) (T.to_maplets neg);

fun pp_literalnet pp_a =
  pp_map to_maplets (pp_list (pp_maplet pp_formula pp_a));

end
