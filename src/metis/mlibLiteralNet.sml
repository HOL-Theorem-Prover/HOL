(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF LITERALS                             *)
(* Created by Joe Hurd, June 2002                                            *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "Mosml", "mlibTerm"];
*)

(*
*)
structure mlibLiteralNet :> mlibLiteralNet =
struct

open mlibUseful mlibTerm;

infixr |-> ::> oo;

structure T = mlibTermNet; local open mlibTermNet in end;

(* ------------------------------------------------------------------------- *)
(* Literal nets.                                                             *)
(* ------------------------------------------------------------------------- *)

type 'a literal_map =
  ('a T.term_map * 'a T.term_map) * ((int * 'a list) * (int * 'a list));

val empty = ((T.empty, T.empty), ((0, []), (0, [])));

fun insert (Atom a |-> b) ((p, n), tf)       = ((T.insert (a |-> b) p, n), tf)
  | insert (Not (Atom a) |-> b) ((p, n), tf) = ((p, T.insert (a |-> b) n), tf)
  | insert (True |-> b) (pn, ((n, l), f))    = (pn, ((n + 1, b :: l), f))
  | insert (False |-> b) (pn, (t, (n, l)))   = (pn, (t, (n + 1, b :: l)))
  | insert (f |-> _) _ = raise BUG "insert" ("not a lit: "^formula_to_string f);

fun from_maplets l = foldl (uncurry insert) empty l;

fun to_list ((pos, neg), ((_, t), (_, f))) =
  rev t @ rev f @ T.to_list pos @ T.to_list neg;

fun pp_literal_map pp_a = pp_map to_list (pp_list pp_a);

local
  fun pos     ((pos, _  ), _               ) = T.size pos;
  fun neg     ((_,   neg), _               ) = T.size neg;
  fun truth   (_,          ((n, _), _     )) = n;
  fun falsity (_,          (_,      (n, _))) = n;
in
  fun size l         = truth l + falsity l + pos l + neg l;
  fun size_profile l = {t = truth l, f = falsity l, p = pos l, n = neg l};
end;

fun match ((pos, _), _) (Atom a) = T.match pos a
  | match ((_, neg), _) (Not (Atom a)) = T.match neg a
  | match (_, ((_, t), _)) True = rev t
  | match (_, (_, (_, f))) False = rev f
  | match _ _ = raise BUG "match" "not a literal";

fun matched ((pos, _), _) (Atom a) = T.matched pos a
  | matched ((_, neg), _) (Not (Atom a)) = T.matched neg a
  | matched (_, ((_, t), _)) True = rev t
  | matched (_, (_, (_, f))) False = rev f
  | matched _ _ = raise BUG "matched" "not a literal";

fun unify ((pos, _), _) (Atom a) = T.unify pos a
  | unify ((_, neg), _) (Not (Atom a)) = T.unify neg a
  | unify (_, ((_, t), _)) True = rev t
  | unify (_, (_, (_, f))) False = rev f
  | unify _ _ = raise BUG "unify" "not a literal";

end
