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

fun insert (Atom A|->a) ((pos,neg), tf) = ((T.insert (Fn A |-> a) pos, neg), tf)
  | insert (Not(Atom A)|->a) ((pos,neg),tf) = ((pos,T.insert(Fn A|->a) neg), tf)
  | insert (True |-> a) (posneg, ((n, l), f)) = (posneg, ((n + 1, a :: l), f))
  | insert (False |-> a) (posneg, (t, (n, l))) = (posneg, (t, (n + 1, a :: l)))
  | insert (fm|->_) _ = raise BUG "insert" ("not a lit: "^formula_to_string fm);

fun from_maplets l = foldl (uncurry insert) empty l;

fun to_list ((pos, neg), ((_, t), (_, f))) =
  rev t @ rev f @ T.to_list pos @ T.to_list neg;

fun pp_literal_map pp_a = pp_map to_list (pp_list pp_a);

local
  fun pos ((pos, _), _) = T.size pos;
  fun neg ((_, neg), _) = T.size neg;
  fun truth (_, ((n, _), _)) = n;
  fun falsity (_, (_, (n, _))) = n;
in
  fun size l = truth l + falsity l + pos l + neg l;
  fun size_profile l = {t = truth l, f = falsity l, p = pos l, n = neg l};
end;

fun match ((pos, _), _) (Atom A) = T.match pos (Fn A)
  | match ((_, neg), _) (Not (Atom A)) = T.match neg (Fn A)
  | match (_, ((_, t), _)) True = rev t
  | match (_, (_, (_, f))) False = rev f
  | match _ _ = raise BUG "match" "not a literal";

fun matched ((pos, _), _) (Atom A) = T.matched pos (Fn A)
  | matched ((_, neg), _) (Not (Atom A)) = T.matched neg (Fn A)
  | matched (_, ((_, t), _)) True = rev t
  | matched (_, (_, (_, f))) False = rev f
  | matched _ _ = raise BUG "matched" "not a literal";

fun unify ((pos, _), _) (Atom A) = T.unify pos (Fn A)
  | unify ((_, neg), _) (Not (Atom A)) = T.unify neg (Fn A)
  | unify (_, ((_, t), _)) True = rev t
  | unify (_, (_, (_, f))) False = rev f
  | unify _ _ = raise BUG "unify" "not a literal";

end