(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF TERMS                                *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "Mosml", "mlibTerm"];
*)

(*
*)
structure mlibTermNet :> mlibTermNet =
struct

open mlibUseful mlibTerm;

infixr |-> ::> oo;

val flatten = List.concat;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun fifo_order (m, _) (n, _) = m <= n;
in
  fun restore_fifo_order l = map snd (sort fifo_order l);
end;

fun partition_find f l =
  let
    fun pf _ [] = (NONE, l)
      | pf dealt (x :: xs) =
      if f x then (SOME x, List.revAppend (dealt, xs)) else pf (x :: dealt) xs
  in
    pf [] l
  end;

(* ------------------------------------------------------------------------- *)
(* Term discrimination trees are optimized for match queries.                *)
(* ------------------------------------------------------------------------- *)

datatype pattern = VAR | FN of string * int;

type 'a map = (pattern, 'a) tree;

datatype 'a term_map = MAP of int * (int * 'a) map list;

val empty = MAP (0, []);

fun size (MAP (i, _)) = i;

fun to_list (MAP (_, n)) =
  restore_fifo_order (flatten (map (tree_foldr (K flatten) wrap) n));

fun pp_term_map pp_a = pp_map to_list (pp_list pp_a);

local
  fun find_pat x (BRANCH (p, _)) = p = x
    | find_pat _ (LEAF _) = raise BUG "find_pat" "misplaced LEAF";

  fun add a [] l = LEAF a :: l
    | add a (tm :: rest) l =
    let
      val (pat, rest) =
        case tm of Var _ => (VAR, rest)
        | Fn (f, args) => (FN (f, length args), args @ rest)
      val (this, others) = partition_find (find_pat pat) l
      val next =
        case this of NONE => []
        | SOME (BRANCH (_, l)) => l
        | SOME (LEAF _) => raise BUG "add" "misplaced LEAF"
    in
      BRANCH (pat, add a rest next) :: others
    end;
in
  fun insert (tm |-> a) (MAP (i, n)) = MAP (i + 1, add (i, a) [tm] n)
  handle ERR_EXN _ => raise BUG "insert" "should never fail";
end;

fun from_maplets l = foldl (uncurry insert) empty l;

local
  fun mat VAR (_ :: rest) = SOME rest
    | mat (FN (f, n)) (Fn (g, args) :: rest) =
    if f = g andalso n = length args then SOME (args @ rest) else NONE
    | mat (FN _) (Var _ :: _) = NONE
    | mat _ [] = raise BUG "match" "ran out of subterms";

  fun final a [] = SOME a
    | final _ (_ :: _) = raise BUG "match" "too many subterms";
in
  fun match (MAP (_, n)) tm =
    restore_fifo_order (flatten (map (tree_partial_foldl mat final [tm]) n))
  handle ERR_EXN _ => raise BUG "match" "should never fail";
end;

local
  fun more VAR = 0 | more (FN (f, n)) = n;
  fun mat pat (0, Var _ :: rest) = SOME (more pat, rest)
    | mat VAR (0, Fn _ :: _) = NONE
    | mat (FN (f, n)) (0, Fn (g, args) :: rest) =
    if f = g andalso n = length args then SOME (0, args @ rest) else NONE
    | mat _ (0, []) = raise BUG "matched" "ran out of subterms"
    | mat pat (n, rest) = SOME (more pat + n - 1, rest);

  fun final a (0, []) = SOME a
    | final _ (0, _ :: _) = raise BUG "matched" "too many subterms"
    | final _ (n, _) = raise BUG "matched" "still skipping";
in
  fun matched (MAP (_, n)) tm =
    restore_fifo_order (flatten (map (tree_partial_foldl mat final (0,[tm])) n))
  handle ERR_EXN _ => raise BUG "matched" "should never fail";
end;

local
  fun more VAR = 0 | more (FN (f, n)) = n;
  fun mat pat (0, Var _ :: rest) = SOME (more pat, rest)
    | mat VAR (0, Fn _ :: rest) = SOME (0, rest)
    | mat (FN (f, n)) (0, Fn (g, args) :: rest) =
    if f = g andalso n = length args then SOME (0, args @ rest) else NONE
    | mat _ (0, []) = raise BUG "unify" "ran out of subterms"
    | mat pat (n, rest) = SOME (more pat + n - 1, rest);

  fun final a (0, []) = SOME a
    | final _ (0, _ :: _) = raise BUG "unify" "too many subterms"
    | final _ (n, _) = raise BUG "unify" "still skipping";
in
  fun unify (MAP (_, n)) tm =
    restore_fifo_order (flatten (map (tree_partial_foldl mat final (0,[tm])) n))
  handle ERR_EXN _ => raise BUG "unify" "should never fail";
end;

(* ------------------------------------------------------------------------- *)
(* We can overlay the above type with a simple list type.                    *)
(* ------------------------------------------------------------------------- *)
(*
type 'a simple = int * int * term list * 'a list;

type 'a term_map = ('a simple, 'a term_map) sum;

fun check (0, _, t, a) =
  INR (from_maplets (foldl (fn (x, xs) => op|-> x :: xs) [] (zip t a)))
  | check p = INL p;

val empty : 'a term_map = INR empty;

fun new n = check (n, 0, [], []);

val insert = fn m =>
  (fn INL (n, s, ts, xs) =>
      (case m of t |-> x => check (n - 1, s + 1, t :: ts, x :: xs))
    | INR d => INR (insert m d));

val match = fn INL (_, _, _, xs) => K (rev xs) | INR d => match d;

val matched = fn INL (_, _, _, xs) => K (rev xs) | INR d => matched d;

val unify = fn INL (_, _, _, xs) => K (rev xs) | INR d => unify d;

val size = fn INL (_, s, _, _) => s | INR d => size d;

val from_maplets = INR o from_maplets;

val to_list = fn INL (_, _, _, xs) => rev xs | INR d => to_list d;

val pp_term_map =
  fn pp_a => fn pp =>
  (fn INL (_, _, _, xs) => pp_list pp_a pp xs | INR d => pp_term_map pp_a pp d);
*)

end
