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

val isSome  = Option.isSome;
val drop    = List.drop;
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
(* Term nets are optimized for match, matched and unify queries.             *)
(* ------------------------------------------------------------------------- *)

type 'a subterm_info =
  {skip : 'a, var : 'a option, fns : ((string * int) * 'a) list};

datatype 'a net = END of 'a list | SUBTERM of 'a net subterm_info;

datatype 'a term_map = NET of int * (int * 'a) net;

val empty_net = SUBTERM {skip = END [], var = NONE, fns = []};

val empty = NET (0, empty_net);

fun size (NET (i, _)) = i;

fun to_list (NET (_, SUBTERM {skip = END l, ...})) = restore_fifo_order l
  | to_list (NET _) = raise BUG "net_to_maplets" "corrupt";

fun pp_term_map pp_a = pp_map to_list (pp_list pp_a);

local
  fun add a [] net =
    let
      val other_ends =
        case net of END l => l
        | SUBTERM {skip = END [], var = NONE, fns = []} => []
        | _ => raise BUG "::+" "corrupt at end"
    in
      (END (a :: other_ends), [])
    end
    | add a (Var _ :: rest) (SUBTERM {skip, var, fns}) =
    let
      val next = case var of SOME n => n | NONE => empty_net
      val (next, share) = add a rest next
    in
      if null fns then
        (SUBTERM {skip = next, var = SOME next, fns = []}, next :: share)
      else
        (SUBTERM {skip = fst (add a rest skip), var = SOME next, fns = fns}, [])
    end
    | add a (Fn (f, args) :: rest) (SUBTERM {skip, var, fns}) =
    let
      val arity = length args
      val sym = (f, arity)
      val (this_fn, other_fns) = partition_find (equal sym o fst) fns
      val next = case this_fn of SOME (_, n) => n | NONE => empty_net
      val (next, share) = add a (args @ rest) next
      val fns = (sym, next) :: other_fns
      val share =
        if length share < arity then [] else drop (next :: share, arity)
    in
      if non null share andalso null other_fns andalso non isSome var then
        (SUBTERM {skip = hd share, var = var, fns = fns}, share)
      else
        (SUBTERM {skip = fst (add a rest skip), var = var, fns = fns}, [])
    end
    | add a (_ :: _) (END _) = raise BUG "::+" "corrupt along path";
in
  fun insert (tm |-> a) (NET (i, d)) = NET (i + 1, fst (add (i, a) [tm] d))
  handle ERR_EXN _ => raise BUG "insert" "should never fail";
end;

fun from_maplets l = foldl (uncurry insert) empty l;

local
  fun mat res [] = res
    | mat res (([], END l) :: others) = mat (l @ res) others
    | mat res ((tm :: rest, SUBTERM {skip = _, var, fns}) :: others) =
    let
      val others =
        case var of NONE => others | SOME net => (rest, net) :: others
      val others =
        case tm of Var _ => others
        | Fn (f, args) =>
          (case List.find (equal (f, length args) o fst) fns of NONE => others
           | SOME (_, net) => (args @ rest, net) :: others)
    in
      mat res others
    end
    | mat _ _ = raise BUG "match" "corrupt";
in
  fun match (NET (_, d)) tm = restore_fifo_order (mat [] [([tm], d)])
  handle ERR_EXN _ => raise BUG "match" "should never fail";
end;

local
  fun uni res [] = res
    | uni res (([], END l) :: others) = uni (l @ res) others
    | uni res ((Var _ :: rest, SUBTERM {skip, var = _, fns = _}) :: others) =
    uni res ((rest, skip) :: others)
    | uni res ((Fn (f, args) :: rest, SUBTERM {skip = _, var, fns}) :: others) =
    let
      val others =
        case var of NONE => others | SOME net => (rest, net) :: others
      val others =
        case List.find (equal (f, length args) o fst) fns of NONE => others
        | SOME (_, net) => (args @ rest, net) :: others
    in
      uni res others
    end
    | uni _ _ = raise BUG "unify" "corrupt";
in
  fun unify (NET (_, d)) tm = restore_fifo_order (uni [] [([tm], d)])
  handle ERR_EXN _ => raise BUG "unify" "should never fail";
end;

local
  fun mtd res [] = res
    | mtd res (([], END l) :: others) = mtd (l @ res) others
    | mtd res ((Var _ :: rest, SUBTERM {skip, var = _, fns = _}) :: others) =
    mtd res ((rest, skip) :: others)
    | mtd res
    ((Fn (f, args) :: rest, SUBTERM {skip = _, var = _, fns}) :: others) =
    let
      val others =
        case List.find (equal (f, length args) o fst) fns of NONE => others
        | SOME (_, net) => (args @ rest, net) :: others
    in
      mtd res others
    end
    | mtd _ _ = raise BUG "matched" "corrupt";
in
  fun matched (NET (_, d)) tm = restore_fifo_order (mtd [] [([tm], d)])
  handle ERR_EXN _ => raise BUG "matched" "should never fail";
end;

end
