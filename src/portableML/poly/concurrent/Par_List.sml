(*  Title:      Pure/Concurrent/par_list.ML
    Author:     Makarius

Parallel list combinators.

Notes:

  * These combinators only make sense if the operator (function or
    predicate) applied to the list of operands takes considerable
    time.  The overhead of scheduling is significantly higher than
    just traversing the list of operands sequentially.

  * The order of operator application is non-deterministic.  Watch out
    for operators that have side-effects or raise exceptions!
*)

structure Par_List :> Par_List =
struct

fun forked_results name f xs =
  if Future.relevant xs
  then Future.forked_results {name = name, deps = []} (map (fn x => fn () => f x) xs)
  else map (Exn.capture f) xs;

fun map_name name f xs = Par_Exn.release_first (forked_results name f xs);
fun map f = map_name "Par_List.map" f;
fun map_independent f =
  Par_Exn.release_all o map (Exn.interruptible_capture f)

fun get_some f xs =
  let
    exception FOUND of 'b;
    val results =
      forked_results "Par_List.get_some"
        (fn x => (case f x of NONE => () | SOME y => raise FOUND y)) xs;
  in
    case
      Portable.first_opt
        (fn _ => fn Exn.Exn (FOUND res) => SOME res | _ => NONE)
        results
    of
      NONE => (Par_Exn.release_first results; NONE)
    | some => some
  end

fun find_some P = get_some (fn x => if P x then SOME x else NONE);

fun exists P = isSome o find_some P;
fun forall P = not o exists (not o P);

end;
