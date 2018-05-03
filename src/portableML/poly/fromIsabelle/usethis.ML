infix 1 |>> |> ||->
infix 2 ?
fun (x,y) |>> f = (f x, y)
fun (x,y) ||-> f = f x y
val is_some = Option.isSome;
val the = Option.valOf;
fun the_list NONE = [] | the_list (SOME x) = [x]
fun the_default d NONE = d | the_default d (SOME x) = x

fun fold _ [] y = y
  | fold f (x :: xs) y = fold f xs (f x y);
fun fold_rev _ [] y = y
  | fold_rev f (x :: xs) y = f x (fold_rev f xs y);
fun fold_map _ [] y = ([], y)
  | fold_map f (x :: xs) y =
      let
        val (x', y') = f x y;
        val (xs', y'') = fold_map f xs y';
      in (x' :: xs', y'') end;


fun these (SOME x) = x
  | these NONE = [];
fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;
fun cons h t = h::t
fun pair x y = (x,y)
fun snd(x,y) = y


fun buse s = (use (s ^ ".sig"); use (s ^ ".sml"));

val _ = use "../PrettyImpl.sml";
val _ = buse "../../UTF8";
val _ = buse "../../HOLPP";
val _ = buse "../../OldPP";
val _ = buse "../Arbnumcore";
val _ = buse "../Arbintcore";
val _ = buse "../../Arbnum";
val _ = buse "../../Arbint";
val _ = buse "../MD5";
val _ = buse "../Susp";

exception SysErr = OS.SysErr
exception Interrupt = Thread.Thread.Interrupt;
structure FileSys = OS.FileSys;

val _ = use "../MLSYSPortable.sml";
val _ = buse "../../Portable";

structure Library =
struct
local open Portable in
  fun member eq list x =
    let
      fun memb [] = false
        | memb (y :: ys) = eq (x, y) orelse memb ys;
    in memb list end;
  fun remove eq x xs = if member eq xs x then
                         List.filter (fn y => not (eq (x, y))) xs
                       else xs;
  fun update eq x xs = cons x (remove eq x xs);
  fun insert eq x xs = if member eq xs x then xs else x :: xs;
  fun merge eq (xs, ys) =
    if null xs then ys else fold_rev (insert eq) ys xs;
  val map_filter = List.mapPartial;
  fun (b ? f) = if b then f else fn x => x
  fun enclose lpar rpar str = lpar ^ str ^ rpar;
  fun filter_out P = List.filter (not o P)
  fun fold2 _ [] [] z = z
    | fold2 f (x :: xs) (y :: ys) z = fold2 f xs ys (f x y z)
    | fold2 _ _ _ _ = raise ListPair.UnequalLengths;
  fun fold_product f _ [] z = z
    | fold_product f [] _ z = z
    | fold_product f (x :: xs) ys z =
        z |> fold (f x) ys |> fold_product f xs ys

  fun single x = [x]
  fun the_single [x] = x
    | the_single _ = raise List.Empty;
  fun singleton f x = the_single (f [x])

end (* local *)
end;


val _ = use "alist.ML";
val _ = use "exn.ML";
val _ = use "table.ML";
val _ = use "graph.ML";

exception Thread = Thread.Thread
structure Mutex = Thread.Mutex;
structure ConditionVar = Thread.ConditionVar;

val _ = use "thread_attributes.ML";
val _ = use "thread_data.ML";

structure Thread = Thread.Thread;

val _ = use "unsynchronized.ML";
val _ = use "multithreading.ML";
val _ = use "synchronized.ML";
val _ = use "single_assignment.ML";
val _ = use "counter.ML";

val _ = use "par_exn.ML";

val _ = use "task_queue.ML";
val _ = use "standard_thread.ML";
val _ = use "future.ML";
