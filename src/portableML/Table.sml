(*  Title:      Pure/General/table.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Generic tables.  Efficient purely functional implementation using
balanced 2-3 trees.
*)

signature KEY =
sig
  type key
  val ord: key * key -> order
  val pp : key HOLPP.pprinter
end;

signature TABLE =
sig
  structure Key: KEY
  type key
  type 'a table
  exception DUP of key
  exception SAME
  exception UNDEF of key
  val size: 'a table -> int
  val empty: 'a table
  val build: ('a table -> 'a table) -> 'a table
  val is_empty: 'a table -> bool
  val map: (key -> 'a -> 'b) -> 'a table -> 'b table
  val fold: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val fold_rev: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val dest: 'a table -> (key * 'a) list
  val keys: 'a table -> key list
  val min: 'a table -> (key * 'a) option
  val max: 'a table -> (key * 'a) option
  val exists: (key * 'a -> bool) -> 'a table -> bool
  val forall: (key * 'a -> bool) -> 'a table -> bool
  val get_first: (key * 'a -> 'b option) -> 'a table -> 'b option
  val lookup_key: 'a table -> key -> (key * 'a) option
  val lookup: 'a table -> key -> 'a option
  val defined: 'a table -> key -> bool
  val update: key * 'a -> 'a table -> 'a table
  val update_new: key * 'a -> 'a table -> 'a table                  (* exn DUP*)
  val default: key * 'a -> 'a table -> 'a table
  val map_entry: key -> ('a -> 'a) (*exception SAME*) -> 'a table -> 'a table
  val map_default: key * 'a -> ('a -> 'a) -> 'a table -> 'a table
  val make: (key * 'a) list -> 'a table                             (* exn DUP*)
  val join: (key -> 'a * 'a -> 'a) (*exception SAME*) ->
    'a table * 'a table -> 'a table                                 (* exn DUP*)
  val merge: ('a -> 'a -> bool) -> 'a table * 'a table -> 'a table  (* exn DUP*)
  val joins: (key -> 'a * 'a -> 'a) (*exception SAME*) ->
    'a table list -> 'a table                                       (* exn DUP*)
  val merges: ('a -> 'a -> bool) -> 'a table list -> 'a table       (* exn DUP*)
  val delete: key -> 'a table -> 'a table                         (* exn UNDEF*)
  val delete_safe: key -> 'a table -> 'a table
  val member: ('b * 'a -> bool) -> 'a table -> key * 'b -> bool
  val insert: ('a -> 'a -> bool) -> key * 'a -> 'a table -> 'a table(* exn DUP*)
  val remove: ('b -> 'a -> bool) -> key * 'b -> 'a table -> 'a table
  val lookup_list: 'a list table -> key -> 'a list
  val cons_list: key * 'a -> 'a list table -> 'a list table
  val insert_list: ('a -> 'a -> bool) -> key * 'a -> 'a list table ->
                   'a list table
  val update_list: ('a -> 'a -> bool) -> key * 'a -> 'a list table ->
                   'a list table
  val remove_list: ('b -> 'a -> bool) -> key * 'b -> 'a list table ->
                   'a list table
  val make_list: (key * 'a) list -> 'a list table
  val dest_list: 'a list table -> (key * 'a) list
  val merge_list: ('a -> 'a -> bool) -> 'a list table * 'a list table ->
                  'a list table
  type set = unit table
  val insert_set: key -> set -> set
  val remove_set: key -> set -> set
  val make_set: key list -> set

  val pp : 'a HOLPP.pprinter -> 'a table HOLPP.pprinter
end;

functor Table(Key: KEY): TABLE =
struct

(* keys *)
open Portable

structure Key = Key;
type key = Key.key;

exception DUP of key;
fun is_equal EQUAL = true
  | is_equal _ = false
val the = valOf

(* datatype *)

datatype 'a table =
  Empty |
  Leaf1 of key * 'a |
  Leaf2 of key * 'a * key * 'a |
  Leaf3 of key * 'a * key * 'a * key * 'a |
  Branch2 of 'a table * (key * 'a) * 'a table |
  Branch3 of 'a table * (key * 'a) * 'a table * (key * 'a) * 'a table |
  Size of int * 'a table;

fun make2 (Empty, e, Empty) = Leaf1 e
  | make2 (Branch2 (Empty, e1, Empty), e2, right) = make2 (Leaf1 e1, e2, right)
  | make2 (left, e1, Branch2 (Empty, e2, Empty)) = make2 (left, e1, Leaf1 e2)
  | make2 (Branch3 (Empty, (k1, x1), Empty, (k2, x2), Empty), e3, right) =
      make2 (Leaf2 (k1, x1, k2, x2), e3, right)
  | make2 (left, e1, Branch3 (Empty, (k2, x2), Empty, (k3, x3), Empty)) =
      make2 (left, e1, Leaf2 (k2, x2, k3, x3))
  | make2 (Leaf1 (k1, x1), (k2, x2), Empty) = Leaf2 (k1, x1, k2, x2)
  | make2 (Empty, (k1, x1), Leaf1 (k2, x2)) = Leaf2 (k1, x1, k2, x2)
  | make2 (Leaf1 (k1, x1), (k2, x2), Leaf1 (k3, x3)) = Leaf3 (k1, x1, k2, x2, k3, x3)
  | make2 (Leaf2 (k1, x1, k2, x2), (k3, x3), Empty) = Leaf3 (k1, x1, k2, x2, k3, x3)
  | make2 (Empty, (k1, x1), Leaf2 (k2, x2, k3, x3)) = Leaf3 (k1, x1, k2, x2, k3, x3)
  | make2 arg = Branch2 arg;

fun make3 (Empty, (k1, x1), Empty, (k2, x2), Empty) = Leaf2 (k1, x1, k2, x2)
  | make3 (Branch2 (Empty, e1, Empty), e2, mid, e3, right) = make3 (Leaf1 e1, e2, mid, e3, right)
  | make3 (left, e1, Branch2 (Empty, e2, Empty), e3, right) = make3 (left, e1, Leaf1 e2, e3, right)
  | make3 (left, e1, mid, e2, Branch2 (Empty, e3, Empty)) = make3 (left, e1, mid, e2, Leaf1 e3)
  | make3 (Leaf1 (k1, x1), (k2, x2), Empty, (k3, x3), Empty) = Leaf3 (k1, x1, k2, x2, k3, x3)
  | make3 (Empty, (k1, x1), Leaf1 (k2, x2), (k3, x3), Empty) = Leaf3 (k1, x1, k2, x2, k3, x3)
  | make3 (Empty, (k1, x1), Empty, (k2, x2), Leaf1 (k3, x3)) = Leaf3 (k1, x1, k2, x2, k3, x3)
  | make3 arg = Branch3 arg;

fun unmake (Leaf1 e) = Branch2 (Empty, e, Empty)
  | unmake (Leaf2 (k1, x1, k2, x2)) = Branch3 (Empty, (k1, x1), Empty, (k2, x2), Empty)
  | unmake (Leaf3 (k1, x1, k2, x2, k3, x3)) =
      Branch2 (Branch2 (Empty, (k1, x1), Empty), (k2, x2), Branch2 (Empty, (k3, x3), Empty))
  | unmake (Size (_, arg)) = arg
  | unmake arg = arg;


(* size *)

(*literal copy from set.ML*)
local
  fun count Empty n = n
    | count (Leaf1 _) n = n + 1
    | count (Leaf2 _) n = n + 2
    | count (Leaf3 _) n = n + 3
    | count (Branch2 (left, _, right)) n = count right (count left (n + 1))
    | count (Branch3 (left, _, mid, _, right)) n = count right (count mid (count left (n + 2)))
    | count (Size (m, _)) n = m + n;

  fun box (Branch2 _) = 1
    | box (Branch3 _) = 1
    | box _ = 0;

  fun bound arg b =
    if b > 0 then
      (case arg of
        Branch2 (left, _, right) =>
          bound right (bound left (b - box left - box right))
      | Branch3 (left, _, mid, _, right) =>
          bound right (bound mid (bound left (b - box left - box mid - box right)))
      | _ => b)
    else b;
in
  fun size arg = count arg 0;
  fun make_size m arg = if bound arg 3 <= 0 then Size (m, arg) else arg;
end;


(* empty *)

val empty = Empty;

fun build (f: 'a table -> 'a table) = f empty;

(*literal copy from set.ML*)
fun is_empty Empty = true
  | is_empty (Size (_, arg)) = is_empty arg
  | is_empty _ = false;


(* map and fold combinators *)

fun map_table f =
  let
    fun map Empty = Empty
      | map (Leaf1 (k, x)) = Leaf1 (k, f k x)
      | map (Leaf2 (k1, x1, k2, x2)) = Leaf2 (k1, f k1 x1, k2, f k2 x2)
      | map (Leaf3 (k1, x1, k2, x2, k3, x3)) = Leaf3 (k1, f k1 x1, k2, f k2 x2, k3, f k3 x3)
      | map (Branch2 (left, (k, x), right)) =
          Branch2 (map left, (k, f k x), map right)
      | map (Branch3 (left, (k1, x1), mid, (k2, x2), right)) =
          Branch3 (map left, (k1, f k1 x1), map mid, (k2, f k2 x2), map right)
      | map (Size (m, arg)) = Size (m, map arg);
  in map end;

fun fold_table f =
  let
    fun fold Empty a = a
      | fold (Leaf1 e) a = f e a
      | fold (Leaf2 (k1, x1, k2, x2)) a = f (k2, x2) (f (k1, x1) a)
      | fold (Leaf3 (k1, x1, k2, x2, k3, x3)) a = f (k3, x3) (f (k2, x2) (f (k1, x1) a))
      | fold (Branch2 (left, e, right)) a =
          fold right (f e (fold left a))
      | fold (Branch3 (left, e1, mid, e2, right)) a =
          fold right (f e2 (fold mid (f e1 (fold left a))))
      | fold (Size (_, arg)) a = fold arg a;
  in fold end;

fun fold_rev_table f =
  let
    fun fold_rev Empty a = a
      | fold_rev (Leaf1 e) a = f e a
      | fold_rev (Leaf2 (k1, x1, k2, x2)) a = f (k1, x1) (f (k2, x2) a)
      | fold_rev (Leaf3 (k1, x1, k2, x2, k3, x3)) a = f (k1, x1) (f (k2, x2) (f (k3, x3) a))
      | fold_rev (Branch2 (left, e, right)) a =
          fold_rev left (f e (fold_rev right a))
      | fold_rev (Branch3 (left, e1, mid, e2, right)) a =
          fold_rev left (f e1 (fold_rev mid (f e2 (fold_rev right a))))
      | fold_rev (Size (_, arg)) a = fold_rev arg a;
  in fold_rev end;

fun lbuild (f : 'a list -> 'a list) = f []
fun dest tab = lbuild (fold_rev_table cons tab);
fun keys tab = lbuild (fold_rev_table (cons o #1) tab);


(* min/max entries *)

fun min Empty = NONE
  | min (Leaf1 e) = SOME e
  | min (Leaf2 (k, x, _, _)) = SOME (k, x)
  | min (Leaf3 (k, x, _, _, _, _)) = SOME (k, x)
  | min (Branch2 (Empty, e, _)) = SOME e
  | min (Branch3 (Empty, e, _, _, _)) = SOME e
  | min (Branch2 (left, _, _)) = min left
  | min (Branch3 (left, _, _, _, _)) = min left
  | min (Size (_, arg)) = min arg;

fun max Empty = NONE
  | max (Leaf1 e) = SOME e
  | max (Leaf2 (_, _, k, x)) = SOME (k, x)
  | max (Leaf3 (_, _, _, _, k, x)) = SOME (k, x)
  | max (Branch2 (_, e, Empty)) = SOME e
  | max (Branch3 (_, _, _, e, Empty)) = SOME e
  | max (Branch2 (_, _, right)) = max right
  | max (Branch3 (_, _, _, _, right)) = max right
  | max (Size (_, arg)) = max arg;


(* exists and forall *)

fun exists pred =
  let
    fun ex Empty = false
      | ex (Leaf1 e) = pred e
      | ex (Leaf2 (k1, x1, k2, x2)) = pred (k1, x1) orelse pred (k2, x2)
      | ex (Leaf3 (k1, x1, k2, x2, k3, x3)) =
          pred (k1, x1) orelse pred (k2, x2) orelse pred (k3, x3)
      | ex (Branch2 (left, e, right)) =
          ex left orelse pred e orelse ex right
      | ex (Branch3 (left, e1, mid, e2, right)) =
          ex left orelse pred e1 orelse ex mid orelse pred e2 orelse ex right
      | ex (Size (_, arg)) = ex arg;
  in ex end;

fun forall pred = not o exists (not o pred);


(* get_first *)

fun get_first f =
  let
    fun get Empty = NONE
      | get (Leaf1 e) = f e
      | get (Leaf2 (k1, x1, k2, x2)) =
          (case f (k1, x1) of
            NONE => f (k2, x2)
          | some => some)
      | get (Leaf3 (k1, x1, k2, x2, k3, x3)) =
          (case f (k1, x1) of
            NONE =>
              (case f (k2, x2) of
                NONE => f (k3, x3)
              | some => some)
          | some => some)
      | get (Branch2 (left, e, right)) =
          (case get left of
            NONE =>
              (case f e of
                NONE => get right
              | some => some)
          | some => some)
      | get (Branch3 (left, e1, mid, e2, right)) =
          (case get left of
            NONE =>
              (case f e1 of
                NONE =>
                  (case get mid of
                    NONE =>
                      (case f e2 of
                        NONE => get right
                      | some => some)
                  | some => some)
              | some => some)
          | some => some)
      | get (Size (_, arg)) = get arg;
  in get end;


(* lookup *)

fun lookup tab key =
  let
    fun key_ord k = Key.ord (key, k);
    val key_eq = is_equal o key_ord;

    fun look Empty = NONE
      | look (Leaf1 (k, x)) =
          if key_ord k = EQUAL then SOME x else NONE
      | look (Leaf2 (k1, x1, k2, x2)) =
          (case key_ord k1 of
            LESS => NONE
          | EQUAL => SOME x1
          | GREATER => if key_eq k2 then SOME x2 else NONE)
      | look (Leaf3 (k1, x1, k2, x2, k3, x3)) =
          (case key_ord k2 of
            LESS => if key_eq k1 then SOME x1 else NONE
          | EQUAL => SOME x2
          | GREATER => if key_eq k3 then SOME x3 else NONE)
      | look (Branch2 (left, (k, x), right)) =
          (case key_ord k of
            LESS => look left
          | EQUAL => SOME x
          | GREATER => look right)
      | look (Branch3 (left, (k1, x1), mid, (k2, x2), right)) =
          (case key_ord k1 of
            LESS => look left
          | EQUAL => SOME x1
          | GREATER =>
              (case key_ord k2 of
                LESS => look mid
              | EQUAL => SOME x2
              | GREATER => look right))
      | look (Size (_, arg)) = look arg;
  in look tab end;

fun lookup_key tab key =
  let
    fun key_ord k = Key.ord (key, k);
    val key_eq = is_equal o key_ord;

    fun look Empty = NONE
      | look (Leaf1 (k, x)) =
          if key_eq k then SOME (k, x) else NONE
      | look (Leaf2 (k1, x1, k2, x2)) =
          (case key_ord k1 of
            LESS => NONE
          | EQUAL => SOME (k1, x1)
          | GREATER => if key_eq k2 then SOME (k2, x2) else NONE)
      | look (Leaf3 (k1, x1, k2, x2, k3, x3)) =
          (case key_ord k2 of
            LESS => if key_eq k1 then SOME (k1, x1) else NONE
          | EQUAL => SOME (k2, x2)
          | GREATER => if key_eq k3 then SOME (k3, x3) else NONE)
      | look (Branch2 (left, (k, x), right)) =
          (case key_ord k of
            LESS => look left
          | EQUAL => SOME (k, x)
          | GREATER => look right)
      | look (Branch3 (left, (k1, x1), mid, (k2, x2), right)) =
          (case key_ord k1 of
            LESS => look left
          | EQUAL => SOME (k1, x1)
          | GREATER =>
              (case key_ord k2 of
                LESS => look mid
              | EQUAL => SOME (k2, x2)
              | GREATER => look right))
      | look (Size (_, arg)) = look arg;
  in look tab end;

fun defined tab key =
  let
    fun key_ord k = Key.ord (key, k);
    val key_eq = is_equal o key_ord;

    fun def Empty = false
      | def (Leaf1 (k, _)) = key_eq k
      | def (Leaf2 (k1, _, k2, _)) =
          (case key_ord k1 of
            LESS => false
          | EQUAL => true
          | GREATER => key_eq k2)
      | def (Leaf3 (k1, _, k2, _, k3, _)) =
          (case key_ord k2 of
            LESS => key_eq k1
          | EQUAL => true
          | GREATER => key_eq k3)
      | def (Branch2 (left, (k, _), right)) =
          (case key_ord k of
            LESS => def left
          | EQUAL => true
          | GREATER => def right)
      | def (Branch3 (left, (k1, _), mid, (k2, _), right)) =
          (case key_ord k1 of
            LESS => def left
          | EQUAL => true
          | GREATER =>
              (case key_ord k2 of
                LESS => def mid
              | EQUAL => true
              | GREATER => def right))
      | def (Size (_, arg)) = def arg;
  in def tab end;


(* modify *)

datatype 'a growth =
  Stay of 'a table |
  Sprout of 'a table * (key * 'a) * 'a table;

exception SAME;

fun modify key f tab =
  let
    fun key_ord k = Key.ord (key, k);

    val inc = Unsynchronized.ref 0;
    fun insert () = f NONE before ignore (Unsynchronized.inc inc);
    fun update x = f (SOME x);

    fun modfy Empty = Sprout (Empty, (key, insert ()), Empty)
      | modfy (t as Leaf1 _) = modfy (unmake t)
      | modfy (t as Leaf2 _) = modfy (unmake t)
      | modfy (t as Leaf3 _) = modfy (unmake t)
      | modfy (Branch2 (left, p as (k, x), right)) =
          (case key_ord k of
            LESS =>
              (case modfy left of
                Stay left' => Stay (make2 (left', p, right))
              | Sprout (left1, q, left2) => Stay (make3 (left1, q, left2, p, right)))
          | EQUAL => Stay (make2 (left, (k, update x), right))
          | GREATER =>
              (case modfy right of
                Stay right' => Stay (make2 (left, p, right'))
              | Sprout (right1, q, right2) =>
                  Stay (make3 (left, p, right1, q, right2))))
      | modfy (Branch3 (left, p1 as (k1, x1), mid, p2 as (k2, x2), right)) =
          (case key_ord k1 of
            LESS =>
              (case modfy left of
                Stay left' => Stay (make3 (left', p1, mid, p2, right))
              | Sprout (left1, q, left2) =>
                  Sprout (make2 (left1, q, left2), p1, make2 (mid, p2, right)))
          | EQUAL => Stay (make3 (left, (k1, update x1), mid, p2, right))
          | GREATER =>
              (case key_ord k2 of
                LESS =>
                  (case modfy mid of
                    Stay mid' => Stay (make3 (left, p1, mid', p2, right))
                  | Sprout (mid1, q, mid2) =>
                      Sprout (make2 (left, p1, mid1), q, make2 (mid2, p2, right)))
              | EQUAL => Stay (make3 (left, p1, mid, (k2, update x2), right))
              | GREATER =>
                  (case modfy right of
                    Stay right' => Stay (make3 (left, p1, mid, p2, right'))
                  | Sprout (right1, q, right2) =>
                      Sprout (make2 (left, p1, mid), p2, make2 (right1, q, right2)))))
      | modfy (Size (_, arg)) = modfy arg;

    val tab' =
      (case tab of
        Empty => Leaf1 (key, insert ())
      | Leaf1 (k, x) =>
          (case key_ord k of
            LESS => Leaf2 (key, insert (), k, x)
          | EQUAL => Leaf1 (k, update x)
          | GREATER => Leaf2 (k, x, key, insert ()))
      | Leaf2 (k1, x1, k2, x2) =>
          (case key_ord k1 of
            LESS => Leaf3 (key, insert (), k1, x1, k2, x2)
          | EQUAL => Leaf2 (k1, update x1, k2, x2)
          | GREATER =>
              (case key_ord k2 of
                LESS => Leaf3 (k1, x1, key, insert (), k2, x2)
              | EQUAL => Leaf2 (k1, x1, k2, update x2)
              | GREATER => Leaf3 (k1, x1, k2, x2, key, insert ())))
      | _ =>
          (case modfy tab of
            Stay tab' => tab'
          | Sprout br => make2 br));
  in
    make_size (size tab + !inc) tab'
  end handle SAME => tab;

fun update (key, x) tab = modify key (fn _ => x) tab;
fun update_new (key, x) tab = modify key (fn NONE => x | SOME _ => raise DUP key) tab;
fun default (key, x) tab = modify key (fn NONE => x | SOME _ => raise SAME) tab;
fun map_entry key f = modify key (fn NONE => raise SAME | SOME x => f x);
fun map_default (key, x) f = modify key (fn NONE => f x | SOME y => f y);


(* delete *)

exception UNDEF of key;

local

fun compare NONE _ = LESS
  | compare (SOME k1) (k2, _) = Key.ord (k1, k2);

fun if_equal ord x y = if is_equal ord then x else y;

fun del (SOME k) Empty = raise UNDEF k
  | del NONE Empty = raise Match
  | del NONE (Leaf1 p) = (p, (true, Empty))
  | del NONE (Leaf2 (k1, x1, k2, x2)) = ((k1, x1), (false, Leaf1 (k2, x2)))
  | del k (Leaf1 p) =
      (case compare k p of
        EQUAL => (p, (true, Empty))
      | _ => raise UNDEF (the k))
  | del k (Leaf2 (k1, x1, k2, x2)) =
      (case compare k (k1, x1) of
        EQUAL => ((k1, x1), (false, Leaf1 (k2, x2)))
      | _ =>
        (case compare k (k2, x2) of
          EQUAL => ((k2, x2), (false, Leaf1 (k1, x1)))
        | _ => raise UNDEF (the k)))
  | del k (Leaf3 (k1, x1, k2, x2, k3, x3)) = del k (Branch2 (Leaf1 (k1, x1), (k2, x2), Leaf1 (k3, x3)))
  | del k (Branch2 (l, p, r)) =
      (case compare k p of
        LESS =>
          (case del k l of
            (p', (false, l')) => (p', (false, make2 (l', p, r)))
          | (p', (true, l')) => (p', case unmake r of
              Branch2 (rl, rp, rr) =>
                (true, make3 (l', p, rl, rp, rr))
            | Branch3 (rl, rp, rm, rq, rr) => (false, make2
                (make2 (l', p, rl), rp, make2 (rm, rq, rr)))))
      | ord =>
          (case del (if_equal ord NONE k) r of
            (p', (false, r')) => (p', (false, make2 (l, if_equal ord p' p, r')))
          | (p', (true, r')) => (p', case unmake l of
              Branch2 (ll, lp, lr) =>
                (true, make3 (ll, lp, lr, if_equal ord p' p, r'))
            | Branch3 (ll, lp, lm, lq, lr) => (false, make2
                (make2 (ll, lp, lm), lq, make2 (lr, if_equal ord p' p, r'))))))
  | del k (Branch3 (l, p, m, q, r)) =
      (case compare k q of
        LESS =>
          (case compare k p of
            LESS =>
              (case del k l of
                (p', (false, l')) => (p', (false, make3 (l', p, m, q, r)))
              | (p', (true, l')) => (p', (false, case (unmake m, unmake r) of
                  (Branch2 (ml, mp, mr), Branch2 _) =>
                    make2 (make3 (l', p, ml, mp, mr), q, r)
                | (Branch3 (ml, mp, mm, mq, mr), _) =>
                    make3 (make2 (l', p, ml), mp, make2 (mm, mq, mr), q, r)
                | (Branch2 (ml, mp, mr), Branch3 (rl, rp, rm, rq, rr)) =>
                    make3 (make2 (l', p, ml), mp, make2 (mr, q, rl), rp,
                      make2 (rm, rq, rr)))))
          | ord =>
              (case del (if_equal ord NONE k) m of
                (p', (false, m')) =>
                  (p', (false, make3 (l, if_equal ord p' p, m', q, r)))
              | (p', (true, m')) => (p', (false, case (unmake l, unmake r) of
                  (Branch2 (ll, lp, lr), Branch2 _) =>
                    make2 (make3 (ll, lp, lr, if_equal ord p' p, m'), q, r)
                | (Branch3 (ll, lp, lm, lq, lr), _) =>
                    make3 (make2 (ll, lp, lm), lq,
                      make2 (lr, if_equal ord p' p, m'), q, r)
                | (_, Branch3 (rl, rp, rm, rq, rr)) =>
                    make3 (l, if_equal ord p' p, make2 (m', q, rl), rp,
                      make2 (rm, rq, rr))))))
      | ord =>
          (case del (if_equal ord NONE k) r of
            (q', (false, r')) =>
              (q', (false, make3 (l, p, m, if_equal ord q' q, r')))
          | (q', (true, r')) => (q', (false, case (unmake l, unmake m) of
              (Branch2 _, Branch2 (ml, mp, mr)) =>
                make2 (l, p, make3 (ml, mp, mr, if_equal ord q' q, r'))
            | (_, Branch3 (ml, mp, mm, mq, mr)) =>
                make3 (l, p, make2 (ml, mp, mm), mq,
                  make2 (mr, if_equal ord q' q, r'))
            | (Branch3 (ll, lp, lm, lq, lr), Branch2 (ml, mp, mr)) =>
                make3 (make2 (ll, lp, lm), lq, make2 (lr, p, ml), mp,
                  make2 (mr, if_equal ord q' q, r'))))))
  | del k (Size (_, arg)) = del k arg;
in

fun delete key tab = make_size (size tab - 1) (snd (snd (del (SOME key) tab)));
fun delete_safe key tab = if defined tab key then delete key tab else tab;

end;


(* membership operations *)

fun member eq tab (key, x) =
  (case lookup tab key of
    NONE => false
  | SOME y => eq (x, y));

fun insert eq (key, x) =
  modify key (fn NONE => x | SOME y => if eq x y then raise SAME
                                       else raise DUP key);

fun remove eq (key, x) tab =
  (case lookup tab key of
    NONE => tab
  | SOME y => if eq x y then delete key tab else tab);


(* simultaneous modifications *)

fun make entries = build (Portable.foldl' update_new entries);

fun join f (tab1, tab2) =
  let
    fun add (key, y) tab = modify key (fn NONE => y | SOME x => f key (x, y)) tab;
  in
    if pointer_eq (tab1, tab2) then tab1
    else if is_empty tab1 then tab2
    else fold_table add tab2 tab1
  end;

fun merge eq = join (fn key => fn (x,y) => if eq x y then raise SAME
                                           else raise DUP key);

fun lfoldl f =
    let fun itl (A, []) = A
          | itl (A, e::es) = itl (f(A,e), es)
    in
      itl
    end
fun joins f tabs = lfoldl (join f) (empty, tabs);
fun merges eq tabs = lfoldl (merge eq) (empty, tabs);


(* list tables *)

fun lookup_list tab key = these (lookup tab key);

fun cons_list (key, x) tab = modify key (fn NONE => [x] | SOME xs => x :: xs) tab;

fun modify_list key f =
  modify key (fn arg =>
    let
      val xs = the_default [] arg;
      val ys = f xs;
    in if pointer_eq (xs, ys) then raise SAME else ys end);

fun insert_list eq (key, x) = modify_list key (op_insert eq x);
fun update_list eq (key, x) = modify_list key (op_update eq x);

fun remove_list eq (key, x) tab =
  map_entry key (fn xs =>
    (case op_remove eq x xs of
      [] => raise UNDEF key
    | ys => if pointer_eq (xs, ys) then raise SAME else ys)) tab
  handle UNDEF _ => delete key tab;

fun make_list args = build (Portable.foldr' cons_list args);
fun dest_list tab =
    List.concat (map (fn (key, xs) => map (pair key) xs) (dest tab));
fun merge_list eq =
  join (fn _ => fn (x,y) => if list_eq eq x y then raise SAME
                            else op_union eq x y);


(* set operations *)

type set = unit table;

fun insert_set x = default (x, ());
fun remove_set x : set -> set = delete_safe x;
fun make_set xs = build (Portable.foldl' insert_set xs);

(* pretty-printing *)
fun pp vpp tab =
  let
    open HOLPP
    fun ppi (k,v) =
      block CONSISTENT 0 [Key.pp k, add_string " |->", add_break(1,2), vpp v]
  in
    block CONSISTENT 0 [
      add_string "Table{",
      block INCONSISTENT 6
            (pr_list ppi [add_string ",", add_break(1,0)] (dest tab)),
      add_string "}"
    ]
  end


(*final declarations of this structure!*)
val map = map_table;
val fold = fold_table;
val fold_rev = fold_rev_table;

end;
