structure Cache :> Cache =
struct

open HolKernel liteLib Abbrev boolSyntax boolLib
open Trace

type key = term
type hypinfo = {hyps : term HOLset.set, thms : term HOLset.set}
type data = (hypinfo * thm option) list

(* Each cached key gets a heap-allocated node carrying its data and its
   position in a doubly-linked LRU list.  Promotion on a hit only
   rewrites the prev/next ref cells inside the node and its neighbours;
   the Termtab is left untouched.  Wrapped in a single-constructor
   datatype because SML `type` declarations are non-recursive. *)
datatype node = N of {
  key  : key,
  data : data ref,
  prev : node option ref,  (* NONE iff this node is head (MRU) *)
  next : node option ref   (* NONE iff this node is tail (LRU) *)
}

(* Invariants on a state value (maintained by every mutator below):
   - head = NONE  <=>  tail = NONE  <=>  size = 0
                  <=>  Termtab.size store = 0
   - Following next from head reaches tail in exactly `size` steps;
     symmetric for prev from tail.
   - Termtab.lookup store k = SOME n  implies  #key n = k and n is in
     the list.
   - capacity and per_key_cap live in this same record so callers can
     tune them on the fly via Cache.set_capacity / Cache.set_per_key_cap.
     Mutating either records a fresh state value through the cache's
     state ref, in the same way an insert/eviction does. *)
type state = {
  store       : node Termtab.table,
  head        : node option,   (* MRU *)
  tail        : node option,   (* LRU *)
  size        : int,           (* explicit; avoids Termtab.size in hot path *)
  capacity    : int,
  per_key_cap : int
}

type cache = state Sref.t

fun empty_state caps : state =
    {store = Termtab.empty, head = NONE, tail = NONE, size = 0,
     capacity = #capacity caps, per_key_cap = #per_key_cap caps}

fun new_cache caps : cache = Sref.new (empty_state caps)

(* ----------------------------------------------------------------------
   DLL primitives.  Each operates on the supplied state and returns the
   (possibly rebuilt) state record.  Node ref cells are mutated in
   place; the record is rebuilt only when head/tail/size/store actually
   change.

   Identity of nodes is determined by the prev/next refs in context:
   a node is at head iff its prev ref holds NONE, and at tail iff its
   next ref holds NONE.  We never compare nodes with `=` (term keys are
   not equality types).
   ---------------------------------------------------------------------- *)

(* Helper: rebuild a state record, threading through capacity / per_key_cap
   from the source.  Avoids spelling out the two cap fields in every
   rebuild site. *)
fun with_state {store, head, tail, size} (st : state) : state =
    {store = store, head = head, tail = tail, size = size,
     capacity = #capacity st, per_key_cap = #per_key_cap st}

(* Disconnect node `n` from its current position in the list.  Mutates
   neighbours' next/prev to skip n and adjusts head/tail if n sat at
   either end.  Leaves n.prev / n.next intact — the immediately following
   link_at_head will overwrite them. *)
fun unlink (st : state, N {prev, next, ...} : node) : state =
    let
      val p = !prev
      val q = !next
      val () = case p of
                 NONE => ()
               | SOME (N {next = pnext, ...}) => pnext := q
      val () = case q of
                 NONE => ()
               | SOME (N {prev = qprev, ...}) => qprev := p
      val head' = case p of
                    NONE   => q     (* n was head; successor is new head *)
                  | SOME _ => #head st
      val tail' = case q of
                    NONE   => p     (* n was tail; predecessor is new tail *)
                  | SOME _ => #tail st
    in
      with_state {store = #store st, head = head', tail = tail',
                  size = #size st} st
    end

(* Splice `n` in at the front (MRU).  Caller guarantees `n` is detached
   from the list. *)
fun link_at_head (st : state, n as N {prev, next, ...} : node) : state =
    let
      val old_head = #head st
      val () = prev := NONE
      val () = next := old_head
      val () = case old_head of
                 NONE => ()
               | SOME (N {prev = hprev, ...}) => hprev := SOME n
      val tail' = case #tail st of
                    NONE => SOME n            (* list was empty *)
                  | t    => t
    in
      with_state {store = #store st, head = SOME n, tail = tail',
                  size = #size st} st
    end

(* Drop tail nodes until size <= capacity.  Called from c_insert (where
   size grows by at most one per call, so the loop runs at most once)
   and from set_capacity (where size may be many over the new cap). *)
fun evict_to_fit (st : state) : state =
    if #size st <= #capacity st then st
    else case #tail st of
           NONE => st  (* unreachable: size > 0 *)
         | SOME (N {key = k, prev = tprev, ...}) =>
           let
             val store' = Termtab.delete_safe k (#store st)
             val _ = trace(2,
                           REDUCE("Cache: evicting LRU entry", k))
             val p = !tprev
             val () = case p of
                        NONE => ()
                      | SOME (N {next = pnext, ...}) => pnext := NONE
             val head' = case p of
                           NONE   => NONE         (* list now empty *)
                         | SOME _ => #head st
             val st' = with_state
                         {store = store', head = head', tail = p,
                          size = #size st - 1} st
           in
             evict_to_fit st'
           end

(* Read without bumping: callers that immediately follow with c_insert
   on the same key let the c_insert do the bump.  Lock-free
   (Sref.value): the snapshot is internally consistent and node.data
   is a stable ref the caller may dereference safely. *)
fun peek (c : cache) k : data option =
    case Termtab.lookup (#store (Sref.value c)) k of
      NONE                  => NONE
    | SOME (N {data, ...})  => SOME (!data)

(* Bump k to most-recently-used without changing its data.  Used at
   terminal cache-hit sites where no insert follows.  Short-circuits if
   k is already at head. *)
fun bump (c : cache) k : unit =
    Sref.update c (fn st =>
      case Termtab.lookup (#store st) k of
        NONE                 => st
      | SOME (n as N {prev, ...}) =>
          (case !prev of
             NONE   => st     (* already head — no list mutation *)
           | SOME _ => link_at_head (unlink (st, n), n)))

(* Per-key cap bounds the (hypinfo, thm option) list under a single key.
   Without this bound, "hot" keys — especially boolSyntax.F, which
   prove_false_context writes to on every failed-contradiction attempt
   — accumulate thousands of entries.  Every cache consultation then
   scans the entire list (List.find in consider_false_context_cache and
   in the RCACHE / CACHE main lookups), making per-call cost grow
   linearly with session length.  Capping turns that linear scan into a
   constant.  Dropping oldest entries can cost an occasional re-prove
   when a query's context matched an evicted entry — slower but always
   correct. *)
fun take_at_most n xs =
    let
      fun loop _ acc [] = List.rev acc
        | loop 0 acc _  = List.rev acc
        | loop i acc (x :: rest) = loop (i - 1) (x :: acc) rest
    in
      loop n [] xs
    end

(* Insert/update k -> v, promote it, then evict if over capacity. *)
fun c_insert (c : cache) (k, v) : unit =
    Sref.update c (fn st =>
      let
        val v' = take_at_most (#per_key_cap st) v
      in
        case Termtab.lookup (#store st) k of
          SOME (n as N {data, prev, ...}) =>
            let
              val () = data := v'
            in
              case !prev of
                NONE   => st     (* already head *)
              | SOME _ => link_at_head (unlink (st, n), n)
            end
        | NONE =>
            let
              val n = N {key  = k,         data = ref v',
                         prev = ref NONE,  next = ref NONE}
              val store' = Termtab.update (k, n) (#store st)
              val st1 = link_at_head
                          (with_state {store = store',
                                       head  = #head st,
                                       tail  = #tail st,
                                       size  = #size st + 1} st,
                           n)
            in
              evict_to_fit st1
            end
      end)

(* clear_cache preserves the current capacity / per_key_cap settings so
   that a tuned cache stays tuned across a session-level reset. *)
fun clear_cache (c : cache) : unit =
    Sref.update c (fn st => empty_state {capacity    = #capacity st,
                                         per_key_cap = #per_key_cap st})

fun cache_capacity    (c : cache) : int = #capacity (Sref.value c)
fun cache_per_key_cap (c : cache) : int = #per_key_cap (Sref.value c)

(* Lower the global capacity (if necessary) and immediately evict to the
   new bound.  Raising never evicts.  A reduction prompts an in-place
   purge of the LRU tail until size <= n; chosen over lazy eviction so
   that the user-observable state (cache_values, cache_capacity) reflects
   the new cap immediately. *)
fun set_capacity (c : cache) n =
    Sref.update c (fn st =>
      evict_to_fit
        {store = #store st, head = #head st, tail = #tail st,
         size = #size st, capacity = n, per_key_cap = #per_key_cap st})

(* Set the per-key cap and immediately truncate every per-key data list
   to the new bound (in-place on the node's data ref — no list structural
   change).  Same rationale as set_capacity: the user-observable cache
   reflects the new cap immediately. *)
fun set_per_key_cap (c : cache) n =
    Sref.update c (fn st =>
      let
        val () = Termtab.fold
                   (fn (_, N {data, ...}) => fn () =>
                       data := take_at_most n (!data))
                   (#store st)
                   ()
      in
        {store = #store st, head = #head st, tail = #tail st,
         size = #size st, capacity = #capacity st, per_key_cap = n}
      end)

val empty_hypinfo = {hyps = empty_tmset, thms = empty_tmset}
fun hypinfo_addth (th, {hyps,thms}) =
    {hyps = HOLset.union(hyps, hypset th), thms = HOLset.add(thms, concl th)}
val all_hyps = List.foldl hypinfo_addth empty_hypinfo

infix <<;  (* A subsetof B *)
fun {hyps=h1,thms=ths1} << {hyps=h2,thms=ths2} =
    HOLset.isSubset(h1,h2) andalso HOLset.isSubset(ths1, ths2)
val _ = op<< : hypinfo * hypinfo -> bool
fun hypinfo_list {hyps,thms} = HOLset.foldl op:: (HOLset.listItems hyps) thms
fun hypinfo_isEmpty ({hyps,thms}:hypinfo) =
    HOLset.isEmpty hyps andalso HOLset.isEmpty thms

exception NOT_FOUND
exception FIRST
fun first p [] = raise FIRST
  | first p (h::t) = if p h then h else first p t

fun CACHE (spec : {capacity:int, per_key_cap:int}) (filt,conv) = let
  val cache = new_cache spec
  fun cache_proc thms tm = let
    val _ = if (filt tm) then ()
            else failwith "CACHE_CCONV: not applicable"
    val prevs = Option.getOpt (peek cache tm, [])
    val curr = all_hyps thms
    fun ok (prev,SOME thm) = prev << curr
      | ok (prev,NONE) = curr << prev
  in
    let val (_, res) = first ok prevs
        val () = bump cache tm
    in
      case res of
        SOME x => (trace(1,PRODUCE(tm,"cache hit!",x)); x)
      | NONE => failwith "cache hit was failure"
    end
    handle FIRST => let
             val thm = conv thms tm
                 handle e as (HOL_ERR _) =>
                        (trace(2,
                               REDUCE("Inserting failed ctxt",
                                      if hypinfo_isEmpty curr then tm
                                      else
                                        mk_imp(list_mk_conj (hypinfo_list curr),
                                               tm))) ;
                         c_insert cache (tm, (curr,NONE)::prevs);
                         raise e)
           in
             (trace(2,PRODUCE(tm, "Inserting into cache:", thm));
              c_insert cache (tm,(curr,SOME thm)::prevs);
              thm)
           end
  end
in
  (cache_proc, cache)
end

fun cache_values (cache : cache) = let
  val items = Termtab.dest (#store (Sref.value cache))
  fun tolist (set, thmopt) = (hypinfo_list set, thmopt)
  fun ToList (k, N {data, ...}) = (k, map tolist (!data))
in
  map ToList items
end


(* ----------------------------------------------------------------------
    RCACHE

    Cached decision procedures have always recorded both the successes
    and the failures of the underlying d.p.  With failures recorded,
    the system will not repeatedly try (and fail) to solve the same
    goal.  However, the underlying decision procedures are
    context-aware, and the context as well the goal attempted is
    stored in the cache.

    If a success is stored with context C, and the context of the
    latest attempt is a superset of C, then the cache's stored
    information can be accepted.  Conversely, if there is a failure
    stored in the cache, and a new attempt is made to prove the same
    goal, with a smaller context, then the cache's verdict can be
    accepted immediately.  On the other hand, if this means that the
    latest attempt has a larger context, and what's stored is a
    failure, then a fresh call to the underlying decision procedure is
    called for.

    However, if the context in the latest attempt is only larger
    because of the addition of irrelevant new assumptions (those that
    do not mention any variables from the underlying goal), then they
    shouldn't make any difference, and trying the goal again with this
    bigger context will just result in a slower failure.  That is,
    unless the new assumptions introduce a contradiction with other
    irrelevants bits of the assumptions.

    The RCACHE code does a connected components analysis to split
    problems up, and the sub-problems are tried (and cached!)
    independently.

   ---------------------------------------------------------------------- *)

fun ccs G vs = let
  (* G is a Termtab from terms to term sets, with the set representing
     the adjacent nodes in the graph.  The graph is undirected so
     there will be two entries for each link.
     vs is a list of all the terms in G. *)
  fun recurse acc visited v = let
    (* v is already in acc and visited *)
    val neighbours = Option.getOpt (Termtab.lookup G v, empty_tmset)
    fun visit_neighbour(n, (acc, visited)) =
        if HOLset.member(visited, n) then (acc, visited)
        else recurse (n::acc) (HOLset.add(visited, n)) n
  in
    HOLset.foldl visit_neighbour (acc, visited) neighbours
  end
  fun find_component visited v = (* v is not in visited *)
    recurse [v] (HOLset.add(visited, v)) v
  fun find_component_acc(v, (acc,visited)) =
      if HOLset.member (visited, v) then (acc,visited)
      else let
          val (vcomp, visited') = find_component visited v
        in
          (vcomp::acc, visited')
        end
in
  List.foldl find_component_acc ([], empty_tmset) vs
end

fun make_links fvs_of (t, G) = let
  val fvs = fvs_of t
  fun mk_link1 t1 t2 G = let
    val newset =
        case Termtab.lookup G t1 of
          NONE => HOLset.singleton Term.compare t2
        | SOME s => HOLset.add(s, t2)
  in
    Termtab.update (t1, newset) G
  end
  fun mk_link t1 t2 G = mk_link1 t1 t2 (mk_link1 t2 t1 G)
  fun mk_links [] G = G
    | mk_links [_] G = G
    | mk_links (x::y::rest) G = mk_link x y (mk_links (y::rest) G)
  fun enter_domain x G =
      case Termtab.lookup G x of
        NONE => Termtab.update (x, HOLset.empty Term.compare) G
      | SOME _ => G
in
  case fvs of
    [x] => enter_domain x G
  | _ => mk_links fvs G
end

(* Creates a graph. Each node is a term where two terms are linked (by
   the transitive closure of the adjacency relation) if each appears
   in a term from tmlist.  The function parameter fvs_of calculates
   which sub-terms should be inserted into the graph.

   The "idea" is that only free variables are linked, but the
   specified fvs_of function may additionally cause other sorts of
   sub-terms to be treated as variables.

   The implementation (see make_links) just creates a linear sub-graph
   for each element of tmlist.  In other words, if a term gives rise
   to n subterms, the K_n subgraph is not inserted, only a connected
   linear graph of those n subterms.  The later connected components
   analysis will realise that all of these sub-terms are part of the
   same component anyway.
*)
fun build_graph fvs_of tmlist =
    List.foldl (make_links fvs_of) Termtab.empty tmlist

(* given a list of list of variables; build a map where all the variables
   in the same list point to the same updatable reference cell *)
val build_var_to_group_map = let
  fun foldthis (tlist, acc) = let
    val r = Uref.new (empty_hypinfo, [] : thm list)
  in
    List.foldl (fn (t, acc) => Termtab.update (t, r) acc) acc tlist
  end
in
  List.foldl foldthis Termtab.empty
end


fun thmlistrefcmp(r1, r2) =
    if r1 = r2 then EQUAL
    else Term.compare (concl (hd (!r1)), concl (hd (!r2)))

type context = hypinfo * thm list
               (* terms are the union of all the theorems hypotheses *)
datatype result = proved_it of thm
                | possible_ctxts of context list
fun mk_goal t = let
  val ty = type_of t
in
  mk_eq(t, if ty = bool then T else mk_arb ty)
end

(* Note: takes the cache ref (not a snapshot) so that a contradiction hit
   can bump the F key. *)
fun consider_false_context_cache (cache:cache) original_goal
                                 (ctxtlist:context list) =
    let
      val cache_F = Option.getOpt (peek cache boolSyntax.F, [])
      fun recurse acc ctxts =
          case ctxts of
            [] => possible_ctxts acc
          | (c as (hyps, thlist))::cs => let
              fun ok (cached, SOME _) = cached << hyps
                | ok (cached, NONE) = hyps << cached
            in
              case List.find ok cache_F of
                NONE => recurse (c::acc) cs
              | SOME (_, NONE) => recurse acc cs
              | SOME (_, SOME th) =>
                (trace(1,PRODUCE(original_goal,
                                 "cache hit for contradiction", th));
                 bump cache boolSyntax.F;
                 proved_it (CCONTR (mk_goal original_goal) (EQT_ELIM th)))
            end
    in
      recurse [] ctxtlist
    end

fun prove_false_context (conv:thm list -> conv) (cache:cache) (ctxtlist:context list) original_goal = let
  fun recurse clist =
      case clist of
        [] => raise mk_HOL_ERR "Cache" "RCACHE"
                               "No (more) possibly false contexts"
      | (hyps,thms)::cs => let
          val oldval = Option.getOpt (peek cache F, [])
          val conjs = list_mk_conj (map concl thms)
        in
          case Lib.total (conv thms) boolSyntax.F of
            SOME th => let
              val newth = CCONTR (mk_goal original_goal) (EQT_ELIM th)
            in
              trace(2,PRODUCE(conjs, "Inserting into cache:", th));
              c_insert cache (F, (hyps, SOME th) :: oldval);
              newth
            end
          | NONE => (
              trace(2, REDUCE("Inserting failed contradictory context", conjs));
              c_insert cache (F, (hyps, NONE)::oldval);
              recurse cs
            )
        end
in
  recurse ctxtlist
end

fun RCACHE (spec : {capacity:int, per_key_cap:int}) (dpfvs, check, conv) = let
  open Uref
  val cache = new_cache spec
  fun build_up_ctxt mp th = let
    val c = concl th
  in
    case dpfvs c of
      [] => ()
    | (v::_) => let
        val r = valOf (Termtab.lookup mp v)
        val (oldhyps, oldthms) = !r
      in
        r := (hypinfo_addth(th, oldhyps), th::oldthms)
      end
  end
  fun decider ctxt t = let
    val _ = if check t then ()
            else raise mk_HOL_ERR "Cache" "RCACHE" "not applicable"
    val prevs = Option.getOpt (peek cache t, [])
    val curr = all_hyps ctxt
    fun oksome (prev, SOME thm) = prev << curr
      | oksome (_, NONE) = false
  in
    case List.find oksome prevs of
      SOME (_, SOME x) =>
        (trace(1,PRODUCE(t, "cache hit!", x)); bump cache t; x)
    | SOME (_, NONE) => raise Fail "RCACHE: Invariant failure"
    | NONE => let
        (* do connected component analysis to test for false *)
        fun foldthis (th, (ctxt_ts, ground_ths)) = let
          val c = concl th
        in
          if null (dpfvs c) then (ctxt_ts, th::ground_ths)
          else (c::ctxt_ts, ground_ths)
        end
        val (ctxt_ts,ground_ctxt_ths) =
            List.foldl foldthis ([], []) ctxt
        val G = build_graph dpfvs (t::ctxt_ts)
                (* G a map from v to v's neighbours *)
        val vs = Termtab.fold (fn (k,_) => fn acc => k::acc) G []
        val (comps, _) = ccs G vs
                (* a list of lists of variables *)
        val group_map = build_var_to_group_map comps
        val _ = app (build_up_ctxt group_map) ctxt
                  (* group map is a map from variables to all the
                     ctxts (theorems) that are in that variable's component *)

        (* now extract the ctxt relevant for the goal statement *)
        val (group_map', glstmtref) =
          case dpfvs t of
            [] => (group_map, Uref.new (empty_hypinfo, []))
          | (glvar::_) =>
              let val r = valOf (Termtab.lookup group_map glvar)
              in (Termtab.delete glvar group_map, r) end

        (* and the remaining contexts, ensuring there are no
           duplicate copies *)
        fun foldthis (k, v) (acc as (setlist, seenreflist)) =
            if mem v seenreflist then acc
            else (!v::setlist, v::seenreflist)
        val (divided_clist0, _) =
            Termtab.fold foldthis group_map' ([], [glstmtref])

        (* fold in every ground hypothesis as a separate context, entire
           unto itself *)
        val divided_clist =
            divided_clist0 @
            map (fn th => (hypinfo_addth(th, empty_hypinfo), [th]))
                ground_ctxt_ths

        val (glhyps, thmlist) = !glstmtref
        fun oknone (prev, NONE) = glhyps << prev
          | oknone _ = false
      in
        case List.find oknone prevs of
          NONE => let
            (* nothing cached, but should still try cache for proving
               false from the context *)
          in
            case consider_false_context_cache cache t divided_clist
            of
              proved_it th => th
            | possible_ctxts cs => let
                (* cs is the list of things worth trying to prove, but
                   in this situation should first try conv on the original
                   goal because there's nothing in the cache about it *)
              in
                case Lib.total (conv thmlist) t of
                  SOME th => let
                  in
                    trace(2,PRODUCE(t,"Inserting into cache:", th));
                    c_insert cache (t, (glhyps,SOME th)::prevs);
                    th
                  end
                | NONE => let
                  in
                    trace(2, REDUCE("Inserting failure to prove",
                                    if hypinfo_isEmpty glhyps then t
                                    else mk_imp(list_mk_conj
                                                  (map concl thmlist), t)));
                    c_insert cache (t, (glhyps, NONE)::prevs);
                    prove_false_context conv cache cs t
                  end
              end
          end
        | SOME (_, NONE) => let
            (* with the relevant context, our goal doesn't resolve one
               way or the other.  However, it's possible that part of the
               rest of the context goes to false *)
          in
            case consider_false_context_cache cache t divided_clist of
              proved_it th => th
            | possible_ctxts cs => prove_false_context conv cache cs t
          end
        | SOME _ => raise Fail "RCACHE: invariant failure the second"
      end
  end
in
  (decider,cache)
end

end (* struct *)
