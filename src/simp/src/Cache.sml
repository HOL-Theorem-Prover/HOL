structure Cache :> Cache =
struct

open HolKernel liteLib Abbrev boolSyntax boolLib
open Trace

type key = term
type hypinfo = {hyps : term HOLset.set, thms : term HOLset.set}
type data = (hypinfo * thm option) list

type entry = {seq : int, data : data}

(* The mutable part of a cache.
   Invariant: store(k) = {seq = i, ...}  iff  by_seq(i) = k.  i.e. by_seq
   is the inverse of the seq# projection of store.  Maintained by every
   mutator below. *)
type state = {
  store    : entry Termtab.table,
  by_seq   : term Inttab.table,
  next_seq : int
}

(* Sizing parameters are fixed at construction time and live on the cache
   wrapper, not in the mutable state — so mutators never thread them
   through their record reconstructions. *)
type cache = {
  state       : state Sref.t,
  capacity    : int,
  per_key_cap : int
}

val empty_state : state =
    {store = Termtab.empty, by_seq = Inttab.empty, next_seq = 0}

fun new_cache {capacity, per_key_cap} : cache =
    {state = Sref.new empty_state,
     capacity = capacity, per_key_cap = per_key_cap}

(* When next_seq would overflow, renumber existing entries to 0..n-1.
   Effectively unreachable on Poly/ML (63-bit Int); on Moscow ML's 31-bit
   Int this fires at most once per ~10^9 cache operations.  If Int is
   unbounded (Int.maxInt = NONE), renumbering is never needed. *)
fun needs_renumber n =
    case Int.maxInt of
      NONE => false
    | SOME m => n >= m - 16

fun renumber ({store, by_seq, ...} : state) : state =
    let
      val items = Inttab.dest by_seq  (* in seq# order *)
      val (store', by_seq', n) =
          List.foldl
            (fn ((_, k), (st, bs, i)) =>
                case Termtab.lookup st k of
                  NONE => (st, bs, i)
                | SOME {data, ...} =>
                  (Termtab.update (k, {seq = i, data = data}) st,
                   Inttab.update (i, k) bs,
                   i + 1))
            (store, Inttab.empty, 0)
            items
    in
      {store = store', by_seq = by_seq', next_seq = n}
    end

(* Move k to the front of the LRU order, storing data v under it. *)
fun touch_with_data (st : state, k, v) : state =
    let
      val st = if needs_renumber (#next_seq st) then renumber st else st
      val {store, by_seq, next_seq} = st
      val by_seq1 =
          case Termtab.lookup store k of
            NONE => by_seq
          | SOME {seq = old_seq, ...} => Inttab.delete_safe old_seq by_seq
      val store' = Termtab.update (k, {seq = next_seq, data = v}) store
      val by_seq' = Inttab.update (next_seq, k) by_seq1
    in
      {store = store', by_seq = by_seq', next_seq = next_seq + 1}
    end

(* Drop the LRU key until size <= capacity. *)
fun evict_to_fit capacity (st : state) : state =
    if Termtab.size (#store st) <= capacity then st
    else
      case Inttab.min (#by_seq st) of
        NONE => st
      | SOME (min_seq, evict_key) =>
          let
            val store' = Termtab.delete_safe evict_key (#store st)
            val by_seq' = Inttab.delete_safe min_seq (#by_seq st)
            val _ = trace(2,
                          REDUCE("Cache: evicting LRU entry", evict_key))
          in
            evict_to_fit capacity
              {store = store', by_seq = by_seq', next_seq = #next_seq st}
          end

(* Read without bumping: callers that immediately follow with c_insert
   on the same key let the c_insert do the bump. *)
fun peek (c : cache) k : data option =
    Option.map #data (Termtab.lookup (#store (Sref.value (#state c))) k)

(* Bump k to most-recently-used without changing its data.  Used at
   terminal cache-hit sites where no insert follows. *)
fun bump (c : cache) k : unit =
    Sref.update (#state c)
      (fn st =>
          case Termtab.lookup (#store st) k of
            NONE => st
          | SOME {data, ...} => touch_with_data (st, k, data))

(* Per-key cap (per the lru record) bounds the (hypinfo, thm option) list
   under a single key.  Without this bound, "hot" keys — especially
   boolSyntax.F, which prove_false_context writes to on every failed-
   contradiction attempt — accumulate thousands of entries.  Every cache
   consultation then scans the entire list (List.find in
   consider_false_context_cache and in the RCACHE / CACHE main lookups),
   making per-call cost grow linearly with session length.  Capping turns
   that linear scan into a constant.  Dropping oldest entries can cost an
   occasional re-prove when a query's context matched an evicted entry
   — slower but always correct. *)
fun take_at_most n xs =
    let
      fun loop _ acc [] = List.rev acc
        | loop 0 acc _  = List.rev acc
        | loop i acc (x :: rest) = loop (i - 1) (x :: acc) rest
    in
      loop n [] xs
    end

(* Insert/update k -> v, bump it, then evict if over capacity. *)
fun c_insert (c : cache) (k, v) : unit =
    Sref.update (#state c)
      (fn st => evict_to_fit (#capacity c)
                  (touch_with_data (st, k, take_at_most (#per_key_cap c) v)))

fun clear_cache (c : cache) : unit =
    Sref.update (#state c) (fn _ => empty_state)

fun cache_capacity (c : cache) : int = #capacity c

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
  val items = Termtab.dest (#store (Sref.value (#state cache)))
  fun tolist (set, thmopt) = (hypinfo_list set, thmopt)
  fun ToList (k, {data, ...} : entry) = (k, map tolist data)
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
