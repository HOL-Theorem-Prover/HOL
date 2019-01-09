structure Cache :> Cache =
struct

open HolKernel liteLib Trace Abbrev boolSyntax boolLib


type key = term
type hypinfo = {hyps : term HOLset.set, thms : term HOLset.set}
type data = (hypinfo * thm option) list

type table = (key, data) Redblackmap.dict
val empty_table = Redblackmap.mkDict Term.compare : table

type cache = table Sref.t
fun c_insert c (k,v) = Sref.update c (fn t => Redblackmap.insert(t,k,v))
fun cvalue (c:cache) = Sref.value c
fun new_cache() : cache = Sref.new empty_table

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

fun CACHE (filt,conv) = let
  val cache = new_cache()
  fun cache_proc thms tm = let
    val _ = if (filt tm) then ()
            else failwith "CACHE_CCONV: not applicable"
    val prevs = Redblackmap.find (cvalue cache, tm)
                handle Redblackmap.NotFound => []
    val curr = all_hyps thms
    fun ok (prev,SOME thm) = prev << curr
      | ok (prev,NONE) = curr << prev
  in
    (case snd (first ok prevs) of
       SOME x => (trace(1,PRODUCE(tm,"cache hit!",x)); x)
     | NONE => failwith "cache hit was failure")
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

fun clear_cache cache = (Sref.update cache (fn c => empty_table))

fun cache_values (cache : cache) = let
  val items = Redblackmap.listItems (cvalue cache)
  fun tolist (set, thmopt) = (hypinfo_list set, thmopt)
  fun ToList (k, stlist) = (k, map tolist stlist)
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
  (* G is a Binarymap from terms to term sets, with the set representing
     the adjacent nodes in the graph.  The graph is undirected so
     there will be two entries for each link.
     vs is a list of all the terms in G. *)
  fun recurse acc visited v = let
    (* v is already in acc and visited *)
    val neighbours = Binarymap.find (G, v)
        handle Binarymap.NotFound => empty_tmset
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
        case Binarymap.peek(G, t1) of
          NONE => HOLset.singleton Term.compare t2
        | SOME s => HOLset.add(s, t2)
  in
    Binarymap.insert(G, t1, newset)
  end
  fun mk_link t1 t2 G = mk_link1 t1 t2 (mk_link1 t2 t1 G)
  fun mk_links [] G = G
    | mk_links [_] G = G
    | mk_links (x::y::rest) G = mk_link x y (mk_links (y::rest) G)
  fun enter_domain x G =
      case Binarymap.peek (G, x) of
        NONE => Binarymap.insert(G, x, HOLset.empty Term.compare)
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
    List.foldl (make_links fvs_of) (Binarymap.mkDict Term.compare) tmlist

(* given a list of list of variables; build a map where all the variables
   in the same list point to the same updatable reference cell *)
val build_var_to_group_map = let
  fun foldthis (tlist, acc) = let
    val r = Unsynchronized.ref (empty_hypinfo, [] : thm list)
  in
    List.foldl (fn (t, acc) => Binarymap.insert(acc, t, r)) acc tlist
  end
in
  List.foldl foldthis (Binarymap.mkDict Term.compare)
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

fun consider_false_context_cache table original_goal (ctxtlist:context list) =
    let
      val cache_F = Redblackmap.find (table, boolSyntax.F)
                    handle Redblackmap.NotFound => []
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
          val oldval = Redblackmap.find (cvalue cache, F)
                       handle Redblackmap.NotFound => []
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

fun RCACHE (dpfvs, check, conv) = let
  open Unsynchronized
  val cache = new_cache()
  fun build_up_ctxt mp th = let
    val c = concl th
  in
    case dpfvs c of
      [] => ()
    | (v::_) => let
        val r = Binarymap.find(mp,v)
        val (oldhyps, oldthms) = !r
      in
        r := (hypinfo_addth(th, oldhyps), th::oldthms)
      end
  end
  fun decider ctxt t = let
    val _ = if check t then ()
            else raise mk_HOL_ERR "Cache" "RCACHE" "not applicable"
    val prevs = Redblackmap.find (cvalue cache, t) handle NotFound => []
    val curr = all_hyps ctxt
    fun oksome (prev, SOME thm) = prev << curr
      | oksome (_, NONE) = false
  in
    case List.find oksome prevs of
      SOME (_, SOME x) => (trace(1,PRODUCE(t, "cache hit!", x)); x)
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
        val vs = Binarymap.foldl (fn (k,v,acc) => k::acc) [] G
        val (comps, _) = ccs G vs
                (* a list of lists of variables *)
        val group_map = build_var_to_group_map comps
        val _ = app (build_up_ctxt group_map) ctxt
                  (* group map is a map from variables to all the
                     ctxts (theorems) that are in that variable's component *)

        (* now extract the ctxt relevant for the goal statement *)
        val (group_map', glstmtref) =
          case dpfvs t of
            [] => (group_map, ref (empty_hypinfo, []))
          | (glvar::_) => Binarymap.remove(group_map, glvar)

        (* and the remaining contexts, ensuring there are no
           duplicate copies *)
        fun foldthis (k, v, acc as (setlist, seenreflist)) =
            if mem v seenreflist then acc
            else (!v::setlist, v::seenreflist)
        val (divided_clist0, _) =
            Binarymap.foldl foldthis ([], [glstmtref]) group_map'

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
            case consider_false_context_cache (cvalue cache) t divided_clist
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
            case consider_false_context_cache (cvalue cache) t divided_clist of
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
