signature ImplicitGraph =
sig

  type 'a graph = 'a -> 'a list

  val dfs : 'a graph -> ('a * 'a -> order) ->
            (int -> 'a -> 'result -> 'result) ->
            'a -> 'result -> 'result
  val bfs : 'a graph -> ('a * 'a -> order) ->
            (int -> 'a -> 'result -> 'result) ->
            'a -> 'result -> 'result
  val limdfs : 'a graph -> ('a * 'a -> order) ->
               (int -> 'a -> 'result -> 'result) ->
               int -> 'a -> 'result -> 'result
  val limbfs : 'a graph -> ('a * 'a -> order) ->
               (int -> 'a -> 'result -> 'result) ->
               int -> 'a -> 'result -> 'result

(* fold functions get passed distance from root as extra integer parameter.
   the "lim" versions of the functions will drop visited nodes that have depths
   greater than the provided limit.  In all cases, the initial node is
   folded into the 'result at depth 0.
*)

end
