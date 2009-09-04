(*
 *  gr.sml - definitions that are shared among different graph implementations
 *
 *  COPYRIGHT (c) 1997 by Martin Erwig.  See COPYRIGHT file for details.
 *)

(*
   structures and functors defined:

    GraphNode          defines type of graph nodes
    GraphExceptions    defines graph exceptions
    GraphTypes         functor for deriving types from graph implementation
    UnlabGraphTypes    functor for deriving types from graph implementation
    StampUtil          time stamping utilities
    SortEdges          utilities to sort successors/predecessors) by edge labels
 *)

structure GraphNode : GRAPH_NODE =
struct
  type node = int
end


structure GraphExceptions : GRAPH_EXCEPTIONS =
struct
  exception Node
  exception Edge
  exception NotImplemented
end



(* functors deriving types from graph implementations *)

functor UnlabGraphTypes (type 'a graph) : UNLAB_GRAPH_TYPES =
struct
  type node          = GraphNode.node
  type 'a graph      = 'a graph
  type 'a adj        = 'a * node list
  type 'a context    = node list * node * 'a * node list
  type 'a decomp     = 'a context * 'a graph
  type 'a fwd_decomp = 'a adj * 'a graph
end


functor GraphTypes (type ('a,'b) graph) : GRAPH_TYPES =
struct
  type node               = GraphNode.node
  type ('a,'b) graph      = ('a,'b) graph
  type     'b out         = ('b * node) list
  type ('a,'b) adj        = 'a * 'b out
  type ('a,'b) context    = 'b out * node * 'a * 'b out
  type ('a,'b) decomp     = ('a,'b) context * ('a,'b) graph
  type ('a,'b) fwd_decomp = ('a,'b) adj * ('a,'b) graph
end
